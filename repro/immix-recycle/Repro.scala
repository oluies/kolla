//> using scala 3.9.0
//> using platform scala-native
//> using nativeVersion 0.5.12
//> using nativeGc immix

// One thread allocates; `--idle N` other threads exist and do nothing.
//
// Hypothesis: after each collection immix hands partly free blocks and freed
// large-object chunks to every mutator thread in turn (`Heap_Recycle`,
// `NextMutatorThread`), and a thread can only allocate from what it was given.
// With N idle threads the allocating one sees about 1/(N+1) of the reclaimed
// space, so the heap grows far past the live set, and a capped heap fails with
// `Out of heap space grow heap` from the large-object path.
//
// The workload is the shape of a streaming checker: a slowly growing
// long-lived structure, a lot of short-lived small garbage interleaved with it,
// and short-lived 64 KiB and 128 KiB buffers like a reader's input chunks.
//
//   scala-cli package --native Repro.scala -o repro -f
//   ./repro --idle 0
//   ./repro --idle 16
//   GC_MAXIMUM_HEAP_SIZE=1G ./repro --idle 16

import java.util.concurrent.CountDownLatch
import scala.scalanative.runtime.GC

final class Node(val left: Node, val right: Node, val key: Long)

object Repro:

  final case class Config(
      idle: Int = 0,
      steps: Int = 2_000_000,
      garbage: Int = 40,    // short-lived nodes per step
      large: Boolean = true,
      pool: Boolean = false, // reuse the large buffers instead of reallocating
      ring: Int = 4,        // how many large buffers are alive at once
      logEvery: Int = 100_000
  )

  def parse(args: List[String], c: Config = Config()): Config = args match
    case "--idle" :: n :: rest      => parse(rest, c.copy(idle = n.toInt))
    case "--steps" :: n :: rest     => parse(rest, c.copy(steps = n.toInt))
    case "--garbage" :: n :: rest   => parse(rest, c.copy(garbage = n.toInt))
    case "--no-large" :: rest       => parse(rest, c.copy(large = false))
    case "--pool" :: rest           => parse(rest, c.copy(pool = true))
    case "--log-every" :: n :: rest => parse(rest, c.copy(logEvery = n.toInt))
    case Nil                        => c
    case other :: _                 => sys.error(s"unknown argument $other")

  private val mb = 1024.0 * 1024.0

  private def heapMb: Double = GC.getUsedHeapSize().toLong / mb

  def main(args: Array[String]): Unit =
    val c = parse(args.toList)

    // Idle mutators: started, then blocked for the whole run.
    val release = new CountDownLatch(1)
    val idlers = (1 to c.idle).map { i =>
      val t = new Thread(() => release.await(), s"idle-$i")
      t.setDaemon(true)
      t.start()
      t
    }

    val nodeBytes = 32L // header, two references, a long
    val bytesBuf  = Array.ofDim[Array[Byte]](c.ring)
    val charsBuf  = Array.ofDim[Array[Char]](c.ring)
    if c.pool then
      for i <- 0 until c.ring do
        bytesBuf(i) = new Array[Byte](64 * 1024)
        charsBuf(i) = new Array[Char](64 * 1024)

    System.err.println(
      s"config idle=${c.idle} steps=${c.steps} garbage=${c.garbage} large=${c.large} " +
        s"pool=${c.pool} maxHeap=${(GC.getMaxHeapSize().toLong / mb).round}MB"
    )
    System.err.println("step,retained,live_mb,heap_mb,collections,seconds")
    val start = System.nanoTime()
    def log(step: Int, retained: Long): Unit =
      val live = retained * nodeBytes / mb + (if c.large then c.ring * 192.0 / 1024 else 0.0)
      val secs = (System.nanoTime() - start) / 1e9
      System.err.println(
        f"$step,$retained,$live%.1f,$heapMb%.1f,${GC.getStatsCollectionTotal().toLong},$secs%.1f"
      )

    var kept: Node = null // the long-lived structure
    var retained = 0L
    var sink = 0L          // keeps the garbage from being optimised away
    var step = 0
    while step < c.steps do
      // Short-lived small garbage, interleaved with one long-lived node, so
      // that blocks end up partly live and are recycled line by line.
      var tmp: Node = null
      var g = 0
      while g < c.garbage do
        tmp = new Node(tmp, null, g)
        g += 1
      if tmp != null then sink += tmp.key
      kept = new Node(kept, null, step)
      retained += 1

      if c.large then
        val slot = step % c.ring
        if c.pool then
          bytesBuf(slot)(step & 0xffff) = step.toByte
          charsBuf(slot)(step & 0xffff) = step.toChar
        else
          bytesBuf(slot) = new Array[Byte](64 * 1024)  // 64 KiB, like an input chunk
          charsBuf(slot) = new Array[Char](64 * 1024)  // 128 KiB, like its decoded text
        sink += bytesBuf(slot)(0) + charsBuf(slot)(0)

      step += 1
      if step % c.logEvery == 0 then log(step, retained)

    log(step, retained)
    release.countDown()
    idlers.foreach(_.join())
    System.err.println(f"done heap_mb=$heapMb%.1f sink=$sink kept=${kept.key}")
