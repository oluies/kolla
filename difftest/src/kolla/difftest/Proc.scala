package kolla.difftest

import cats.effect.IO
import java.nio.file.Path
import scala.concurrent.duration.FiniteDuration
import scala.jdk.CollectionConverters.*

final case class ProcResult(exitCode: Int, stdout: String, stderr: String, nanos: Long, timedOut: Boolean = false):
  def ok: Boolean = exitCode == 0 && !timedOut
  def orFail(what: String): IO[ProcResult] =
    if timedOut then IO.raiseError(new RuntimeException(s"$what timed out"))
    else if ok then IO.pure(this)
    else
      IO.raiseError(
        new RuntimeException(
          s"$what failed with exit code $exitCode\nstdout:\n${stdout.takeRight(4000)}\nstderr:\n${stderr.takeRight(4000)}"
        )
      )

/** Subprocess execution. `difftest` is JVM-only, so `ProcessBuilder` is fine
  * here; the cross-compiled modules must not use it.
  */
object Proc:

  def run(
      cmd: Seq[String],
      cwd: Option[Path] = None,
      env: Map[String, String] = Map.empty,
      stdoutTo: Option[Path] = None,
      timeout: Option[FiniteDuration] = None
  ): IO[ProcResult] =
    IO.interruptible {
      val pb = new ProcessBuilder(cmd.asJava)
      cwd.foreach(d => pb.directory(d.toFile))
      env.foreach((k, v) => pb.environment().put(k, v))
      stdoutTo match
        case Some(p) =>
          java.nio.file.Files.createDirectories(p.getParent)
          pb.redirectOutput(p.toFile)
        case None => ()
      val t0   = System.nanoTime()
      val proc = pb.start()
      proc.getOutputStream.close()
      // Drain both streams so the child cannot block on a full pipe.
      val outF =
        if stdoutTo.isDefined then null
        else drain(proc.getInputStream)
      val errF = drain(proc.getErrorStream)
      val finished = timeout match
        case Some(d) => proc.waitFor(d.toMillis, java.util.concurrent.TimeUnit.MILLISECONDS)
        case None    => proc.waitFor(); true
      if !finished then
        proc.destroyForcibly()
        proc.waitFor()
      val out = if outF == null then "" else outF.get()
      ProcResult(proc.exitValue(), out, errF.get(), System.nanoTime() - t0, timedOut = !finished)
    }

  private def drain(in: java.io.InputStream): java.util.concurrent.FutureTask[String] =
    val task = new java.util.concurrent.FutureTask[String](() =>
      val sb  = new StringBuilder
      val buf = new Array[Byte](8192)
      var n   = in.read(buf)
      while n >= 0 do
        sb ++= new String(buf, 0, n, "UTF-8")
        n = in.read(buf)
      sb.result()
    )
    val th = new Thread(task, "proc-drain")
    th.setDaemon(true)
    th.start()
    task

  def which(cmd: String): IO[Option[Path]] =
    run(Seq("sh", "-c", s"command -v ${shellQuote(cmd)}")).map { r =>
      if r.ok && r.stdout.trim.nonEmpty then Some(java.nio.file.Paths.get(r.stdout.trim)) else None
    }

  def shellQuote(s: String): String = "'" + s.replace("'", "'\\''") + "'"
