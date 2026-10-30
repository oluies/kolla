# immix: interleaved retention, idle threads and large objects

A self-contained Scala Native program, no dependencies, that reproduces why
kolla's native binary with the default `immix` collector needs about 100 times
the heap of the JVM build (docs/semantics.md F7). One thread allocates; the
others, if any, are idle.

```
scala-cli --power package --native Repro.scala -o repro -f
GC_MAXIMUM_HEAP_SIZE=512M ./repro --idle 0 --no-large    # passes
GC_MAXIMUM_HEAP_SIZE=512M ./repro --idle 16 --no-large   # Out of heap space
```

Each step allocates `--garbage` short-lived 32-byte nodes (default 40) and one
node that is kept for the rest of the run. Unless `--no-large` is given it also
allocates a fresh 64 KiB `Array[Byte]` and a 128 KiB `Array[Char]`, four of
each alive at a time; `--pool` reuses four instead. It logs to stderr as CSV:
step, retained nodes, estimated live MB, `GC.getUsedHeapSize()` in MB (the
committed heap), collections so far and seconds.

## Results

Scala Native 0.5.12, immix, multithreading on, debug mode, macOS 26 on an
18-core arm64 machine. 1,000,000 steps, so about 30.5 MB is live at the end.
Caps tried: 48M, 64M, 128M, 256M, 512M, 768M, 1G, 2G.

| configuration | smallest passing `GC_MAXIMUM_HEAP_SIZE` | collections | time |
|---|---|---|---|
| `--no-large --garbage 0`, idle 0 or 16 | 48 MB | 3 | 0.1s |
| `--no-large`, idle 0 | 512 MB | 10 | 1.0s |
| `--no-large`, idle 4 | 768 MB | 19 | 2.5s |
| `--no-large`, idle 16 | 2 GB (fails at 1 GB) | 12 | 1.2s |
| `--pool`, idle 0 | 512 MB | 10 | 1.0s |
| `--pool`, idle 16 | over 512 MB (fails at 512 MB) | — | — |
| fresh large arrays, idle 0 | 512 MB | 3,178 | 140.6s |
| fresh large arrays, idle 16 | 512 MB | 8,488 | 319.2s |

Three separate effects:

1. **Interleaving.** The same 30.5 MB needs 48 MB when the retained nodes are
   allocated together and 512 MB when each sits among 40 garbage nodes. immix
   here does not move objects and reclaims by 256-byte line, so a live node
   alone in a line keeps the line. That is a property of non-moving immix
   rather than a defect, but it is the base the next two multiply.
2. **Idle threads.** With interleaving, the requirement rises with the number
   of threads that never allocate: 512 MB, 768 MB, 2 GB for 0, 4 and 16. With
   contiguous retention there is nothing partly free and idle threads cost
   nothing. In the source, `Heap_Recycle` distributes partly free blocks and
   freed large-object chunks to every mutator thread in turn
   (`NextMutatorThread()`), and each thread allocates from its own share, so
   space handed to an idle thread is unusable until the next collection.
   `Heap_shouldGrow` counts it as available, so the allocating thread
   collects, finds little, and grows the heap one block at a time.
3. **Large objects.** A fresh allocation of 8 KiB or more that does not fit
   runs a full collection on the spot (`LargeAllocator_Alloc`): 3,178
   collections in 140 seconds where pooled buffers take 10 in one. Idle
   threads raise it to 8,488 and 319 seconds, consistent with freed large
   chunks also being distributed.

### Linux

The same on Linux. Rancher Desktop VM: Ubuntu 24.04, aarch64, 2 CPUs, clang
18, built inside it with scala-cli 1.18.0:

| configuration | smallest passing cap |
|---|---|
| `--no-large`, idle 0 | 512 MB (fails at 256 MB) |
| `--no-large`, idle 16 | 2 GB, 1,544 MB committed (fails at 1 GB) |

200,000 steps with fresh large arrays: 1,620 collections, 13.6s. Pooled: 6,
0.3s. Identical to macOS to the megabyte.

```
docker build -t sn-repro:linux -f Dockerfile.linux .
docker run --rm -v "$PWD":/src:ro sn-repro:linux bash -c \
  'cp /src/Repro.scala . && scala-cli --power package --native Repro.scala -o repro -f &&
   GC_MAXIMUM_HEAP_SIZE=1G ./repro --idle 16 --no-large'
```

### Memory checkers see nothing, as they should not

- AddressSanitizer, with `--native-compile -fsanitize=address --native-linking
  -fsanitize=address`: no errors. With idle threads, ASan's own `Failed to
  munmap` at thread exit ends the process before LeakSanitizer runs; without
  them, no leaks.
- Valgrind Memcheck: 0 bytes definitely lost. Its 8 errors are
  `tryGrowStack` deliberately probing the stack from
  `setupStackOverflowGuards`.
- macOS `leaks --atExit` with `MallocStackLogging=1`: 0 leaks, 555 KB malloced.

These watch `malloc`; the immix heap is `mmap`ed and managed by the collector.
`vmmap --summary <pid>` on macOS shows it as one large untagged region.

Not yet checked: release mode, and commix.

## Draft report

Not filed. A search of scala-native/scala-native issues for these terms found
nothing on idle threads or recycling; #4032 and #5052 share the error message
with different causes.

> **immix: heap requirement grows with the number of idle threads, because
> recycled blocks are distributed to threads that never allocate**
>
> Scala Native 0.5.12, immix, multithreading enabled (default). Same figures on
> macOS 26 arm64 and Ubuntu 24.04 aarch64 (clang 18).
>
> A single thread builds a long-lived linked list, one 32-byte node per 40
> short-lived nodes. With 1,000,000 retained nodes (~30 MB live), the smallest
> `GC_MAXIMUM_HEAP_SIZE` that completes is 512 MB with no other threads,
> 768 MB with 4 idle threads and 2 GB with 16 (blocked on a latch, never
> allocating). With the retained nodes allocated contiguously, 48 MB suffices
> regardless of thread count. Reproduction: [Repro.scala, ~130 lines].
>
> `Heap_Recycle` hands each partly free block and each swept large-object
> chunk to the next mutator thread in turn, and allocation only draws on the
> current thread's own recycled list, so with N idle threads the allocating
> thread receives about 1/(N+1) of the reclaimed space until the next
> collection. A cats-effect program has an idle compute pool of one thread per
> core by default, which is how we met it: a 25 GB requirement for a workload
> whose JVM build needs 256 MB.
>
> Separately, an allocation of 8 KiB or more that does not fit triggers a full
> collection immediately; a loop allocating fresh 64 KiB and 128 KiB arrays does
> 3,178 collections in 140 s (8,488 in 319 s with 16 idle threads) against 10
> in 1 s with the buffers reused.
>
> Possible directions: give the allocating thread first claim on recycled
> blocks (or let a thread take blocks from another thread's recycled list when
> its own is empty), and skip idle or blocked mutators when distributing.
