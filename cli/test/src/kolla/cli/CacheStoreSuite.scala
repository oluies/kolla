package kolla.cli

import cats.effect.IO
import fs2.io.file.{Files, Path}
import kolla.leanexport.Digest
import munit.CatsEffectSuite

/** The cache file: what survives a run, and what a damaged file costs. */
class CacheStoreSuite extends CatsEffectSuite:

  private def withTemp[A](f: Path => IO[A]): IO[A] =
    Files[IO].tempFile(None, "kolla-cache", ".txt", None).use(f)

  private val d1 = Digest.mixString(Digest.seed, "one")
  private val d2 = Digest.mixString(Digest.seed, "two")

  test("a missing file loads as an empty cache") {
    CacheStore.load("/nonexistent/kolla/cache.txt").map { s =>
      assertEquals(s.loaded, 0)
      assert(!s.contains(d1))
    }
  }

  test("what one run accepts, the next run reads back") {
    withTemp { p =>
      for
        a <- CacheStore.load(p.toString)
        _ <- IO(a.accepted(d1))
        _ <- IO(a.accepted(d2))
        _ <- a.flush
        b <- CacheStore.load(p.toString)
      yield
        assertEquals(b.loaded, 2)
        assert(b.contains(d1))
        assert(b.contains(d2))
    }
  }

  test("flushing twice does not duplicate an entry") {
    withTemp { p =>
      for
        a <- CacheStore.load(p.toString)
        _ <- IO(a.accepted(d1))
        _ <- a.flush
        _ <- a.flush
        _ <- IO(a.accepted(d1))
        _ <- a.flush
        b <- CacheStore.load(p.toString)
      yield assertEquals(b.loaded, 1)
    }
  }

  test("appending keeps what an earlier run wrote") {
    // This is what makes a failure partway cheap to retry: the second run adds
    // to the file rather than replacing it.
    withTemp { p =>
      for
        a <- CacheStore.load(p.toString)
        _ <- IO(a.accepted(d1))
        _ <- a.flush
        b <- CacheStore.load(p.toString)
        _ <- IO(b.accepted(d2))
        _ <- b.flush
        c <- CacheStore.load(p.toString)
      yield
        assertEquals(c.loaded, 2)
        assert(c.contains(d1) && c.contains(d2))
    }
  }

  test("a damaged line is skipped, not fatal") {
    // The worst a bad line may cost is a re-check, so a cache with junk in it
    // still loads the entries that are intact.
    withTemp { p =>
      val text = s"${d1.hex}\nnot-a-digest\n\n${d2.hex}\nzz\n"
      for
        _ <- fs2.Stream
               .emit(text)
               .through(fs2.text.utf8.encode)
               .through(Files[IO].writeAll(p))
               .compile
               .drain
        s <- CacheStore.load(p.toString)
      yield
        assertEquals(s.loaded, 2)
        assert(s.contains(d1) && s.contains(d2))
    }
  }
