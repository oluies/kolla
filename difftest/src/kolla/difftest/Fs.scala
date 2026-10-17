package kolla.difftest

import java.nio.file.{FileVisitResult, Files, Path, SimpleFileVisitor}
import java.nio.file.attribute.BasicFileAttributes
import java.io.IOException

/** Filesystem helpers. JVM-only, like the rest of `difftest`. */
object Fs:

  def removeRecursively(p: Path): Unit =
    if Files.exists(p) then
      Files.walkFileTree(
        p,
        new SimpleFileVisitor[Path]:
          override def visitFile(f: Path, attrs: BasicFileAttributes): FileVisitResult =
            Files.delete(f)
            FileVisitResult.CONTINUE
          override def postVisitDirectory(d: Path, e: IOException): FileVisitResult =
            if e != null then throw e
            Files.delete(d)
            FileVisitResult.CONTINUE
      )
      ()
