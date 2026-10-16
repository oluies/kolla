# Build

Mill 1.3.0, Scala 3.9.0, Scala.js 1.22.0, Scala Native 0.5.12.

Scala 3.10.0 is the latest release but cannot be used here: linking any Scala.js module
that reaches a `RichInt` or `RichChar` method fails with

    Referring to non-existent method scala.Int$.until(int,int)scala.collection.immutable.Range
    Referring to non-existent method scala.Char$.isLetter(char)boolean

The forwarders exist in `scalajs-scalalib_2.13:3.10.0` but the linker does not resolve
them. `kernel.jvm.compile` and `kernel.js.compile` both succeed; only `fastLinkJS` fails.
Scala 3.9.0 links and runs on all three platforms.

Commands:

    mill kernel.jvm.test
    mill kernel.js.test
    mill kernel.native.test
    mill __.test

## Lean toolchains on this host

`lake build` of lean4export succeeds for Lean v4.35.0 and the binary runs.

The Lean v4.12.0 toolchain installs and builds, but the resulting binary does not
start on macOS 27:

    dyld[45339]: __DATA_CONST segment missing SG_READ_ONLY flag in .lake/build/bin/lean4export

So no text v1 export could be produced on this machine; the text v1 reader is
tested against hand-written files transcribed from `dumpConstant` at `d797849`.
