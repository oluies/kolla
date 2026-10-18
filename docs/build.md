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

## Publishing

The three library modules publish from the JVM platform only:

| module | artifact |
|---|---|
| `kernel.jvm` | `io.github.oluies::kolla-kernel` |
| `export.jvm` | `io.github.oluies::kolla-export` |
| `dsl.jvm` | `io.github.oluies::kolla-dsl` |

`cli` and `web` are programs rather than libraries and `difftest` is a test
harness, so none of them publish.

There is no cross-build over Scala versions, because one is not needed to serve
a consumer on a later release. Scala 3 reads the TASTy of earlier 3.x versions,
so an artifact built with 3.9.0 can be depended on from 3.10.0; only the
reverse fails. Verified rather than assumed: `kernel.jvm.publishM2Local`
followed by a Mill module with `scalaVersion = "3.10.0"` depending on
`io.github.oluies::kolla-kernel:0.1.0` compiles and runs. The repository
already relies on the same guarantee in the other direction of the dependency
graph, since `cats-core_3:2.13.0` is built with Scala 3.3.4.

The 3.9.0 pin above is therefore about Scala.js linking, not about what a
consumer can use.

### Releasing

`io.github.oluies` is already a verified namespace on the Central Portal, so
kolla publishes under it without further namespace work. The release workflow is
tag-driven: pushing `v<version>` publishes, and it first asserts that the tag
agrees with `publishVersion` so that the artifact is the one the tag names.
`workflow_dispatch` runs everything up to the upload, which is the dry run.

Four repository secrets, named for the environment variables Mill reads:

| secret | what it is |
|---|---|
| `MILL_SONATYPE_USERNAME` | Central Portal user token, name |
| `MILL_SONATYPE_PASSWORD` | Central Portal user token, password |
| `MILL_PGP_SECRET_BASE64` | the signing key, armored then base64, one line |
| `MILL_PGP_PASSPHRASE` | that key's passphrase |

Set them with `gh secret set <name> --repo oluies/kolla`, which prompts rather
than taking the value on the command line. None of the four is ever echoed by
the workflow, and none belongs in the repository or in a conversation: a leaked
Portal token can publish under the namespace permanently, because Central
releases are immutable. Revoke and reissue in the Portal if one is exposed.

Locally, `./mill __.jvm.publishArtifacts` builds exactly what would be uploaded
and signs and sends nothing, and `./mill kernel.jvm.publishM2Local` is enough to
test a consumer against a real artifact.
