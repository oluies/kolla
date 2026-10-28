package kolla.cli

import cats.effect.IO
import cats.effect.std.Console
import kolla.kernel.{Axioms, Environment, KernelProfile, Name, Pretty}
import kolla.leanexport.{JsonWriter, ReplayJson}

/** A resident kernel: one environment, many questions.
  *
  * Every other mode pays for the whole export before it answers anything,
  * which on Mathlib is 83 seconds and 9.40 GB (docs/scale.md). A caller with
  * many small questions pays that per question. `--serve` loads once and
  * answers from the environment it keeps.
  *
  * A request is one line on standard input: an operation, then for most of
  * them one argument running to the end of the line. A reply is one JSON
  * object per line on standard output. A request that fails is answered with
  * `"ok": false` rather than ending the session, because a caller generating
  * requests will get some of them wrong. See docs/semantics.md S1.
  */
object Serve:

  /** What the session holds between requests. */
  final case class State(profile: KernelProfile, env: Environment, maxSteps: Long, served: Long):
    def declarations: Int = env.size

  /** Which of a candidate's declarations the base has not checked already.
    *
    * `Replay` admits the rest unchecked and reports them as carried over, the
    * same treatment `--check` gives a declaration outside its prefix (P14).
    * Here that is not a narrowing of the verdict: the base was checked when it
    * was loaded.
    */
  def delta(base: Environment): Name => Boolean = n => !base.contains(n)

  /** An operation and its argument, which is the rest of the line. */
  def split(line: String): (String, String) =
    val t = line.trim
    val i = t.indexWhere(_.isWhitespace)
    if i < 0 then (t, "") else (t.take(i), t.drop(i).trim)

  private def reply(op: String, nanos: Long, fields: (String, String)*): String =
    JsonWriter.obj(
      (("op" -> JsonWriter.str(op)) +: fields) ++
        Seq("ms" -> JsonWriter.num(nanos / 1000000L))*
    )

  private def failed(op: String, nanos: Long, why: String): String =
    reply(op, nanos, "ok" -> JsonWriter.bool(false), "error" -> JsonWriter.str(why))

  /** Reads an export and checks what the base does not already hold.
    *
    * No digest cache: a seeded replay cannot carry one, because the base's
    * names have no digest in this replay's table and two different bases would
    * give one candidate the same digest. `Replay` refuses the combination.
    */
  private def replay(
      state: State,
      file: String,
      bytes: String => fs2.Stream[IO, Byte]
  ): IO[Either[Check.Failure, Check.Result]] =
    Check.stream(
      file, bytes(file), state.profile, abortOnReject = false,
      (_, _, _) => IO.unit, None, delta(state.env), None, None, None,
      state.maxSteps, state.env
    )

  /** Answers one request, and says whether the session goes on. */
  def handle(
      state: State,
      line: String,
      bytes: String => fs2.Stream[IO, Byte]
  ): IO[(State, Option[String], Boolean)] =
    val (op, arg) = split(line)
    val next      = state.copy(served = state.served + 1)

    def timed[A](io: IO[A]): IO[(A, Long)] =
      for
        t0 <- IO.monotonic
        a  <- io
        t1 <- IO.monotonic
      yield (a, (t1 - t0).toNanos)

    def load(keep: Boolean): IO[(State, Option[String], Boolean)] =
      if arg.isEmpty then IO.pure((next, Some(failed(op, 0L, s"$op needs a file")), true))
      // Standard input is the protocol here, so it cannot also be the export.
      else if arg == "-" then
        IO.pure((next, Some(failed(op, 0L, "--serve reads requests on stdin; name a file")), true))
      else
        timed(replay(state, arg, bytes).attempt).map { (outcome, took) =>
          outcome match
            case Left(e) => (next, Some(failed(op, took, message(e))), true)
            case Right(Left(f)) => (next, Some(failed(op, took, f.message)), true)
            case Right(Right(r)) =>
              val t = r.tally
              (
                if keep then next.copy(env = r.environment) else next,
                Some(reply(op, took,
                  "ok"           -> JsonWriter.bool(t.ok),
                  "file"         -> JsonWriter.str(arg),
                  "accepted"     -> JsonWriter.num(t.accepted.toLong),
                  "rejected"     -> JsonWriter.num(t.rejected.toLong),
                  "carriedOver"  -> JsonWriter.num(t.carriedOver.toLong),
                  "errored"      -> JsonWriter.num(t.failed.toLong),
                  "declarations" -> JsonWriter.num(
                    (if keep then r.environment.size else state.env.size).toLong
                  )
                )),
                true
              )
        }

    def named(f: Name => IO[(State, Option[String], Boolean)]): IO[(State, Option[String], Boolean)] =
      if arg.isEmpty then IO.pure((next, Some(failed(op, 0L, s"$op needs a name")), true))
      else f(Name.parse(arg))

    op match
      case "" => IO.pure((state, None, true))

      case "load"  => load(keep = true)
      case "check" => load(keep = false)

      case "axioms" =>
        named { n =>
          timed(IO(Axioms.of(state.env, n))).map { (closure, took) =>
            closure match
              case Left(why) => (next, Some(failed(op, took, why)), true)
              case Right(c) =>
                (next, Some(reply(op, took,
                  "ok"     -> JsonWriter.bool(!c.hasSorry && c.unusual.isEmpty),
                  "result" -> ReplayJson.axioms(
                    c.declaration.toString, c.axioms.map(_.toString),
                    c.hasSorry, c.unusual.map(_.toString), state.profile.label
                  ),
                  "constants" -> JsonWriter.num(c.constants.toLong)
                )), true)
          }
        }

      case "type" =>
        named { n =>
          timed(IO(state.env.find(n))).map { (info, took) =>
            info match
              case None => (next, Some(failed(op, took, s"unknown constant '$n'")), true)
              case Some(i) =>
                (next, Some(reply(op, took,
                  "ok"   -> JsonWriter.bool(true),
                  "name" -> JsonWriter.str(n.toString),
                  "type" -> JsonWriter.str(Pretty.expr(i.tpe, Int.MaxValue))
                )), true)
          }
        }

      case "eval" =>
        if arg.isEmpty then IO.pure((next, Some(failed(op, 0L, "eval needs a term")), true))
        else
          kolla.dsl.LeanParser.parse(arg) match
            case Left(err) =>
              IO.pure((next, Some(failed(op, 0L, s"${err.message} at offset ${err.offset}")), true))
            case Right(term) =>
              timed(IO(kolla.dsl.Evaluate(state.env, state.profile, term, state.maxSteps)).attempt)
                .map { (outcome, took) =>
                  outcome match
                    case Left(e)             => (next, Some(failed(op, took, message(e))), true)
                    case Right(Left(why))    => (next, Some(failed(op, took, why)), true)
                    case Right(Right(res)) =>
                      (next, Some(reply(op, took,
                        "ok"      -> JsonWriter.bool(true),
                        "partial" -> JsonWriter.bool(res.partial),
                        "result"  -> ReplayJson.evaluation(
                          arg, Pretty.expr(res.value, Int.MaxValue),
                          Pretty.expr(res.tpe, Int.MaxValue), state.profile.label
                        )
                      )), true)
                }

      case "status" =>
        IO.pure((next, Some(reply(op, 0L,
          "ok"              -> JsonWriter.bool(true),
          "profile"         -> JsonWriter.str(state.profile.label),
          "declarations"    -> JsonWriter.num(state.declarations.toLong),
          "quotInitialized" -> JsonWriter.bool(state.env.quotInitialized),
          "maxSteps"        -> JsonWriter.num(state.maxSteps),
          "served"          -> JsonWriter.num(state.served)
        )), true))

      case "quit" =>
        IO.pure((next, Some(reply(op, 0L, "ok" -> JsonWriter.bool(true))), false))

      case other =>
        IO.pure((next, Some(failed("unknown", 0L, s"unknown operation '$other'")), true))

  /** A thrown kernel exception reads as a rejection, not as a crash. */
  private def message(e: Throwable): String =
    Option(e.getMessage).getOrElse(e.getClass.getName)

  /** The session: a line in, a line out, until standard input ends or the
    * caller says `quit`.
    */
  def run(o: Options, bytes: String => fs2.Stream[IO, Byte]): IO[cats.effect.ExitCode] =
    val profile = Options.profileOf(o)
    val start   = State(profile, Environment.empty, o.maxSteps, 0L)

    val preload: IO[State] =
      o.files.headOption.fold(IO.pure(start)) { f =>
        handle(start, s"load $f", bytes).flatMap { (s, out, _) =>
          out.fold(IO.unit)(Console[IO].println) *> IO.pure(s)
        }
      }

    preload.flatMap { loaded =>
      fs2.io
        .stdin[IO](1024 * 64)
        .through(fs2.text.utf8.decode)
        .through(fs2.text.lines)
        .evalMapAccumulate(Option(loaded)) { (open, line) =>
          open match
            case None => IO.pure((None, ()))
            case Some(s) =>
              handle(s, line, bytes).flatMap { (s2, out, go) =>
                out.fold(IO.unit)(Console[IO].println).as((if go then Some(s2) else None, ()))
              }
        }
        .takeWhile((open, _) => open.isDefined, takeFailure = true)
        .compile
        .drain
        .as(cats.effect.ExitCode.Success)
    }
