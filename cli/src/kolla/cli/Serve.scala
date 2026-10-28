package kolla.cli

import cats.effect.IO
import cats.effect.std.Console
import kolla.kernel.{Axioms, Environment, KernelProfile, Name, Pretty, TypeChecker}
import kolla.leanexport.{JsonWriter, ReplayJson, ReplayOutcome, ReplayTally}

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
  final case class State(
      profile: KernelProfile,
      env: Environment,
      maxSteps: Long,
      served: Long,
      /** The wall-clock budget per declaration, set by a `deadline` request. */
      timeLimit: Option[TypeChecker.TimeLimit] = None
  ):
    def declarations: Int = env.size
    def deadlineMillis: Long = timeLimit.fold(0L)(_.nanos / 1000000L)

  /** How many names a listing answers with. A caller asking for a prefix of
    * Mathlib wants a handle on it, not 729,263 of them in one line.
    */
  val maxNames: Int = 200

  /** Whether every declaration of a replay went through the kernel.
    *
    * `Replay` carries a rejected declaration into the environment unchecked so
    * that the rest of the file can still be replayed (P6), so the environment
    * a failed replay ends with holds something the kernel did not accept. That
    * is why such a load is not kept: the base this session answers from, and
    * checks candidates against, holds only what passed.
    *
    * Carried-over declarations are not counted against it. The only selector
    * here is `delta`, which answers false exactly for the names the base
    * already holds, and those were checked when the base was loaded. Requiring
    * none of them would refuse every load after the first. `notReached` cannot
    * be other than zero, since the session never aborts on a rejection.
    */
  def checked(t: ReplayTally): Boolean =
    t.rejected == 0 && t.failed == 0 && t.notReached == 0

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
      bytes: String => fs2.Stream[IO, Byte],
      reason: (Name, ReplayOutcome) => IO[Unit]
  ): IO[Either[Check.Failure, Check.Result]] =
    Check.stream(
      file, bytes(file), state.profile, abortOnReject = false,
      (n, outcome, _) => reason(n, outcome), None, delta(state.env), None, None, None,
      state.maxSteps, state.env, state.timeLimit
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
        // The first declaration that did not pass, so a reply says why and not
        // only how many. A time limit is reported through it, which is the
        // point of having one: the caller learns which constant the reduction
        // was in when the budget ran out.
        var first: Option[String] = None
        val note: (Name, ReplayOutcome) => IO[Unit] = (n, outcome) =>
          IO {
            val bad = outcome match
              case _: ReplayOutcome.Rejected => true
              case _: ReplayOutcome.Failed   => true
              case _                         => false
            if first.isEmpty && bad then
              first = Some(ReplayTally.detail(outcome).fold(n.toString)(d => s"$n: $d"))
          }
        timed(replay(state, arg, bytes, note).attempt).map { (outcome, took) =>
          outcome match
            case Left(e) => (next, Some(failed(op, took, message(e))), true)
            case Right(Left(f)) => (next, Some(failed(op, took, f.message)), true)
            case Right(Right(r)) =>
              val t    = r.tally
              val held = keep && checked(t)
              (
                if held then next.copy(env = r.environment) else next,
                Some(reply(op, took,
                  "ok"           -> JsonWriter.bool(t.ok),
                  "file"         -> JsonWriter.str(arg),
                  "kept"         -> JsonWriter.bool(held),
                  "accepted"     -> JsonWriter.num(t.accepted.toLong),
                  "rejected"     -> JsonWriter.num(t.rejected.toLong),
                  "carriedOver"  -> JsonWriter.num(t.carriedOver.toLong),
                  "errored"      -> JsonWriter.num(t.failed.toLong),
                  "declarations" -> JsonWriter.num(
                    (if held then r.environment.size else state.env.size).toLong
                  ),
                  "reason" -> first.fold("null")(JsonWriter.str)
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

      case "deadline" =>
        arg.replace("_", "").toLongOption match
          case None =>
            IO.pure((next, Some(failed(op, 0L, "deadline expects a number of milliseconds")), true))
          case Some(ms) if ms < 0 =>
            IO.pure((next, Some(failed(op, 0L, "deadline expects a positive number, or 0 for none")), true))
          case Some(ms) =>
            val limit =
              if ms == 0 then None
              else Some(new TypeChecker.TimeLimit(ms * 1000000L, () => System.nanoTime()))
            val s2 = next.copy(timeLimit = limit)
            IO.pure((s2, Some(reply(op, 0L,
              "ok"       -> JsonWriter.bool(true),
              "deadline" -> JsonWriter.num(s2.deadlineMillis)
            )), true))

      case "names" =>
        timed(IO {
          val hits = state.env.names.filter(_.toString.startsWith(arg))
          (hits.length, hits.take(Serve.maxNames))
        }).map { (pair, took) =>
          val (total, shown) = pair
          (next, Some(reply(op, took,
            "ok"    -> JsonWriter.bool(true),
            "prefix" -> JsonWriter.str(arg),
            "total" -> JsonWriter.num(total.toLong),
            "names" -> JsonWriter.arr(shown.map(n => JsonWriter.str(n.toString)))
          )), true)
        }

      case "mentions" =>
        named { n =>
          timed(IO {
            if !state.env.contains(n) then None
            else
              val hits = state.env.declarations.collect {
                case i if Axioms.referencesOf(i).contains(n) => i.name
              }
              Some((hits.length, hits.take(Serve.maxNames)))
          }).map { (found, took) =>
            found match
              case None => (next, Some(failed(op, took, s"unknown constant '$n'")), true)
              case Some((total, shown)) =>
                (next, Some(reply(op, took,
                  "ok"    -> JsonWriter.bool(true),
                  "name"  -> JsonWriter.str(n.toString),
                  "total" -> JsonWriter.num(total.toLong),
                  "names" -> JsonWriter.arr(shown.map(m => JsonWriter.str(m.toString)))
                )), true)
          }
        }

      case "unfold" =>
        named { n =>
          timed(IO(state.env.find(n))).map { (info, took) =>
            info match
              case None => (next, Some(failed(op, took, s"unknown constant '$n'")), true)
              case Some(i) =>
                i.value(allowOpaque = true) match
                  case None =>
                    (next, Some(failed(op, took, s"'$n' has no value to unfold")), true)
                  case Some(v) =>
                    (next, Some(reply(op, took,
                      "ok"    -> JsonWriter.bool(true),
                      "name"  -> JsonWriter.str(n.toString),
                      "value" -> JsonWriter.str(Pretty.expr(v, Int.MaxValue)),
                      "type"  -> JsonWriter.str(Pretty.expr(i.tpe, Int.MaxValue))
                    )), true)
          }
        }

      case "gate" =>
        // The comparator's criterion: a named set, and what falls outside it.
        if arg.isEmpty then
          IO.pure((next, Some(failed(op, 0L, "gate needs a declaration, then the axioms it may rest on")), true))
        else
          val parts     = arg.split("\\s+").toList
          val target    = Name.parse(parts.head)
          val permitted = parts.tail.flatMap(_.split(",")).map(_.trim).filter(_.nonEmpty).map(Name.parse).toSet
          timed(IO(Axioms.of(state.env, target))).map { (closure, took) =>
            closure match
              case Left(why) => (next, Some(failed(op, took, why)), true)
              case Right(c) =>
                val outside = Axioms.within(c, permitted)
                (next, Some(reply(op, took,
                  "ok"           -> JsonWriter.bool(outside.isEmpty),
                  "declaration"  -> JsonWriter.str(c.declaration.toString),
                  "permitted"    -> JsonWriter.arr(permitted.toVector.map(_.toString).sorted.map(JsonWriter.str)),
                  "notPermitted" -> JsonWriter.arr(outside.map(m => JsonWriter.str(m.toString))),
                  "sorry"        -> JsonWriter.bool(c.hasSorry)
                )), true)
          }
        end if

      case "status" =>
        IO.pure((next, Some(reply(op, 0L,
          "ok"              -> JsonWriter.bool(true),
          "profile"         -> JsonWriter.str(state.profile.label),
          "declarations"    -> JsonWriter.num(state.declarations.toLong),
          "quotInitialized" -> JsonWriter.bool(state.env.quotInitialized),
          "maxSteps"        -> JsonWriter.num(state.maxSteps),
          "deadline"        -> JsonWriter.num(state.deadlineMillis),
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
    val start   = State(profile, Environment.empty, o.maxSteps, 0L, Main.timeLimitOf(o))

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
