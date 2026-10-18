package kolla.web

import kolla.kernel.KernelProfile
import scala.scalajs.js

/** The page, built once at start-up.
  *
  * There is no HTML file to keep in step: the element ids `Main` writes to are
  * the ones created here, so a rename cannot leave a dangling lookup.
  */
object Layout:

  def page(): js.Dynamic =
    val root = Dom.elem("main", id = "kolla")

    Dom.append(root, Dom.elem("h1", text = "kolla"))
    Dom.append(
      root,
      Dom.elem(
        "p",
        className = "lede",
        text = "A Lean 4 kernel type checker. Paste a lean4export file and check it here; " +
          "nothing leaves the page."
      )
    )

    val controls = Dom.elem("div", id = "controls")
    val select   = Dom.elem("select", id = "profile")
    KernelProfile.all.reverse.foreach { p =>
      val option = Dom.elem("option", text = p.label)
      option.value = p.label
      Dom.append(select, option)
    }
    Dom.append(
      controls,
      Dom.elem("label", text = "profile"),
      select,
      Dom.elem("button", id = "check", text = "check"),
      Dom.elem("button", id = "clear", text = "clear")
    )
    Dom.append(root, controls)

    val source = Dom.elem("textarea", id = "source")
    source.setAttribute("rows", "14")
    source.setAttribute("spellcheck", "false")
    source.setAttribute("placeholder", "{\"meta\":{...}}\n{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Nat\"}}")
    Dom.append(root, source)

    val verdict = Dom.elem("div", id = "verdict", className = "idle")
    Dom.append(
      verdict,
      Dom.elem("span", id = "status", text = "ready"),
      Dom.elem("span", id = "counts"),
      Dom.elem("span", id = "timing")
    )
    Dom.append(root, verdict)

    val progress = Dom.elem("div", id = "progress")
    Dom.append(progress, Dom.elem("div", id = "bar"))
    Dom.append(root, progress)

    Dom.append(root, Dom.elem("pre", id = "rejection"))
    Dom.append(root, style())
    root

  private def style(): js.Dynamic =
    val css = """
      |:root { color-scheme: light dark; --fg: #1a1a1a; --bg: #fdfdfc; --dim: #666;
      |  --ok: #1a7f37; --bad: #b42318; --line: #d8d8d4; }
      |@media (prefers-color-scheme: dark) {
      |  :root { --fg: #e8e8e6; --bg: #16171a; --dim: #9a9a96;
      |    --ok: #4ac26b; --bad: #ff7b72; --line: #2d2f34; }
      |}
      |body { margin: 0; background: var(--bg); color: var(--fg);
      |  font: 15px/1.5 ui-monospace, SFMono-Regular, Menlo, monospace; }
      |#kolla { max-width: 56rem; margin: 0 auto; padding: 2rem 1rem; }
      |h1 { font-size: 1.4rem; margin: 0 0 .25rem; }
      |.lede { color: var(--dim); margin: 0 0 1.5rem; }
      |#controls { display: flex; gap: .5rem; align-items: center; margin-bottom: .75rem;
      |  flex-wrap: wrap; }
      |label { color: var(--dim); }
      |select, button, textarea { font: inherit; color: var(--fg); background: transparent;
      |  border: 1px solid var(--line); border-radius: 4px; padding: .35rem .6rem; }
      |button { cursor: pointer; }
      |button:hover { border-color: var(--fg); }
      |textarea { width: 100%; box-sizing: border-box; resize: vertical; }
      |#verdict { display: flex; gap: 1rem; flex-wrap: wrap; margin: .75rem 0 .35rem; }
      |#verdict.accepted #status { color: var(--ok); }
      |#verdict.rejected #status, #verdict.error #status { color: var(--bad); }
      |#counts, #timing { color: var(--dim); }
      |#progress { height: 3px; background: var(--line); border-radius: 2px; overflow: hidden; }
      |#bar { height: 100%; width: 0; background: var(--fg); transition: width .1s linear; }
      |#verdict.accepted ~ #progress #bar { background: var(--ok); }
      |#verdict.rejected ~ #progress #bar { background: var(--bad); }
      |#rejection { white-space: pre-wrap; color: var(--bad); margin-top: 1rem; }
      |""".stripMargin
    Dom.elem("style", text = css)
