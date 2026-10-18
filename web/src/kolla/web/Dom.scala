package kolla.web

import scala.scalajs.js
import scala.scalajs.js.annotation.JSGlobal

/** The browser API this page uses.
  *
  * `scalajs-dom` is not one of the dependencies the project allows, so the few
  * calls needed are declared here rather than pulled in. Keeping them in one
  * file also keeps `Main` readable as a description of the page.
  */
@js.native
@JSGlobal("document")
object document extends js.Object:
  def getElementById(id: String): js.Dynamic             = js.native
  def createElement(tag: String): js.Dynamic             = js.native
  def createTextNode(text: String): js.Dynamic           = js.native
  val body: js.Dynamic                                   = js.native
  var title: String                                      = js.native

@js.native
@JSGlobal("window")
object window extends js.Object:
  def setTimeout(f: js.Function0[Any], ms: Double): Double = js.native
  def requestAnimationFrame(f: js.Function1[Double, Any]): Double = js.native

object Dom:

  /** An element with a tag, optional id and optional text, in one call. */
  def elem(tag: String, id: String = "", text: String = "", className: String = ""): js.Dynamic =
    val e = document.createElement(tag)
    if id.nonEmpty then e.id = id
    if className.nonEmpty then e.className = className
    if text.nonEmpty then e.textContent = text
    e

  def byId(id: String): js.Dynamic = document.getElementById(id)

  def append(parent: js.Dynamic, children: js.Dynamic*): js.Dynamic =
    children.foreach(c => parent.appendChild(c))
    parent

  def setText(id: String, text: String): Unit =
    val e = byId(id)
    if e != null then e.textContent = text

  def setHtmlClass(id: String, className: String): Unit =
    val e = byId(id)
    if e != null then e.className = className

  def on(e: js.Dynamic, event: String)(handler: => Unit): Unit =
    e.addEventListener(event, (_: js.Dynamic) => handler)

  def value(id: String): String =
    val e = byId(id)
    if e == null then "" else e.value.asInstanceOf[String]
