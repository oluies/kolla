package kolla.difftest

/** A minimal JSON writer for the reports. */
object Json:

  def str(s: String): String =
    val sb = new StringBuilder(s.length + 2)
    sb += '"'
    s.foreach {
      case '"'  => sb ++= "\\\""
      case '\\' => sb ++= "\\\\"
      case '\n' => sb ++= "\\n"
      case '\r' => sb ++= "\\r"
      case '\t' => sb ++= "\\t"
      case c if c < 0x20 => sb ++= f"\\u${c.toInt}%04x"
      case c    => sb += c
    }
    sb += '"'
    sb.result()

  def num(l: Long): String   = l.toString
  def num(d: Double): String = if d.isNaN || d.isInfinite then "null" else d.toString
  def bool(b: Boolean): String = b.toString

  def obj(fields: (String, String)*): String =
    fields.map((k, v) => s"${str(k)}:$v").mkString("{", ",", "}")

  def arr(items: Seq[String]): String = items.mkString("[", ",", "]")
