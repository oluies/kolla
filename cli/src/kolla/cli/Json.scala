package kolla.cli

/** A JSON writer for the checker's own output.
  *
  * The reader in `kolla.leanexport.Json` parses; this only writes, and only the
  * shapes `Render` needs.
  */
object Json:

  def str(s: String): String =
    val sb = new StringBuilder("\"")
    s.foreach {
      case '"'  => sb ++= "\\\""
      case '\\' => sb ++= "\\\\"
      case '\n' => sb ++= "\\n"
      case '\r' => sb ++= "\\r"
      case '\t' => sb ++= "\\t"
      case c if c < ' ' => sb ++= f"\\u${c.toInt}%04x"
      case c    => sb += c
    }
    sb += '"'
    sb.result()

  def num(l: Long): String     = l.toString
  def bool(b: Boolean): String = b.toString
  def arr(items: Seq[String]): String = items.mkString("[", ",", "]")
  def obj(fields: (String, String)*): String =
    fields.map((k, v) => s"${str(k)}:$v").mkString("{", ",", "}")
