package kolla.leanexport

final class ExportException(val detail: String, val lineNumber: Int)
    extends RuntimeException(
      if lineNumber > 0 then s"line $lineNumber: $detail" else detail
    ):
  def atLine(n: Int): ExportException =
    if lineNumber > 0 then this else new ExportException(detail, n)

object ExportException:
  def apply(detail: String): ExportException             = new ExportException(detail, 0)
  def apply(detail: String, line: Int): ExportException  = new ExportException(detail, line)
