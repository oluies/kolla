package kolla.leanexport

enum ExportFormat:
  /** lean4export before the v2.0.0 format change; Lean v4.12.0 .. v4.19. */
  case TextV1
  /** lean4export v2.0.0 text format; Lean v4.20 .. v4.26. */
  case TextV2
  /** lean4export NDJSON format; `version` is the value of `meta.format.version`. */
  case Ndjson(version: String)

  def isText: Boolean = this match
    case TextV1 | TextV2 => true
    case _               => false

  /** NDJSON 3.0.x wraps definition groups in arrays and spells the inductive
    * fields `inductiveVals`/`constructorVals`/`recursorVals`.
    */
  def ndjsonMajorMinor: Option[(Int, Int)] = this match
    case Ndjson(v) =>
      v.split('.').toList match
        case a :: b :: _ => a.toIntOption.zip(b.toIntOption)
        case _           => None
    case _ => None

object ExportFormat:
  def parse(s: String): ExportFormat = s.trim match
    case "text-v1" | "v1" | "1" => TextV1
    case "text-v2" | "v2" | "2" => TextV2
    case other if other.startsWith("ndjson:") => Ndjson(other.stripPrefix("ndjson:"))
    case other if other.startsWith("3.")      => Ndjson(other)
    case other => throw ExportException(s"unknown export format '$other'")
