package kolla.kernel

enum DataValue:
  case OfString(value: String)
  case OfBool(value: Boolean)
  case OfName(value: Name)
  case OfNat(value: BigInt)
  case OfInt(value: BigInt)

final case class KVMap(entries: List[(Name, DataValue)]):
  def isEmpty: Boolean = entries.isEmpty
  def get(n: Name): Option[DataValue] = entries.collectFirst { case (k, v) if k == n => v }

object KVMap:
  val empty: KVMap = KVMap(Nil)
