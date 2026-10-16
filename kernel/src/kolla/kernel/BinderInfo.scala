package kolla.kernel

enum BinderInfo:
  case Default, Implicit, StrictImplicit, InstImplicit

  def isExplicit: Boolean = this match
    case Default => true
    case _       => false

  def isImplicit: Boolean     = this == BinderInfo.Implicit
  def isStrictImplicit: Boolean = this == BinderInfo.StrictImplicit
  def isInstImplicit: Boolean = this == BinderInfo.InstImplicit

  def toInt: Int = this match
    case Default        => 0
    case Implicit       => 1
    case StrictImplicit => 2
    case InstImplicit   => 3

object BinderInfo:
  def fromInt(i: Int): BinderInfo = i match
    case 0 => Default
    case 1 => Implicit
    case 2 => StrictImplicit
    case 3 => InstImplicit
    case _ => throw new IllegalArgumentException(s"bad BinderInfo $i")
