package kolla.kernel

/** The kernel decisions that differ between Lean releases.
  *
  * `src/kernel` is not behaviourally stable across releases: v4.35.0 added
  * soundness checks and changed `is_prop`, so a declaration v4.25.0 accepts can
  * be rejected by v4.35.0 and vice versa. A checker that has to agree with
  * `lean4checker` from several releases therefore needs the release as a
  * parameter. See docs/semantics.md K1.
  */
final case class KernelProfile(
    label: String,
    /** Constructor `string_lit_to_constructor` wraps a character list in.
      * `String.mk` up to v4.26, `String.ofList` from v4.27.
      */
    stringLiteralCtor: Name,
    /** `is_prop`: `normalizes_to_zero(sort_level(s))` from v4.35, a syntactic
      * comparison against `Prop` before that.
      */
    propByNormalization: Boolean,
    /** Upper bound in bytes on the `Nat` numerals the kernel will compute;
      * unbounded before v4.35. `LEAN_NAT_MAX_SIZE`.
      */
    natMaxSizeBytes: Option[Long],
    /** v4.35 rejects a projection index that does not fit in a 32-bit unsigned;
      * earlier releases truncated it. */
    boundedProjIdx: Boolean,
    /** v4.35 `check_uniform_ind_occs`: occurrences of a datatype being declared
      * must be applied to the parameters and universe levels of the block. */
    checkUniformIndOccs: Boolean,
    /** v4.35 `check_recursors`: each generated recursor's type is checked and
      * each computation rule is checked to be type-preserving. */
    checkRecursors: Boolean,
    /** Structure eta and the unit-like rule require `is_non_rec_structure` from
      * v4.35, which additionally demands the inductive not be recursive;
      * earlier releases used `is_structure_like`, which did not. */
    etaStructRequiresNonRec: Boolean,
    /** v4.35 keeps a positive `is_def_eq` cache alongside the negative one. */
    cacheDefEqSuccess: Boolean
):
  def natMaxSize: Long = natMaxSizeBytes.getOrElse(Long.MaxValue)

object KernelProfile:

  val stringMk: Name     = Name.parse("String.mk")
  val stringOfList: Name = Name.parse("String.ofList")

  /** 128 MB, `LEAN_NAT_MAX_SIZE_DEFAULT`. */
  val natMaxSizeDefault: Long = 128L * 1024L * 1024L

  /** Lean v4.35.0, the latest stable release. */
  val v4_35: KernelProfile = KernelProfile(
    label = "v4.35.0",
    stringLiteralCtor = stringOfList,
    propByNormalization = true,
    natMaxSizeBytes = Some(natMaxSizeDefault),
    boundedProjIdx = true,
    checkUniformIndOccs = true,
    checkRecursors = true,
    etaStructRequiresNonRec = true,
    cacheDefEqSuccess = true
  )

  /** Lean v4.27.0. */
  val v4_27: KernelProfile = v4_35.copy(
    label = "v4.27.0",
    propByNormalization = false,
    natMaxSizeBytes = None,
    boundedProjIdx = false,
    checkUniformIndOccs = false,
    checkRecursors = false,
    etaStructRequiresNonRec = false,
    cacheDefEqSuccess = false
  )

  /** Lean v4.25.0, the last release lean4export covered with its text format. */
  val v4_25: KernelProfile = v4_27.copy(
    label = "v4.25.0",
    stringLiteralCtor = stringMk
  )

  val default: KernelProfile = v4_35

  val all: List[KernelProfile] = List(v4_25, v4_27, v4_35)

  /** Resolves an elan toolchain spec or a bare version to a profile. Releases
    * between the pinned ones take the nearest profile at or below them.
    */
  def forToolchain(spec: String): KernelProfile =
    val v = spec.substring(spec.lastIndexOf(':') + 1).stripPrefix("v")
    val parts = v.split('.').toList.flatMap(p => p.takeWhile(_.isDigit).toIntOption)
    parts match
      case major :: minor :: _ if major == 4 && minor >= 35 => v4_35
      case major :: minor :: _ if major == 4 && minor >= 27 => v4_27
      case major :: minor :: _ if major == 4               => v4_25
      case _                                                => default
