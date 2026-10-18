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

  /** The release this profile is of, with any optimisation suffix removed.
    *
    * `label` names the kernel that ran and `release` names the behaviour it
    * implements. They differ only for `withDefEqSuccessCache`, which changes
    * no verdict, so this is what a cache key identifies a profile by: adding
    * `--defeq-cache` must not invalidate digests accepted without it. See
    * docs/semantics.md P15 and K18.
    */
  def release: String = label.stripSuffix(KernelProfile.defeqCacheSuffix)

  /** The same profile, keeping the positive `is_def_eq` cache that only v4.35
    * has.
    *
    * This is an optimisation and not a change of profile. An entry is written
    * only where `is_def_eq` already answered true, and `succeededBefore` does
    * nothing but short-circuit to that answer; `TypeChecker` is one instance
    * per declaration, and within one the environment is fixed and the local
    * context append-only with globally unique free variables (K6), so a pair
    * that answered true cannot answer otherwise later.
    *
    * It can still change an outcome in one way: caching cuts the step count,
    * so a declaration that would exhaust `maxSteps` without it may pass with
    * it. That guard is kolla's and not Lean's. See docs/semantics.md K18.
    *
    * The label carries the change so that any report naming the profile says
    * the kernel was not the release's. A profile that already caches is
    * returned unchanged.
    */
  def withDefEqSuccessCache: KernelProfile =
    if cacheDefEqSuccess then this
    else copy(label = label + KernelProfile.defeqCacheSuffix, cacheDefEqSuccess = true)

object KernelProfile:

  /** Marks a profile whose kernel keeps an optimisation the release did not. */
  val defeqCacheSuffix: String = "+defeq-cache"

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
