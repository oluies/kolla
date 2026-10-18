package kolla.kernel

/** `withDefEqSuccessCache` as a profile change, and what it must not change. */
class DefEqCacheSuite extends munit.FunSuite:

  test("it turns the cache on and says so in the label") {
    val p = KernelProfile.v4_27.withDefEqSuccessCache
    assert(!KernelProfile.v4_27.cacheDefEqSuccess)
    assert(p.cacheDefEqSuccess)
    assertEquals(p.label, "v4.27.0+defeq-cache")
  }

  test("a profile that already caches is returned unchanged") {
    assert(KernelProfile.v4_35.cacheDefEqSuccess)
    assertEquals(KernelProfile.v4_35.withDefEqSuccessCache, KernelProfile.v4_35)
  }

  test("it is idempotent, so the label cannot accumulate suffixes") {
    val once  = KernelProfile.v4_25.withDefEqSuccessCache
    val twice = once.withDefEqSuccessCache
    assertEquals(twice, once)
    assertEquals(twice.label, "v4.25.0+defeq-cache")
  }

  test("it changes nothing else about the profile") {
    // Every other field decides what the kernel accepts, so the whole profile
    // apart from the cache and the label has to be the release's. Derived from
    // the profile itself rather than a list of literals, so a new field is
    // covered the day it is added.
    for base <- KernelProfile.all do
      val p = base.withDefEqSuccessCache
      assertEquals(p, base.copy(label = p.label, cacheDefEqSuccess = true), clue(base.label))
  }
