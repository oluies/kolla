package kolla.cli

/** Which build this is. Cross modules cannot ask the runtime, so the answer is
  * a per-platform source file.
  */
object Platform:
  def name: String = "jvm"
