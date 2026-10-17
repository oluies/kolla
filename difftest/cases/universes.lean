/-- Universe-polymorphic definitions exercise level normalisation. -/
def idU.{u} (α : Sort u) (a : α) : α := a

def pairU.{u, v} (α : Sort u) (β : Sort v) : Sort (max 1 (max u v)) := PProd α β

/-- `imax` arises from a Pi whose codomain may be a proposition. -/
def arrowU.{u, v} (α : Sort u) (β : Sort v) : Sort (imax u v) := α → β

theorem maxIdem.{u} (α : Sort u) : pairU α α = PProd α α := rfl

/-- `max u 0` normalises to `u`. -/
def maxZero.{u} (α : Sort u) : Sort (max u 0) := α

/-- `imax u 0` normalises to `0`, so this lands in `Prop`. -/
def imaxZero.{u} (α : Sort u) : Sort (imax u 0) := α → False
