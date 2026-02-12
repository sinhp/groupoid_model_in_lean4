import Qq

/-! Utilities for shallowly embedded representations of SynthLean expressions
(i.e., for pretending that a `SynthLean.Expr` is a `Lean.Expr`). -/

namespace SynthLean
open Qq

/-- A representation of `⸨..⸩` in the shallow embedding.
It can have whatever type is necessary,
and the actual data is stored in quoted form in `e`
(which must be a closed expression and not refer to any global constants). -/
/- FIXME: Double-quoting `e` may become a performance issue.
An alternative would be to store an auxiliary definition in the environment,
and use its name here. -/
axiom SemAx.{u} (α : Type u) (e : Q(Lean.Expr)) : α

-- TODO: delaborators.

end SynthLean
