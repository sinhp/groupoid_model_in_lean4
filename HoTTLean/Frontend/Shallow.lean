import Qq

/-! Utilities for shallowly embedded representations of SynthLean expressions
(i.e., for pretending that a `SynthLean.Expr` is a `Lean.Expr`). -/

namespace SynthLean
open Qq

/-- An optional specification of the expected theory.

Copied from `Lean.Parser.Tactic.valConfigItem`. -/
syntax theorySpec := atomic(" (" &"theory" " := ") withoutPosition(term) ") "

/-- A SynthLean type expression.

#### Expected theory

This macro needs to know the *expected theory* `𝕋`
w.r.t. which the type `A` should be typechecked,
so that we'll have `𝕋 ∣ [] ⊢[?l] A`.
When the optional `(theory := thy)` argument is provided,
the expected theory is `thy`.
Otherwise the expected theory is inferred from the expected type `eT`:
- When `eT = SynthLean.Expr s.SigInt` for `s : UHomSeq 𝒞`,
  the expected theory is `s.thyInt`.
- Otherwise inference fails. -/
syntax "tp%" (theorySpec)? "{" term "}" : term
/-- A SynthLean term expression. See `tp%{..}` for more info. -/
syntax "tm%" (theorySpec)? "{" term "}" : term

/-- *Deinterpretation* `⸨..⸩` (the *Scott unbracket*) works in any `tm%{..}/tp%{..}` context
where the expected theory is `s.thyInt`.
It allows us to name a semantic type in the syntax
(so, in a sense, it is inverse to interpretation).

It obeys the following rule,
where `⊢[..]` is the internal typing judgment,
and `⊢` is Lean's usual typing.
```
Γ ⊢ t : 𝟭_ _ ⟶ s[l].Ty
---------------------------------
s.thyInt ∣ · ⊢[l+1] ⸨t⸩ : .univ l
```
where `Γ` is the external local context
in which `tm%{..}/tp%{..}` is being elaborated.

TODO: Also support semantic term deinterpretation. -/
syntax "⸨" term "⸩" : term

/-- A representation of `⸨t⸩` in the shallow embedding.
It can have whatever type is necessary.
The external arrow `t` is stored in quoted form in `e`.
It must be a closed expression and not refer to any global constants. -/
/- FIXME: Double-quoting `e` may become a performance issue.
One alternative would be to store an auxiliary definition in the environment,
and use its name here. -/
axiom SemAx.{u} (α : Type u) (e : Lean.Expr) : α

end SynthLean
