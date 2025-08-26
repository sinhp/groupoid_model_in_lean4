prelude
public import Init.Core

/-! ## Leanternal prelude

The prelude of every Leanternal theory.

This imports part of the default Lean prelude,
including definitions that we don't support (e.g. `Prop`-valued `Eq`),
because it's difficult to make Lean function without that. -/

universe u

/-- The identity type. -/
inductive Id {α : Type u} : α → α → Type u where
  | refl (a : α) : Id a a

@[match_pattern] def Id.rfl {α : Type u} {a : α} : Id a a := Id.refl a
