/-! ## Leanternal prelude

The prelude of every Leanternal theory.

This imports the default Lean prelude,
including definitions that we don't support (e.g. `Prop`-valued `Eq`),
because it's difficult to make Lean function without that. -/

universe u

/-- The identity type. -/
inductive Identity {α : Type u} : α → α → Type u where
  | refl (a : α) : Identity a a

@[match_pattern] def Identity.rfl {α : Type u} {a : α} : Identity a a :=
  Identity.refl a
