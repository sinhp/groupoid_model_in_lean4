/-! ## SynthLean prelude

The prelude of every SynthLean theory.

This imports the default Lean prelude,
including definitions that we don't support (e.g. `Prop`-valued `Eq`),
because it's difficult to make Lean function without that. -/

universe u

/-- The identity type. -/
inductive Identity {α : Type u} : α → α → Type u where
  | refl (a : α) : Identity a a

namespace Identity

-- FIXME: add universe polymorphism via `(l : Nat) → { d : CheckedAx .. // d.l = l }`
@[match_pattern] def rfl₀ {α : Type 0} {a : α} : Identity a a :=
  Identity.refl a

@[match_pattern] def rfl₁ {α : Type 1} {a : α} : Identity a a :=
  Identity.refl a

@[symm] noncomputable def symm₀ {α : Type 0} {a b : α} (h : Identity a b) : Identity b a :=
  h.rec .rfl₀

@[symm] noncomputable def symm₁ {α : Type 1} {a b : α} (h : Identity a b) : Identity b a :=
  h.rec .rfl₁

noncomputable def trans₀ {α : Type 0} {a b c : α} (h₁ : Identity a b) (h₂ : Identity b c) :
    Identity a c :=
  h₂.rec h₁

noncomputable def trans₁ {α : Type 1} {a b c : α} (h₁ : Identity a b) (h₂ : Identity b c) :
    Identity a c :=
  h₂.rec h₁

end Identity

-- Rudimentary support for `sorry`.
axiom sorryAx₀ (A : Type 0) : A
axiom sorryAx₁ (A : Type 1) : A
axiom sorryAx₂ (A : Type 2) : A
