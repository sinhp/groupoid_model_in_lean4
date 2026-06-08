import HoTTLean.Frontend.Commands

noncomputable section

/-! ## Theory -/

declare_theory unitt

namespace UniTT

unitt axiom funext {α : Type} {β : α → Type} (f g : (a : α) → β a) :
  (∀ a, Identity (f a) (g a)) → Identity f g

unitt axiom Unit : Type
unitt axiom u : Unit
unitt axiom uniq_u (u' : Unit) : Identity u' u

unitt #print u -- Prints `axiom u : Unit`
#print u -- Prints `def u : CheckedAx (Axioms.empty.snoc Unit) := …`

unitt def uniq_fn {A : Type} (f g : A → Unit) : Identity f g := by
  apply funext; intro; exact (uniq_u _).trans₀ (uniq_u _).symm₀

/-! ## Interpretation

The old semantic interpretation smoke test in this file referred to modules that no longer exist
(`HoTTLean.Model.Interpretation` and `HoTTLean.Groupoids.NaturalModelBase`).  The current model
API is exercised by the main `HoTTLean` build; this file remains a frontend/theory smoke test for
unit types until a replacement semantic test is written against the current model API.
-/

end UniTT
