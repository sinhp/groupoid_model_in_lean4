import HoTTLean.Syntax.InversionLemmas
import HoTTLean.Model.Unstructured.Interpretation

/-! ## The internal theory of an unstructured model -/

namespace Model.UnstructuredUniverse.UHomSeq

open SynthLean
open Interpretation
open CategoryTheory ChosenTerminal

universe v u
variable {𝒞 : Type u} [Category.{v} 𝒞] [ChosenTerminal 𝒞]
variable (s : UHomSeq 𝒞)

/-- The signature of the internal theory of `s`.
It includes a name for each semantic term and each semantic type
at every universe level strictly below `univMax`. -/
inductive SigInt
  | tm {l} (llen : l < univMax) (t : 𝟭_ 𝒞 ⟶ s[l].Tm)
  | tp {l} (llen : l < univMax) (A : 𝟭_ 𝒞 ⟶ s[l].Ty)

/-- The internal theory of a model `s`.

The syntactic type of a semantic type constant is the universe it lives in.
The syntactic type of a semantic term constant is (`el` of) its semantic type as a constant. -/
def thyInt : Axioms s.SigInt
  | .tm (l := l) llen t =>
    some ⟨
      (.el (.ax (.tp llen (t ≫ s[l].tp)) (.univ l)), l),
      by simp [Expr.isClosed]; omega⟩
  | .tp (l := l) _ A =>
    some ⟨
      (.univ l, l+1),
      by simp [Expr.isClosed]; omega⟩

theorem thyInt_wf : s.thyInt.Wf :=
  fun
    | .tm (l := l) _ t, _, get => by
      simp only [thyInt, Option.some.injEq] at get
      rw [← get]
      apply WfTp.el
      apply WfTm.ax (Al := s.thyInt (.tp ‹_› (t ≫ s[l].tp)) |>.get rfl) .nil
      . simp
      . apply WfTp.univ .nil ‹_›
    | .tp .., _, get => by
      simp only [thyInt, Option.some.injEq] at get
      subst_vars
      apply WfTp.univ .nil ‹_›

/-- Interpretation of the internal signature of `s`. -/
def interpSigInt : Interpretation s.SigInt s where
  ax := fun
    | .tm (l := l) _ t, l', _ => if eq : l = l' then some (eq ▸ t) else none
    | .tp (l := l) _ A, l', _ => if eq : l+1 = l' then some (eq ▸ s.code (by omega) A) else none

variable [s.PiSeq] [s.SigSeq] [s.IdSeq]

theorem interpSigInt_wf : s.interpSigInt.Wf s.thyInt where
  ax := @fun
    | .tm _ t, _, get => by
      cases get
      simp [interpSigInt, ofType, comp_code]
      simp [nilCObj]; get_elem_tactic
    | .tp _ t, _, get => by
      cases get
      simp [interpSigInt, ofType, nilCObj]

end Model.UnstructuredUniverse.UHomSeq
