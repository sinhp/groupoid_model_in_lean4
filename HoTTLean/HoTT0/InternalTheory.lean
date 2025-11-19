import HoTTLean.Frontend.Commands
import HoTTLean.Model.Unstructured.Interpretation
import HoTTLean.Groupoids.UHom

noncomputable section

universe v u

/-! ## The internal theory of a model -/

namespace Model.UnstructuredUniverse.UHomSeq

open SynthLean
open Model UnstructuredUniverse Interpretation
open CategoryTheory ChosenTerminal

variable {𝒞 : Type u} [Category.{v} 𝒞] [ChosenTerminal 𝒞]
-- TODO: include `univMax ≤ s.length` as a field in `UHomSeq`
variable {s : UHomSeq 𝒞} (slen : univMax ≤ s.length)
  [s.PiSeq] [s.SigSeq] [s.IdSeq]

variable (s) in
/-- Axioms names in the theory of `s`. -/
inductive AxName
  | tm {l} (llen : l < univMax) (t : 𝟭_ 𝒞 ⟶ s[l].Tm)
  | tp {l} (llen : l < univMax) (A : 𝟭_ 𝒞 ⟶ s[l].Ty)

/-- Axioms in the theory of `s`. -/
def axioms : Axioms (s.AxName slen)
  | .tm (l := l) llen t =>
    some ⟨
      (.el (.ax (.tp llen (t ≫ s[l].tp)) (.univ l)), l),
      by simp [Expr.isClosed]; omega⟩
  | .tp (l := l) _ A =>
    some ⟨
      (.univ l, l+1),
      by simp [Expr.isClosed]; omega⟩

/-- Interpretation of the theory of `s`. -/
def interp : Interpretation (s.AxName slen) s where
  ax := fun
    | .tm (l := l) _ t, l', _ => if eq : l = l' then some (eq ▸ t) else none
    | .tp (l := l) _ A, l', _ => if eq : l+1 = l' then some (eq ▸ s.code (by omega) A) else none

theorem interp_wf : (s.interp slen).Wf slen (s.axioms slen) where
  ax := @fun
    | .tm _ t, _, get => by
      cases get
      simp [interp, ofType, comp_code]
      simp [nilCObj]; omega
    | .tp _ t, _, get => by
      cases get
      simp [interp, ofType, nilCObj]
