import HoTTLean.Syntax.Axioms
import HoTTLean.Typechecker.Value

/-! Structures that store deeply embedded axioms and definitions. -/

namespace SynthLean

variable {χ : Type*} {E : Axioms χ}

/-- An axiom checked with respect to the axioms in `E`. -/
structure CheckedAx (E : Axioms χ) where
  name : χ
  get_name : E name = none
  l : Nat
  tp : Expr χ
  nfTp : Val χ
  wf_nfTp : ValEqTp E [] l nfTp tp

namespace CheckedAx

theorem wf_tp (a : CheckedAx E) : E ∣ [] ⊢[a.l] a.tp :=
  a.wf_nfTp.wf_tp

variable [DecidableEq χ]

/-- The set of axioms extended by this one. -/
noncomputable abbrev snocAxioms (a : CheckedAx E) : Axioms χ :=
  E.snoc a.get_name a.wf_tp

theorem le_snocAxioms (a : CheckedAx E) : E ≤ a.snocAxioms :=
  E.le_snoc_self ..

theorem wf_snocAxioms (a : CheckedAx E) (Ewf : E.Wf) : a.snocAxioms.Wf :=
  Ewf.snoc a.get_name a.wf_tp

/-- The axiom as a term. -/
def val (a : CheckedAx E) : Expr χ :=
  .ax a.name a.tp

theorem wf_val (a : CheckedAx E) : a.snocAxioms ∣ [] ⊢[a.l] a.val : a.tp := by
  unfold val
  apply WfTm.ax .nil (E.snoc_get ..)
  apply a.wf_nfTp.wf_tp.of_axioms_le a.le_snocAxioms

end CheckedAx

/-- A definition checked with respect to the axioms in `E`. -/
structure CheckedDef (E : Axioms χ) where
  l : Nat
  tp : Expr χ
  nfTp : Val χ
  wf_nfTp : ValEqTp E [] l nfTp tp
  val : Expr χ
  -- nfVal?
  wf_val : E ∣ [] ⊢[l] val : tp

namespace CheckedDef

theorem wf_tp (d : CheckedDef E) : E ∣ [] ⊢[d.l] d.tp :=
  d.wf_val.wf_tp

end CheckedDef
end SynthLean
