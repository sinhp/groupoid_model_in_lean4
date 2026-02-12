import HoTTLean.Syntax.Axioms
import HoTTLean.Typechecker.Value

/-! Structures that store deeply embedded axioms and definitions. -/

namespace SynthLean

variable {χ : Type*} {𝕋 : Axioms χ}

/-- An axiom checked with respect to the theory `𝕋`. -/
structure ReflectedAx (𝕋 : Axioms χ) where
  name : χ
  get_name : 𝕋 name = none
  l : Nat
  tp : Expr χ
  nfTp : Val χ
  wf_nfTp : ValEqTp 𝕋 [] l nfTp tp

namespace ReflectedAx

theorem wf_tp (a : ReflectedAx 𝕋) : 𝕋 ∣ [] ⊢[a.l] a.tp :=
  a.wf_nfTp.wf_tp

variable [DecidableEq χ]

/-- The theory that `a` depends on, extended by `a`. -/
noncomputable abbrev snocAxioms (a : ReflectedAx 𝕋) : Axioms χ :=
  𝕋.snoc a.get_name a.wf_tp

theorem le_snocAxioms (a : ReflectedAx 𝕋) : 𝕋 ≤ a.snocAxioms :=
  𝕋.le_snoc_self ..

theorem wf_snocAxioms (a : ReflectedAx 𝕋) (𝕋wf : 𝕋.Wf) : a.snocAxioms.Wf :=
  𝕋wf.snoc a.get_name a.wf_tp

/-- The axiom as a term. -/
def val (a : ReflectedAx 𝕋) : Expr χ :=
  .ax a.name a.tp

theorem wf_val (a : ReflectedAx 𝕋) : a.snocAxioms ∣ [] ⊢[a.l] a.val : a.tp := by
  unfold val
  apply WfTm.ax .nil (𝕋.snoc_get ..)
  apply a.wf_nfTp.wf_tp.of_axioms_le a.le_snocAxioms

end ReflectedAx

/-- A definition checked with respect to the theory `𝕋`. -/
structure ReflectedDef (𝕋 : Axioms χ) where
  l : Nat
  tp : Expr χ
  nfTp : Val χ
  wf_nfTp : ValEqTp 𝕋 [] l nfTp tp
  val : Expr χ
  -- nfVal?
  wf_val : 𝕋 ∣ [] ⊢[l] val : tp

namespace ReflectedDef

theorem wf_tp (d : ReflectedDef 𝕋) : 𝕋 ∣ [] ⊢[d.l] d.tp :=
  d.wf_val.wf_tp

end ReflectedDef

end SynthLean
