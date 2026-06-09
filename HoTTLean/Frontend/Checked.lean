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

/-- The set of axioms extended by this one. -/
noncomputable def snocAxioms (a : CheckedAx E) : Axioms χ :=
  E.snoc a.l a.name a.tp a.wf_tp.le_univMax a.wf_tp.isClosed

theorem le_snocAxioms (a : CheckedAx E) : E ≤ a.snocAxioms :=
  E.le_snoc_self _ _ _ _ _ a.get_name

theorem wf_snocAxioms (a : CheckedAx E) (Ewf : E.Wf) : a.snocAxioms.Wf :=
  Ewf.snoc a.name a.wf_tp a.get_name

/-- The axiom as a term. -/
def val (a : CheckedAx E) : Expr χ :=
  .ax a.name a.tp

theorem wf_val (a : CheckedAx E) : a.snocAxioms ∣ [] ⊢[a.l] a.val : a.tp := by
  unfold val
  have := E.snoc_get a.l a.name a.tp a.wf_tp.le_univMax a.wf_tp.isClosed
  apply WfTm.ax .nil this
  apply a.wf_nfTp.wf_tp.of_axioms_le a.le_snocAxioms

end CheckedAx

/-- A definition checked with respect to the axioms in `E`. -/
structure CheckedDef (E : Axioms χ) where
  l : Nat
  tp : Expr χ
  nfTp : Val χ
  wf_nfTp : ValEqTp E [] l nfTp tp
  val : Expr χ
  /-- Cached value of `val`. Used by the `evalTm` fast path so that references
  to this def don't have to re-evaluate the body. -/
  nfVal : Val χ
  wf_nfVal : ValEqTm E [] l nfVal val tp
  wf_val : E ∣ [] ⊢[l] val : tp

namespace CheckedDef

theorem wf_tp (d : CheckedDef E) : E ∣ [] ⊢[d.l] d.tp :=
  d.wf_val.wf_tp

/-- The cached `nfTp` lifted from empty context (in `E`) to any well-formed context
in a possibly-larger axiom environment `E'`. The def's type is closed, so substitution
does not change it. -/
theorem wf_nfTp_lift_le {E E' : Axioms χ} (d : CheckedDef E) (le : E ≤ E')
    {Γ} (wfΓ : WfCtx E' Γ) : ValEqTp E' Γ d.l d.nfTp d.tp := by
  have h := d.wf_nfTp.of_axioms_le le
  induction Γ with
  | nil => exact h
  | cons head tail ih =>
    have hd : E' ∣ tail ⊢[head.2] head.1 := wfΓ.inv_snoc
    have lifted := (ih hd.wf_ctx).wk hd
    rwa [Expr.subst_of_isClosed _ d.wf_tp.isClosed] at lifted

/-- The cached `nfVal` lifted from empty context (in `E`) to any well-formed context
in a possibly-larger axiom environment `E'`. Both the def's body and type are closed,
so substitution does not change them. -/
theorem wf_nfVal_lift_le {E E' : Axioms χ} (d : CheckedDef E) (le : E ≤ E')
    {Γ} (wfΓ : WfCtx E' Γ) : ValEqTm E' Γ d.l d.nfVal d.val d.tp := by
  have h := d.wf_nfVal.of_axioms_le le
  induction Γ with
  | nil => exact h
  | cons head tail ih =>
    have hd : E' ∣ tail ⊢[head.2] head.1 := wfΓ.inv_snoc
    have lifted := (ih hd.wf_ctx).wk hd
    rwa [Expr.subst_of_isClosed _ d.wf_val.isClosed,
         Expr.subst_of_isClosed _ d.wf_tp.isClosed] at lifted

/-- The def's body, well-typed in any well-formed context in a possibly-larger
axiom environment. Closed; substitution leaves it unchanged. -/
theorem wf_val_lift_le {E E' : Axioms χ} (d : CheckedDef E) (le : E ≤ E')
    {Γ} (wfΓ : WfCtx E' Γ) : E' ∣ Γ ⊢[d.l] d.val : d.tp := by
  have h := d.wf_val.of_axioms_le le
  induction Γ with
  | nil => exact h
  | cons head tail ih =>
    have hd : E' ∣ tail ⊢[head.2] head.1 := wfΓ.inv_snoc
    have lifted := (ih hd.wf_ctx).subst (WfSb.wk hd)
    rwa [Expr.subst_of_isClosed _ d.wf_val.isClosed,
         Expr.subst_of_isClosed _ d.wf_tp.isClosed] at lifted

end CheckedDef
end SynthLean
