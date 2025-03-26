import GroupoidModel.Russell_PER_MS.NaturalModelBase

-- TODO(WN): reorg this module
universe v u

noncomputable section
open CategoryTheory Limits NaturalModelBase

namespace NaturalModelBase
variable {Ctx : Type u}
  [SmallCategory Ctx] (M : NaturalModelBase Ctx)

structure NaturalModelPi where
  Pi : M.Ptp.obj M.Ty ⟶ M.Ty
  lam : M.Ptp.obj M.Tm ⟶ M.Tm
  Pi_pullback : IsPullback lam (M.Ptp.map M.tp) M.tp Pi

class NaturalModelSigma where
  Sig : M.Ptp.obj M.Ty ⟶ M.Ty
  pair : UvPoly.compDom (uvPolyTp M) (uvPolyTp M) ⟶ M.Tm
  Sig_pullback : IsPullback pair ((uvPolyTp M).comp (uvPolyTp M)).p M.tp Sig

-- The use of `IsPullback.flip` suggests an inconsistency in convention.
def pullbackIsoExt {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) :
  pullback A M.uvPolyTp.p ≅ yoneda.obj (M.ext A) :=
  (IsPullback.isoPullback (IsPullback.flip (M.disp_pullback A))).symm

/-- This is a specialization of `UvPoly.equiv`
  the universal property of `UvPoly` to `M.uvPolyTp`.
  We use the chosen pullback `M.ext A`
  instead of `pullback` from the `HasPullback` instance -/
def uvPolyTpEquiv {Γ : Ctx} {X : Psh Ctx} :
    (y(Γ) ⟶ M.uvPolyTp.functor.obj X)
    ≃ (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X) :=
  (UvPoly.equiv _ _ _).trans
  (Equiv.sigmaCongrRight (fun _ =>
    Iso.homCongr (pullbackIsoExt _ _) (Iso.refl _)))

@[simp] theorem uvPolyTpEquiv_fst {Γ : Ctx} {X : Psh Ctx}
    (AB : y(Γ) ⟶ M.uvPolyTp.functor.obj X) :
    (M.uvPolyTpEquiv AB).1 = AB ≫ M.uvPolyTp.fstProj _ :=
  rfl

@[simp] theorem uvPolyTpEquiv_symm_snd {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    eqToHom (by simp) ≫ (M.uvPolyTpEquiv (M.uvPolyTpEquiv.symm ⟨A, B⟩)).snd = B := by
  apply eq_of_heq
  rw [eqToHom_comp_heq_iff]
  have h1 : M.uvPolyTpEquiv (M.uvPolyTpEquiv.symm ⟨A, B⟩) = ⟨A, B⟩ := by simp
  exact (Sigma.mk.inj_iff.mp ((Sigma.eta _).trans h1)).2

theorem uvPolyTpEquiv_symm {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    M.uvPolyTpEquiv.symm ⟨ A, B ⟩ =
    M.uvPolyTp.lift A ((pullbackIsoExt _ _).hom ≫ B) :=
  rfl

@[simp] theorem uvPolyTpEquiv_symm_proj
    {Γ : Ctx} {X : Psh Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X):
    M.uvPolyTpEquiv.symm ⟨A, B⟩ ≫ M.uvPolyTp.fstProj _ = A := by
  simp [uvPolyTpEquiv_symm]

/-- `sec` is the universal lift in the following diagram,
  which is a section of `Groupoidal.forget`

  ===== Γ -------α--------------¬
 ‖      ↓ sec                   V
 ‖   M.ext A ⋯ -------------> M.Tm
 ‖      |                        |
 ‖      |                        |
 ‖   forget                    M.tp
 ‖      |                        |
 ‖      V                        V
  ===== Γ ---- α ≫ M.tp -----> M.Ty
-/
-- TODO(WN): move to `NaturalModel`
def sec {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) :
    y(Γ) ⟶ y(M.ext (α ≫ M.tp)) :=
  (M.disp_pullback (α ≫ M.tp)).lift α (𝟙 y(Γ)) rfl

@[simp] theorem sec_var {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) :
    M.sec α ≫ M.var (α ≫ M.tp) = α :=
  (M.disp_pullback (α ≫ M.tp)).lift_fst _ _ _

@[simp] theorem sec_disp {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) :
    M.sec α ≫ ym(M.disp (α ≫ M.tp)) = 𝟙 _ :=
  (M.disp_pullback (α ≫ M.tp)).lift_snd _ _ _

theorem lift_ev {Γ : Ctx} {AB : y(Γ) ⟶ M.uvPolyTp.functor.obj M.Ty}
    {α : y(Γ) ⟶ M.Tm} (hA : AB ≫ M.uvPolyTp.fstProj M.Ty = α ≫ M.tp)
    : pullback.lift AB α hA ≫ (UvPoly.PartialProduct.fan M.uvPolyTp M.Ty).snd
    = M.sec α ≫ eqToHom (by rw [← hA]; rfl) ≫ (M.uvPolyTpEquiv AB).2 :=
  sorry

/-- A specialization of the universal property of `UvPoly.compDom` to `M.uvPolyTp`,
  using the chosen pullback `M.ext` instead of `pullback`. -/
def uvPolyTpCompDomEquiv (Γ : Ctx) :
    (y(Γ) ⟶ M.uvPolyTp.compDom M.uvPolyTp)
    ≃ (α : y(Γ) ⟶ M.Tm)
    × (B : y(M.ext (α ≫ M.tp)) ⟶ M.Ty)
    × (β : y(Γ) ⟶ M.Tm)
    ×' β ≫ M.tp = M.sec α ≫ B :=
  calc
    _ ≃ _ := UvPoly.compDomEquiv
    _ ≃ _ := {
      toFun x := match x with
      | ⟨ AB, α, β, hA, hB ⟩ => ⟨ α,
        ⟨ eqToHom (by dsimp only [uvPolyTp] at hA; rw [← hA]; rfl)
        ≫ (M.uvPolyTpEquiv AB).2 , β , hB.trans (M.lift_ev hA) ⟩⟩
      invFun x := match x with
      | ⟨ α, B, β, h ⟩ => ⟨ M.uvPolyTpEquiv.symm ⟨ α ≫ M.tp, B ⟩, α, β, by
        fconstructor
        · simp [uvPolyTp_p, uvPolyTpEquiv_symm_proj]
        · refine h.trans ?_
          rw [M.lift_ev]
          congr 1
          rw [uvPolyTpEquiv_symm_snd] ⟩
      left_inv x := match x with
      | ⟨ AB, α, β, hA, hB ⟩ => by
        congr!
        dsimp only [uvPolyTpEquiv_fst]
        rw [Equiv.symm_apply_eq]
        refine Eq.trans ?_ (Sigma.eta _)
        ext
        · rw [M.uvPolyTpEquiv_fst, NatTrans.congr_app hA]
          simp
        · simp
      right_inv x := match x with
      | ⟨ α, B, β, h ⟩ => by
        congr!
        rw [uvPolyTpEquiv_symm_snd] }

end NaturalModelBase
end
