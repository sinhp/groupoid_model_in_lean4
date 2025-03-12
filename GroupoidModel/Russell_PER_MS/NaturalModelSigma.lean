import GroupoidModel.Russell_PER_MS.NaturalModelBase

-- TODO(WN): reorg this module
universe v u

noncomputable section
open CategoryTheory Limits NaturalModelBase

namespace NaturalModelBase
variable {Ctx : Type u} [Category.{v, u} Ctx] (M : NaturalModelBase Ctx)
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
def uvPolyTpEquiv (Γ : Ctx) (X : Psh Ctx) :
    (y(Γ) ⟶ M.uvPolyTp.functor.obj X)
    ≃ (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X) :=
  (UvPoly.equiv _ _ _).trans
  (Equiv.sigmaCongrRight (fun _ =>
    Iso.homCongr (pullbackIsoExt _ _) (Iso.refl _)))

/-- A specialization of the universal property of `genPb` to `M.uvPolyTp`,
  using the chosen pullback `M.ext` instead of `pullback`. -/
def genPbEquiv (Γ : Ctx) (X : Psh Ctx) :
    (y(Γ) ⟶ M.uvPolyTp.genPb X)
    ≃ (α : y(Γ) ⟶ M.Tm)
    × (y(M.ext (α ≫ M.tp)) ⟶ M.Ty) :=
  sorry

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
    Γ ⟶ M.ext (α ≫ M.tp) := sorry

/-- A specialization of the universal property of `UvPoly.compDom` to `M.uvPolyTp`,
  using the chosen pullback `M.ext` instead of `pullback`. -/
def uvPolyTpCompDomEquiv (Γ : Ctx) :
    (y(Γ) ⟶ M.uvPolyTp.compDom M.uvPolyTp)
    ≃ (α : y(Γ) ⟶ M.Tm)
    × (β : y(Γ) ⟶ M.Tm)
    × (B : y(M.ext (α ≫ M.tp)) ⟶ M.Ty)
    ×' β ≫ M.tp = ym(M.sec α) ≫ B :=
  sorry

end NaturalModelBase
end
