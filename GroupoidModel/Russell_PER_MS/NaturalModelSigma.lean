import GroupoidModel.Russell_PER_MS.NaturalModelBase

universe v u

noncomputable section
open CategoryTheory Limits NaturalModelBase

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

/-- This is a specialization of `UvPoly.equiv`.
  We want to use the chosen pullback `M.ext A`
  instead of `pullback` from the `HasPullback` instance
-/
def uvPolyTpEquiv (Γ : Ctx) (X : Psh Ctx) :
    (y(Γ) ⟶ (uvPolyTp M).functor.obj X)
    ≃ (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X) :=
  (UvPoly.equiv _ _ _).trans
  (Equiv.sigmaCongrRight (fun _ =>
    Iso.homCongr (pullbackIsoExt _ _) (Iso.refl _)))

end
