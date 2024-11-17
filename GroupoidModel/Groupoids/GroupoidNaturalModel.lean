import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

import GroupoidModel.NaturalModel
import GroupoidModel.Groupoids.PullBackProofs

/-!
Here we construct the natural model for groupoids.
-/

universe u v u₁ v₁ u₂ v₂

open CategoryTheory
noncomputable section

-- Here I am using sGrpd to be a small category version of Grpd. There is likely a better way to do this.
def sGrpd := ULiftHom.{u+1} Grpd.{u,u}
  deriving SmallCategory

def sGrpd.of (C : Type u) [Groupoid.{u} C] : sGrpd.{u} := Grpd.of C

def SmallGrpd.forget : sGrpd.{u} ⥤ Grpd.{u,u} where
  obj x := Grpd.of x.α
  map f := f.down

def PshsGrpd : (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) ⥤ (sGrpd.{u}ᵒᵖ ⥤ Type (u + 1)) :=
  (whiskeringLeft _ _ _).obj SmallGrpd.forget.op

instance PshsGrpdPreservesLim : Limits.PreservesLimits PshsGrpd := by
  dsimp [PshsGrpd,Limits.PreservesLimits]
  exact whiskeringLeftPreservesLimits SmallGrpd.forget.op

instance GroupoidNM : NaturalModel.NaturalModelBase sGrpd.{u} where
  Ty := PshsGrpd.obj (PshGrpd.obj (Cat.of Grpd.{u,u}))
  Tm := PshsGrpd.obj (PshGrpd.obj (Cat.of PGrpd.{u,u}))
  tp := PshsGrpd.map (PshGrpd.map (PGrpd.forgetPoint))
  ext Γ A := by
    let Γ' : Grpd.{u,u} := SmallGrpd.forget.obj Γ
    let A' : Γ' ⥤ Grpd.{u,u} := by
      have h1 := yonedaEquiv.toFun A
      dsimp [PshsGrpd,PshGrpd,CatLift,Quiver.Hom,Cat.of,Bundled.of,Grpd.forgetToCat] at h1
      refine ?_ ⋙ h1
      exact Up_uni ↑Γ'
    exact sGrpd.of (Grpd.of (GroupoidalGrothendieck A'))
  disp Γ A := by
    constructor
    simp[ULiftHom.objDown,Quiver.Hom]
    refine Grothendieck.forget _ ⋙ ?_
    exact 𝟭 ↑(SmallGrpd.forget.obj Γ)
  var Γ A := by
    refine yonedaEquiv.invFun ?_
    simp[PshGrpd,CatLift,Cat.of,Bundled.of,Quiver.Hom,Grpd.forgetToCat,SmallGrpd.forget]
    have v' := var' _ (Up_uni (@Bundled.α Groupoid Γ) ⋙ yonedaEquiv A)
    refine ?_ ⋙ v'
    exact Down_uni (GroupoidalGrothendieck (Up_uni (@Bundled.α Groupoid Γ) ⋙ yonedaEquiv A))
  disp_pullback A := by
    rename_i Γ
    let Γ' : Grpd.{u,u} := SmallGrpd.forget.obj Γ
    let A' : Γ' ⥤ Grpd.{u,u} := by
      have h1 := yonedaEquiv.toFun A
      dsimp [PshsGrpd,PshGrpd,CatLift,Quiver.Hom,Cat.of,Bundled.of,Grpd.forgetToCat] at h1
      refine ?_ ⋙ h1
      exact Up_uni ↑Γ'
    have pb := Functor.map_isPullback PshsGrpd (PshGrpdPB A')
    dsimp [PshGrpd]
    dsimp [PshGrpd] at pb
    sorry

instance groupoidULift.{u'} {α : Type u} [Groupoid.{v} α] : Groupoid (ULift.{u'} α) where
  inv f := Groupoid.inv f
  inv_comp _ := Groupoid.inv_comp ..
  comp_inv _ := Groupoid.comp_inv ..

instance groupoidULiftHom.{u'} {α : Type u} [Groupoid.{v} α] : Groupoid (ULiftHom.{u'} α) where
  inv f := .up (Groupoid.inv f.down)
  inv_comp _ := ULift.ext _ _ <| Groupoid.inv_comp ..
  comp_inv _ := ULift.ext _ _ <| Groupoid.comp_inv ..

inductive Groupoid2 : Type (u+2) where
  | small (_ : sGrpd.{u})
  | large (_ : sGrpd.{u+1})

def Groupoid2.toLarge : Groupoid2.{u} → sGrpd.{u+1}
  | .small A => .mk (ULiftHom.{u+1} (ULift.{u+1} A.α))
  | .large A => A

/-- A model of Grpd with an internal universe, with the property that the small universe
injects into the large one. -/
def Grpd2 : Type (u+2) := InducedCategory sGrpd.{u+1} Groupoid2.toLarge
  deriving SmallCategory

section NaturalModelSigma

def PolyDataGet (Γ : sGrpdᵒᵖ) (Q : ((NaturalModel.P NaturalModel.tp).obj NaturalModel.Ty).obj Γ) :
    yoneda.obj (Opposite.unop Γ) ⟶ ((NaturalModel.P NaturalModel.tp).obj NaturalModel.Ty) := by
  apply yonedaEquiv.invFun
  exact Q

instance GroupoidNMSigma : NaturalModel.NaturalModelSigma sGrpd.{u} where
  Sig := by
    fconstructor
    . intro Γ Q
      have φ' := PolyDataGet Γ Q
      have pp := (NaturalModel.uvPoly NaturalModel.tp).polyPair φ'
      rcases pp with ⟨A,pb⟩
      let dp := NaturalModel.disp_pullback A
      let help : yoneda.obj (NaturalModel.ext (Opposite.unop Γ) A) ≅
                 (Limits.pullback A NaturalModel.tp) := by
        exact CategoryTheory.IsPullback.isoPullback (CategoryTheory.IsPullback.flip dp)
      let h' := (help.hom.app Γ)
      let pb' := pb.app Γ
      dsimp [NaturalModel.Ty,PshsGrpd,PshGrpd,Quiver.Hom]
      fconstructor
      . fconstructor
        . intro γ
          let yA := (yonedaEquiv.toFun A)
          dsimp [NaturalModel.Ty,PshGrpd,PshsGrpd,Quiver.Hom] at yA
          let Aγ : Grpd := (yA).obj γ
          let ΓA : Grpd := SmallGrpd.forget.obj (NaturalModel.ext (Opposite.unop Γ) A)
          sorry
        . sorry
      dsimp [NaturalModel.uvPoly] at pb'
      let diag := h' ≫ pb'
      sorry
      sorry
    . sorry
  pair := by
    sorry
  Sig_pullback := by
    sorry


end NaturalModelSigma
