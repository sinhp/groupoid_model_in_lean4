import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import GroupoidModel.Tarski.NaturalModel
import GroupoidModel.Grothendieck.Pullback
import GroupoidModel.Grothendieck.Groupoidal


/-!
Here we construct the natural model for groupoids.

TODO: This file needs to eventually be ported to GroupoidRussellNaturalModel
but currently we don't have a Russell style sigma type.
-/

universe u v u₁ v₁ u₂ v₂

open CategoryTheory ULift

noncomputable section

/-
Grpd.{u, u} is
the category of
{small groupoids - size u objects and size u hom sets}
which itself has size u+1 objects (small groupoids)
and size u hom sets (functors).
We want this to be a small category so we lift the homs.
-/
def sGrpd := ULiftHom.{u+1} Grpd.{u,u}
  deriving SmallCategory

def sGrpd.of (C : Type u) [Groupoid.{u} C] : sGrpd.{u} := Grpd.of C

def CatLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
    obj x := Cat.of (ULift.{u + 1, u} x)
    map {x y} f := downFunctor ⋙ f ⋙ upFunctor

@[simp] def sGrpd.forget : sGrpd.{u} ⥤ Grpd.{u,u} := ULiftHom.down

variable (C D) [Category.{u} C] [Category.{u} D]

def ι : Grpd.{u, u} ⥤ Cat.{u,u+1} := Grpd.forgetToCat ⋙ CatLift

def PshGrpdOfCat : Cat.{u,u+1} ⥤ (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj ι.op

def PshsGrpdOfPshGrpd : (Grpd.{u,u}ᵒᵖ ⥤ Type (u + 1)) ⥤ (sGrpd.{u}ᵒᵖ ⥤ Type (u + 1)) :=
  (whiskeringLeft _ _ _).obj sGrpd.forget.op

abbrev yonedaCat : Cat.{u, u+1} ⥤ Psh sGrpd.{u} :=
  PshGrpdOfCat ⋙ PshsGrpdOfPshGrpd

section

variable {Γ Δ : sGrpd.{u}}
  {C D : Type (u+1)} [Category.{u,u+1} C][Category.{u,u+1} D]

/- The bijection y(Γ) → [-,C]   ≃   Γ ⥤ C -/
@[simp] def yonedaCatEquiv :
  (yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C))
  ≃ (sGrpd.forget.obj Γ) ⥤ C :=
  Equiv.trans yonedaEquiv
    {toFun     := λ A ↦ ULift.upFunctor ⋙ A
     invFun    := λ A ↦ ULift.downFunctor ⋙ A
     left_inv  := λ _ ↦ rfl
     right_inv := λ _ ↦ rfl}

theorem yonedaCatEquiv_naturality
  (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C)) (σ : Δ ⟶ Γ) :
  (sGrpd.forget.map σ) ⋙ yonedaCatEquiv A
    = yonedaCatEquiv (yoneda.map σ ≫ A) := by
  simp[← yonedaEquiv_naturality]
  rfl

theorem yonedaCatEquiv_comp
  (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of D)) (U : D ⥤ C) :
  yonedaCatEquiv (A ≫ yonedaCat.map U) = yonedaCatEquiv A ⋙ U := by
  aesop_cat


abbrev Ty : Psh sGrpd.{u} := yonedaCat.obj (Cat.of Grpd.{u,u})

abbrev Tm : Psh sGrpd.{u} := yonedaCat.obj (Cat.of PGrpd.{u,u})

variable {Γ : sGrpd.{u}} (A : yoneda.obj Γ ⟶ Ty)

abbrev tp : Tm ⟶ Ty := yonedaCat.map (PGrpd.forgetToGrpd)

abbrev ext : Grpd.{u,u} := Grpd.of (GroupoidalGrothendieck (yonedaCatEquiv A))

abbrev downDisp : ext A ⟶ (Γ : Grpd.{u,u}) := Grothendieck.forget _

abbrev disp : @Quiver.Hom sGrpd _ (ext A) Γ := { down := downDisp A }

abbrev var : (yoneda.obj (ext A) : Psh sGrpd) ⟶ Tm :=
  yonedaCatEquiv.invFun (sorry)

theorem disp_pullback :
    IsPullback (var A) (yoneda.map { down := downDisp A }) tp A := sorry

-- PLAN

-- show that yonedaCat preserves IsPullback
-- show that yoneda : sGrpd ⥤ Psh sGrpd factors through yonedaCat (up to a natural iso)
-- show that desired pullback is two squares (the natural iso and the image of the grothendieck pullback in Cat under yonedaCat)
-- prove the grothendieck pullback is a pullback

instance GroupoidNM : NaturalModel.NaturalModelBase sGrpd.{u} where
  Ty := Ty
  Tm := Tm
  tp := tp
  ext Γ A := sGrpd.of (ext A)
  disp Γ A := disp A
  var Γ A := var A
  disp_pullback A := disp_pullback A

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

def GetPoint {Γ : Grpd} (x : Γ) : Unit ⥤ Γ where
  obj _ := x
  map _ := 𝟙 x

instance GU : Groupoid Unit where
  inv _ := 𝟙 _
  inv_comp _ := rfl
  comp_inv _ := rfl

def PointToFiber {Γ : Grpd} (A : Γ ⥤ Grpd) (x : Γ) : (A.obj x) ⥤ GroupoidalGrothendieck A where
  obj a := by
    fconstructor
    . exact x
    . exact a
  map f := by
    dsimp
    fconstructor
    . exact 𝟙 x
    . rename_i X Y
      dsimp [Grpd.forgetToCat]
      let h : X = (A.map (𝟙 x)).obj X := by
        simp[CategoryStruct.id]
      refine eqToHom h.symm ≫ ?_
      exact f
  map_comp f g := by
    simp[CategoryStruct.comp,Grothendieck.comp]
    fapply Grothendieck.ext
    . simp
    . simp [Grpd.forgetToCat,eqToHom_map]
      rename_i X Y Z
      let h : A.map (𝟙 x) = 𝟙 (A.obj x) := by
        simp
      let h' : X = (A.map (𝟙 x ≫ 𝟙 x)).obj X := by
        simp[CategoryStruct.id]
      simp [<- Category.assoc]
      refine (congrFun (congrArg CategoryStruct.comp ?_) g)
      simp [Category.assoc]
      have ee : Epi (eqToHom h') := by
        exact IsIso.epi_of_iso (eqToHom h')
      apply ee.left_cancellation
      simp
      refine @IsHomLift.fac _ _ _ _ _ _ _ _ _ f f ?_
      constructor; simp; constructor

def GNT {Γ : Grpd} (A : Γ ⥤ Grpd) (X Y : Γ) (f : X ⟶ Y) : PointToFiber A X ⟶ ((A.map f) ⋙ (PointToFiber A Y)) where
  app x := by
    fconstructor
    . simp[PointToFiber]
      exact f
    . simp [Grpd.forgetToCat,PointToFiber]
      exact 𝟙 ((A.map f).obj x)
  naturality X Y f := by
    simp[PointToFiber,CategoryStruct.comp,Grothendieck.comp]
    fapply Grothendieck.ext
    . simp
    . simp[Grpd.forgetToCat, eqToHom_map]


def GroupoidSigma {Γ : Grpd} (A : Γ ⥤ Grpd) (B : (GroupoidalGrothendieck A) ⥤ Grpd) : Γ ⥤ Grpd where
  obj x := Grpd.of (GroupoidalGrothendieck ((PointToFiber A x) ⋙ B))
  map f := by
    rename_i X Y
    have NT' : (PointToFiber A X) ⋙ (B ⋙ Grpd.forgetToCat) ⟶ (A.map f ⋙ PointToFiber A Y) ⋙ (B ⋙ Grpd.forgetToCat) := whiskerRight (GNT A X Y f) (B ⋙ Grpd.forgetToCat)
    exact (Grothendieck.map NT') ⋙ (GroupoidalGrothendieck.functorial (A.map f) (PointToFiber A Y ⋙ B))
  map_id := by
    intro X
    simp[CategoryStruct.id,whiskerRight,Functor.id]
    refine CategoryTheory.Functor.ext ?_ ?_
    all_goals sorry
  map_comp := by
    intro X Y Z f g
    simp[Grpd.forgetToCat]
    sorry


theorem GroupoidSigmaBeckChevalley (Δ Γ: Grpd) (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd)
  (B : (GroupoidalGrothendieck A) ⥤ Grpd) : σ ⋙ GroupoidSigma A B = GroupoidSigma (σ ⋙ A)
  (GroupoidalGrothendieck.Map Δ Γ σ A B) := sorry

instance GroupoidNMSigma : NaturalModel.NaturalModelSigma sGrpd.{u} where
  Sig := by
    fconstructor
    . intro Γ Q
      have φ' := PolyDataGet Γ Q
      have pp := (NaturalModel.uvPoly (Ctx := sGrpd.{u}) NaturalModel.tp).polyPair φ'
      rcases pp with ⟨A,pb⟩
      let dp := NaturalModel.disp_pullback A
      let help : yoneda.obj (NaturalModel.ext (Opposite.unop Γ) A) ≅
                 (Limits.pullback A NaturalModel.tp) := by
        exact CategoryTheory.IsPullback.isoPullback (CategoryTheory.IsPullback.flip dp)
      let h' := (help.hom.app Γ)
      let pb' := pb.app Γ
      dsimp [NaturalModel.Ty,PshsGrpdOfPshGrpd,PshGrpdOfCat,Quiver.Hom]
      fconstructor
      . fconstructor
        . intro γ
          let yA := (yonedaEquiv.toFun A)
          dsimp [NaturalModel.Ty,PshGrpdOfCat,PshsGrpdOfPshGrpd,Quiver.Hom] at yA
          let Aγ : Grpd := (yA).obj γ
          let ΓA : Grpd := sGrpd.forget.obj (NaturalModel.ext (Opposite.unop Γ) A)
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
