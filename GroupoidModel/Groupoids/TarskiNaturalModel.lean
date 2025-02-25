import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import GroupoidModel.Tarski.NaturalModel
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal
import Poly.LCCC.Basic
import Poly.LCCC.Presheaf
import Poly.Exponentiable
import Poly.Polynomial


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

def sGrpd.remember : Grpd.{u,u} ⥤ sGrpd.{u} := ULiftHom.up

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

abbrev ext : Grpd.{u,u} := Grpd.of (Grothendieck.Groupoidal (yonedaCatEquiv A))

abbrev downDisp : ext A ⟶ (Γ : Grpd.{u,u}) := Grothendieck.forget _

abbrev disp : @Quiver.Hom sGrpd _ (ext A) Γ := { down := downDisp A }

abbrev var : (yoneda.obj (ext A) : Psh sGrpd) ⟶ Tm :=
  yonedaCatEquiv.invFun (sorry)

theorem disp_pullback :
    IsPullback (var A) (yoneda.map { down := downDisp A }) tp A := sorry

end



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

def PointToFiber {Γ : Grpd} (A : Γ ⥤ Grpd) (x : Γ) : (A.obj x) ⥤ Grothendieck.Groupoidal A where
  obj a := { base := x, fiber := a }
  map f := by
    fconstructor
    . exact 𝟙 x
    . rename_i X Y
      dsimp [Grpd.forgetToCat]
      let h : X = (A.map (𝟙 x)).obj X := by
        simp[CategoryStruct.id]
      refine eqToHom h.symm ≫ ?_
      exact f
  map_comp f g := by
    fapply Grothendieck.ext
    . simp
    . simp [Grpd.forgetToCat,eqToHom_map]
      rename_i X Y Z
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

def GroupoidSigma (Γ : Grpd) (A : Γ ⥤ Grpd) (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : Γ ⥤ Grpd where
  obj x := Grpd.of (Grothendieck.Groupoidal ((PointToFiber A x) ⋙ B))
  map f := by
    rename_i X Y
    have NT' : (PointToFiber A X) ⋙ (B ⋙ Grpd.forgetToCat) ⟶ (A.map f ⋙ PointToFiber A Y) ⋙ (B ⋙ Grpd.forgetToCat) := whiskerRight (GNT A X Y f) (B ⋙ Grpd.forgetToCat)
    exact (Grothendieck.map NT') ⋙ (Grothendieck.Groupoidal.functorial (A.map f) (PointToFiber A Y ⋙ B))
  map_id := by
    intro X
    simp[CategoryStruct.id,whiskerRight,Functor.id]
    refine CategoryTheory.Functor.ext ?_ ?_
    . intro X
      simp[PointToFiber,Grpd.forgetToCat]
      sorry
    all_goals sorry
  map_comp := by
    intro X Y Z f g
    simp[Grpd.forgetToCat]
    sorry

#check sGrpd

def SGroupoidSigma (Γ : sGrpd) (A : (sGrpd.forget.obj Γ) ⥤ sGrpd) (B : (Grothendieck.Groupoidal (A ⋙ sGrpd.forget)) ⥤ sGrpd)
 : (sGrpd.forget.obj Γ) ⥤ sGrpd :=
   GroupoidSigma (sGrpd.forget.obj Γ) (A ⋙ sGrpd.forget) (B ⋙ sGrpd.forget) ⋙ sGrpd.remember

def ULiftElim.{q,r} (F : C ⥤ D) : ULift.{q, r} C ⥤ D where
  obj x := F.obj x.down
  map f := F.map f
  map_id := by
    intro x
    simp[CategoryStruct.id]
  map_comp := by
    intro x y z f g
    simp[CategoryStruct.comp]

def ULiftElim'.{q,r} (F : ULift.{q, r} C ⥤ D) :  C ⥤ D where
  obj x := (F.obj {down := x})
  map f := F.map f
  map_id := by
    intro x
    let h := F.map_id {down := x}
    simp[h,CategoryStruct.id]
    aesop_cat
  map_comp := by
    intro x y z f g
    let h := F.map_comp f g
    simp[CategoryStruct.comp]
    aesop_cat

def uv_tp : UvPoly Tm Ty where
  p := tp

def P := uv_tp.functor

#check UvPoly.equiv uv_tp
#check yonedaEquiv.invFun
#check sGrpd.forget

def Sugma : (P.obj Ty) ⟶ Ty := by
  fconstructor
  . dsimp [Quiver.Hom]
    intros sObj poly
    let poly_as_pair := UvPoly.equiv uv_tp (yoneda.obj (Opposite.unop sObj)) Ty (yonedaEquiv.invFun poly)
    rcases poly_as_pair with ⟨A', B'⟩
    let A := yonedaEquiv.toFun A'
    dsimp [PshsGrpdOfPshGrpd,PshGrpdOfCat,Quiver.Hom,ι,Grpd.forgetToCat,Cat.of,Bundled.of]
    unfold CatLift
    dsimp[ULiftHom.objDown]
    refine ULiftElim _ _ ?_
    refine GroupoidSigma ?_ ?_ ?_
    . dsimp [Ty] at A
      dsimp [PshsGrpdOfPshGrpd,PshGrpdOfCat,Quiver.Hom,ι,Grpd.forgetToCat,Cat.of,Bundled.of] at A
      unfold CatLift at A
      dsimp[ULiftHom.objDown] at A
      let A := ULiftElim' A






    let inter : ι.obj (ULiftHom.objDown (Opposite.unop sObj)) ⥤ sGrpd.forget.obj (Opposite.unop sObj) := by
      dsimp[ι,Grpd.forgetToCat,Bundled.α,Cat.of,Bundled.of]
      unfold CatLift
      simp[ULiftHom.objDown]
      exact downFunctor
    refine inter ⋙ ?_
    simp
    have T := GroupoidSigma (ULiftHom.objDown (Opposite.unop sObj)) ?_ ?_
    refine ?_ ⋙ T ⋙ ?_
    . exact 𝟭 ↑(ULiftHom.objDown (Opposite.unop sObj))
    . sorry -- This should just be id but there are universe problems
    . dsimp [Ty,PshsGrpdOfPshGrpd,PshGrpdOfCat,Quiver.Hom] at A
      refine ?_ ⋙ A
      dsimp[ι,Grpd.forgetToCat,Bundled.α,Cat.of]
      simp[ULiftHom.objDown,Bundled.of]





















    simp
  . sorry

#check IsHomLift.domain_eq
#check CategoryTheory.Functor.IsCartesian

theorem GroupoidSigmaBeckChevalley (Δ Γ: Grpd) (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd)
  (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : σ ⋙ GroupoidSigma A B = GroupoidSigma (σ ⋙ A)
  (Grothendieck.Groupoidal.Map Δ Γ σ A B) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  . intros X
    sorry
  . intros X Y f
    have h' : (σ ⋙ GroupoidSigma A B).IsCartesian ((GroupoidSigma (σ ⋙ A) (Grothendieck.Groupoidal.Map Δ Γ σ A B)).map f) f := by
    have h : (σ ⋙ GroupoidSigma A B).IsHomLift ((GroupoidSigma (σ ⋙ A) (Grothendieck.Groupoidal.Map Δ Γ σ A B)).map f) f := by
      apply?





    exact
      Eq.symm
        (IsHomLift.eq_of_isHomLift (σ ⋙ GroupoidSigma A B)
          (eqToHom sorry ≫
            (GroupoidSigma (σ ⋙ A) (Grothendieck.Groupoidal.Map Δ Γ σ A B)).map f ≫
              eqToHom (Eq.symm sorry))
          f)





def GroupoidPair

end NaturalModelSigma
