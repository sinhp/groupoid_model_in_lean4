import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import GroupoidModel.Tarski.NaturalModel
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal

/-!
Here we construct the natural model for groupoids.

TODO: This file needs to eventually be ported to GroupoidRussellNaturalModel
but currently we don't have a Russell style sigma type.
-/

universe u v u₁ v₁ u₂ v₂

open CategoryTheory ULift

noncomputable section

section

section
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

end

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
  ext _ A := sGrpd.of (ext A)
  disp _ A := disp A
  var _ A := var A
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

def  PointToFiberNT {Γ : Grpd} (A : Γ ⥤ Grpd) (X Y : Γ) (f : X ⟶ Y) : PointToFiber A X ⟶ ((A.map f) ⋙ (PointToFiber A Y)) where
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

-- now base.uvPolyTp
def uv_tp : UvPoly Tm.{u} Ty.{u} where
  p := tp

-- now base.Ptp
def P : Psh sGrpd ⥤ Psh sGrpd := uv_tp.functor.{u}

-- now GroupoidModel.sigma
def GroupoidSigma (Γ : Grpd) (A : Γ ⥤ Grpd) (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : Γ ⥤ Grpd where
  obj x := Grpd.of (Grothendieck.Groupoidal ((PointToFiber A x) ⋙ B))
  map f := by
    rename_i X Y
    have NT' : (PointToFiber A X) ⋙ (B ⋙ Grpd.forgetToCat) ⟶ (A.map f ⋙ PointToFiber A Y) ⋙ (B ⋙ Grpd.forgetToCat) := whiskerRight (PointToFiberNT A X Y f) (B ⋙ Grpd.forgetToCat)
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

def GroupoidSigmaMake {Γ : Grpd} {A : Γ ⥤ Grpd} {B : (Grothendieck.Groupoidal A) ⥤ Grpd} {x : Γ} (Ax : A.obj x) (Bx : B.obj {base := x, fiber := Ax}): (GroupoidSigma Γ A B).obj x := by
  fconstructor
  . exact Ax
  . exact Bx

def GroupoidSigmaBase (Γ : Grpd) (A : Γ ⥤ Grpd) (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : (GroupoidSigma Γ A B) ⟶ A := by
  fconstructor
  . dsimp [GroupoidSigma]
    intro x
    dsimp[Quiver.Hom]
    sorry
    --exact Grothendieck.forget (Grpd.ForgetToCat (PointToFiber A x ⋙ B))
  . intros X Y f
    sorry
    --exact rfl

-- this is now called `sigmaBeckChevalley`
theorem GroupoidSigmaBeckChevalley (Δ Γ: Grpd.{v,u}) (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd.{v,u})
  (B : (Grothendieck.Groupoidal A) ⥤ Grpd.{v,u}) : σ ⋙ GroupoidSigma Γ A B = GroupoidSigma _ (σ ⋙ A)
  (Grothendieck.Groupoidal.Map Δ Γ σ A B) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  . intros X
    sorry
  . intros X Y f
    sorry

instance : Limits.HasLimits (Psh sGrpd) := by
  infer_instance

instance {Γ : sGrpd} (A : yoneda.obj Γ ⟶ Ty): Limits.HasLimit (Limits.cospan A uv_tp.p) := by
  infer_instance

def Limits_Sub {Γ : sGrpd} (A : yoneda.obj Γ ⟶ Ty): Limits.pullback A uv_tp.p ≅ yoneda.obj (GroupoidNM.ext _ A) := by
  refine ((IsPullback.isoPullback (snd := (NaturalModel.var Γ A)) (fst := yoneda.map (NaturalModel.disp Γ A))) ?_).symm
  have isPB := GroupoidNM.disp_pullback A
  exact IsPullback.flip isPB

-- this is now called `baseSig`
def GroupoidNMSigma : (P.obj.{u} Ty.{u}) ⟶ Ty.{u} := by
  fconstructor
  . dsimp [Quiver.Hom]
    intros sObj poly
    let poly' := yonedaEquiv.invFun poly
    let poly_as_pair := (UvPoly.equiv uv_tp (yoneda.obj (Opposite.unop sObj)) Ty).toFun poly'
    rcases poly_as_pair with ⟨A, B⟩
    have B := yonedaEquiv.toFun ((Limits_Sub A).inv ≫ B)
    exact downFunctor ⋙ (GroupoidSigma (sGrpd.forget.obj (Opposite.unop sObj)) (upFunctor ⋙ (yonedaEquiv.toFun A)) (upFunctor ⋙ B))
  . intros X Y f
    funext a
    refine CategoryTheory.Functor.ext ?_ ?_
    . intro b
      sorry
    . intros b₁ b₂ g
      sorry

abbrev R := UvPoly.genPb uv_tp Ty

#check Limits.pullback.condition

-- this is now called `basePair`
def GroupoidPair {Γ : sGrpd.{u}} (baB : (yoneda.obj Γ) ⟶ UvPoly.compDom uv_tp uv_tp) : (yoneda.obj Γ) ⟶ Tm := by
  refine yonedaCatEquiv.invFun ?_
  unfold UvPoly.compDom at baB
  let b := baB ≫ (Limits.pullback.fst (uv_tp.p) (UvPoly.genPb.u₂ uv_tp Ty))
  let aB := baB ≫ (Limits.pullback.snd (uv_tp.p) (UvPoly.genPb.u₂ uv_tp Ty))
  unfold UvPoly.genPb at aB
  let a := aB ≫ (Limits.pullback.snd (uv_tp.proj Ty) uv_tp.p)
  let AB := (aB ≫ (Limits.pullback.fst (uv_tp.proj Ty) uv_tp.p))
  let A := yonedaCatEquiv.toFun (UvPoly.polyPair uv_tp AB).fst
  let B := yonedaCatEquiv.toFun ((Limits_Sub _).inv ≫ (UvPoly.polyPair uv_tp AB).snd)
  haveI : Limits.HasLimits (sGrpdᵒᵖ ⥤ Type (u + 1)) := by
        infer_instance
  fconstructor
  fconstructor
  . intro x
    refine PGrpd.fromGrpd ((GroupoidSigma _ A B).obj x) (GroupoidSigmaMake ?_ ?_)
    . let ax := ((yonedaCatEquiv.toFun a).obj x).str.pt
      dsimp [a] at ax
      dsimp [A,AB,UvPoly.polyPair]
      let inst1 : Limits.HasLimit (Limits.cospan (uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd.{u})))) uv_tp.p) := by
        exact
          Limits.hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair
            (uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd)))) uv_tp.p
      let PB_com : (Limits.pullback.fst (uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd)))) uv_tp.p) ≫ uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd))) = (Limits.pullback.snd (uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd)))) uv_tp.p) ≫ uv_tp.p := by
        exact Limits.pullback.condition
      simp[PB_com]
      exact ax
    . let bx := ((yonedaCatEquiv.toFun b).obj x).str.pt
      dsimp [B,AB,aB,UvPoly.polyPair,UvPoly]
      dsimp [b] at bx
      have inst2 : Limits.HasLimit (Limits.cospan (uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd.{u})))) uv_tp.p) := by
        exact
          Limits.hasPullback_symmetry uv_tp.p
            (uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd.{u}))))
      -- let eq1 : (UvPoly.genPb.u₂ uv_tp (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd.{u})))) = Limits.pullback.fst (uv_tp.proj (PshsGrpdOfPshGrpd.obj (PshGrpdOfCat.obj (Cat.of Grpd.{u})))) uv_tp.p := by
      --   exact Limits.pullback.condition
      sorry
  sorry
  sorry
  sorry


def GroupoidNMPair : (UvPoly.compDom uv_tp uv_tp) ⟶ Tm := by
  fconstructor
  . intro Γ U
    exact yonedaEquiv.toFun (GroupoidPair (yonedaEquiv.invFun U))
  . intros X Y f
    sorry

def SigmaPullBack : IsPullback GroupoidNMPair (uv_tp.comp uv_tp).p tp GroupoidNMSigma := by sorry

end NaturalModelSigma
section NaturalModelPi

instance (C : Type) [Category C] (P : C → Prop) : Category {x : C // P x} where
  Hom x y := x.1 ⟶ y.1
  id x := 𝟙 x.1
  comp f g := f ≫ g

instance g (C : Type) [Groupoid C] (P : C → Prop) : Groupoid {x : C // P x} where
  inv f := Groupoid.inv f
  inv_comp _ := Groupoid.inv_comp ..
  comp_inv _ := Groupoid.comp_inv ..

instance (G1 G2 : Type) [Groupoid G1] [Groupoid G2] : Groupoid (G1 ⥤ G2) where
  inv f := by
    rename_i X Y
    fconstructor
    . intro x
      have t := f.app x
      exact Groupoid.inv t
    . simp

def GroupoidPiMap (Γ : Grpd) (A : Γ ⥤ Grpd) (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : Γ ⥤ Grpd where
  obj x := Grpd.of (A.obj x ⥤ (GroupoidSigma Γ A B).obj x)
  map f := by
    dsimp[Quiver.Hom]
    rename_i X Y
    fconstructor
    fconstructor
    . intro F
      exact A.map (Groupoid.inv f) ⋙ F ⋙ ((GroupoidSigma Γ A B).map f)
    . intros X' Y' f'
      fconstructor
      . intro x
        refine ((GroupoidSigma Γ A B).map f).map (f'.app _)
      . intros X' Y' f'
        dsimp
        sorry
    . sorry
    . sorry

def GroupoidPi (Γ : Grpd) (A : Γ ⥤ Grpd) (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : Γ ⥤ Grpd where
  obj x := by
    have t := g (A.obj x ⥤ (GroupoidSigma Γ A B).obj x) (fun(f) => f ⋙ ((GroupoidSigmaBase Γ A B).app x) = 𝟙 (A.obj x))
    exact Grpd.of {f : A.obj x ⥤ (GroupoidSigma Γ A B).obj x // f ⋙ ((GroupoidSigmaBase Γ A B).app x) = 𝟙 (A.obj x)}
  map f := by
    dsimp[Quiver.Hom]
    rename_i X Y
    sorry


end NaturalModelPi

section NaturalModelEq

end NaturalModelEq

end
