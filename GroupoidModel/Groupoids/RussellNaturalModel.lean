import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

import GroupoidModel.Russell_PER_MS.NaturalModelBase
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal


/-!
Here we construct the natural model for groupoids.

TODO: This file needs to eventually be ported to GroupoidRussellNaturalModel
but currently we don't have a Russell style sigma type.
-/

universe u v u₁ v₁ u₂ v₂

open CategoryTheory ULift Grothendieck

/-
Grpd.{u, u} is
the category of
{small groupoids - size u objects and size u hom sets}
which itself has size u+1 objects (small groupoids)
and size u hom sets (functors).
We want this to be a small category so we lift the homs.
-/


namespace CategoryTheory
namespace GroupoidNM
abbrev Ctx := AsSmall.{u} Grpd.{u,u}

def Ctx.ofGroupoid (C : Type u) [Groupoid.{u} C] : Ctx.{u} :=
  AsSmall.up.obj (Grpd.of C)

def Ctx.toGrpd (Γ : Ctx.{u}) : Grpd.{u,u} := AsSmall.down.obj Γ

@[simps] def catLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
    obj x := Cat.of (ULift.{u + 1, u} x)
    map {x y} f := downFunctor ⋙ f ⋙ upFunctor

variable (C D) [Category.{u} C] [Category.{u} D]

abbrev yonedaCat : Cat.{u,u+1} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj
    (AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op

instance yonedaCatPreservesLim : Limits.PreservesLimits yonedaCat :=
  Limits.comp_preservesLimits _ _

variable {Γ Δ : Ctx.{u}} {C D : Type (u+1)}
  [Category.{u,u+1} C] [Category.{u,u+1} D]

/- The bijection y(Γ) → [-,C]   ≃   Γ ⥤ C -/
def yonedaCatEquiv :
    (yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C))
      ≃ Γ.toGrpd ⥤ C :=
  Equiv.trans yonedaEquiv
    {toFun     := λ A ↦ ULift.upFunctor ⋙ A
     invFun    := λ A ↦ ULift.downFunctor ⋙ A
     left_inv  := λ _ ↦ rfl
     right_inv := λ _ ↦ rfl}

theorem yonedaCatEquiv_naturality
    (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C)) (σ : Δ ⟶ Γ) :
    (AsSmall.down.map σ) ⋙ yonedaCatEquiv A
      = yonedaCatEquiv (yoneda.map σ ≫ A) := by
  simp only [AsSmall.down_obj, AsSmall.down_map, yonedaCatEquiv,
    Functor.op_obj, Functor.comp_obj, Cat.of_α,
    Equiv.trans_apply, Equiv.coe_fn_mk, ← yonedaEquiv_naturality]
  rfl

theorem yonedaCatEquiv_comp
    (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of D)) (U : D ⥤ C) :
    yonedaCatEquiv (A ≫ yonedaCat.map U) = yonedaCatEquiv A ⋙ U := by
  aesop_cat

abbrev Ty : Psh Ctx.{u} := yonedaCat.obj (Cat.of Grpd.{u,u})

abbrev Tm : Psh Ctx.{u} := yonedaCat.obj (Cat.of PGrpd.{u,u})

variable {Γ : Ctx.{u}} (A : yoneda.obj Γ ⟶ Ty)

abbrev tp : Tm ⟶ Ty := yonedaCat.map (PGrpd.forgetToGrpd)

abbrev ext : Ctx := Ctx.ofGroupoid (Groupoidal (yonedaCatEquiv A))

abbrev disp : ext A ⟶ Γ :=
  AsSmall.up.map (Grothendieck.forget (yonedaCatEquiv A ⋙ Grpd.forgetToCat))

abbrev var : (yoneda.obj (ext A) : Psh Ctx) ⟶ Tm :=
  yonedaCatEquiv.invFun (Groupoidal.toPGrpd (yonedaCatEquiv A))

/-- The image of (roughly) `Groupoidal.toPGrpd : Grothendieck A ⥤ PGrpd`
  under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapToPGrpd :
    yonedaCat.obj (IsPullback.uLiftGrothendieck $ Groupoidal.toCat (yonedaCatEquiv A)) ⟶ Tm :=
  yonedaCat.map
      (Cat.homOf (ULift.downFunctor ⋙ Groupoidal.toPGrpd (yonedaCatEquiv A)))

/-- The image of (roughly) `Grothendieck.forget : Grothendieck A ⥤ Γ` under
  `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapGrothendieckForget := 
      (yonedaCat.map $ IsPullback.uLiftGrothendieckForget
        (Groupoidal.toCat.{u} $ yonedaCatEquiv A))

/-- The image of `yonedaCatEquiv A` under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapYonedaCatEquiv :
    yonedaCat.obj (IsPullback.uLiftΓ.{u,u} Γ.toGrpd) ⟶ Ty :=
  yonedaCat.map (Cat.homOf (ULift.downFunctor.{u,u} ⋙ (yonedaCatEquiv A)))

/-- The image of the pullback `Grothendieck.Groupoidal.isPullback` under `yonedaCat` -/
theorem isPullback_yonedaCatGrothendieckForget_tp :
    IsPullback
      (yonedaCatMapToPGrpd A)
      (yonedaCatMapGrothendieckForget A)
      tp
      (yonedaCatMapYonedaCatEquiv A) :=
    Functor.map_isPullback _ (Groupoidal.isPullback _)

def asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat :
    (AsSmall.up) ⋙ (yoneda : Ctx.{u} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1))
    ≅ Grpd.forgetToCat ⋙ catLift ⋙ yonedaCat where
  hom := {app Γ := yonedaEquiv.symm (CategoryStruct.id _)}
  inv := {
    app Γ := {
      app Δ := λ F ↦ AsSmall.up.map $ ULift.upFunctor ⋙ F ⋙ ULift.downFunctor}}

/-- `yoneda.map (disp A)` is isomorphic to `yonedaCat(uLiftGrothendieckForget _)` in
  the arrow category, hence forming a pullback square

  yoneda (ext A) ------≅----> yonedaCat(uLift (ext A))
         |                                |
         |                                |
         |                                |
         |                                |
         |                                |
         v                                v
      yoneda Γ --------≅----> yonedaCat(uLift Γ)
-/
theorem isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget :
    IsPullback
      (asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.app _)
      (yoneda.map (disp A))
      (yonedaCatMapGrothendieckForget A)
      (asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.app Γ.toGrpd)
      :=
    IsPullback.of_horiz_isIso ⟨
      asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.naturality
      (AsSmall.down.map (disp A))⟩

theorem isPullback_yonedaDisp_tp :
    IsPullback (var A) (yoneda.map (disp A)) tp A := by
  convert IsPullback.paste_horiz
    (isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget A)
    (isPullback_yonedaCatGrothendieckForget_tp _)
  ext Δ F
  exact congr_fun (@A.naturality (Opposite.op Γ) Δ F.op) (CategoryStruct.id Γ)

end GroupoidNM

open GroupoidNM

-- TODO link to `CategoryTheory.GroupidNMBase` in blueprint
def GroupoidNMBase : NaturalModelBase Ctx.{u} where
  Ty := Ty
  Tm := Tm
  tp := tp
  ext := ext
  disp := disp
  var := var
  disp_pullback := isPullback_yonedaDisp_tp




end CategoryTheory
