import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

import GroupoidModel.ForMathlib.CategoryTheory.Core
import GroupoidModel.Syntax.RepMap
import GroupoidModel.Grothendieck.Groupoidal.IsPullback

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

open CategoryTheory ULift Functor Groupoidal
  Limits RepMap Universe CategoryTheory.Functor

namespace CategoryTheory.PGrpd
def pGrpdToGroupoidalAsSmallFunctor : PGrpd.{v, v} ⥤
    ∫(Grpd.asSmallFunctor.{max w (v+1), v, v}) :=
  Grothendieck.functorTo PGrpd.forgetToGrpd
  (fun x => AsSmall.up.obj.{v, v, max w (v + 1)} x.fiber)
  (fun f => AsSmall.up.map f.fiber)
  (by aesop_cat)
  (by aesop_cat)

def groupoidalAsSmallFunctorToPGrpd :
    ∫(Grpd.asSmallFunctor.{max w (v+1), v, v}) ⥤ PGrpd.{v,v} :=
  PGrpd.functorTo Groupoidal.forget
  (fun x => AsSmall.down.obj.{v, v, max w (v + 1)} x.fiber)
  (fun f => AsSmall.down.map f.fiber)
  (by aesop_cat)
  (by aesop_cat)

@[simp] def pGrpdToGroupoidalAsSmallFunctor_groupoidalAsSmallFunctorToPGrpd :
    groupoidalAsSmallFunctorToPGrpd ⋙ pGrpdToGroupoidalAsSmallFunctor = 𝟭 _ :=
  rfl

@[simp] def groupoidalAsSmallFunctorToPGrpd_pGrpdToGroupoidalAsSmallFunctor :
    pGrpdToGroupoidalAsSmallFunctor ⋙ groupoidalAsSmallFunctorToPGrpd = 𝟭 _ :=
  rfl

@[simp] def pGrpdToGroupoidalAsSmallFunctor_forget : pGrpdToGroupoidalAsSmallFunctor
    ⋙ Groupoidal.forget = PGrpd.forgetToGrpd :=
  rfl

def asSmallFunctor : PGrpd.{v, v} ⥤ PGrpd.{max w (v+1), max w (v+1)} :=
  pGrpdToGroupoidalAsSmallFunctor ⋙
  toPGrpd Grpd.asSmallFunctor.{max w (v+1), v, v}

end CategoryTheory.PGrpd

namespace GroupoidModel

/--
Ctx is
the category of
{small groupoids - size u objects and size u hom sets}
which itself has size u+1 objects (small groupoids)
and size u hom sets (functors).
-/
@[reducible]
def Ctx := Grpd.{u,u}

instance : CartesianMonoidalCategory Ctx := inferInstanceAs (CartesianMonoidalCategory Grpd)

instance : HasFiniteLimits Grpd.{u,u} := sorry

instance : HasFiniteLimits Ctx := inferInstanceAs (HasFiniteLimits Grpd)

namespace Ctx

def coreAsSmall (C : Type (v+1)) [Category.{v} C] : Ctx.{max u (v+1)} :=
  Grpd.of (Core (AsSmall C))

def coreAsSmallFunctor {C : Type (v+1)} [Category.{v} C] {D : Type (w+1)} [Category.{w} D]
    (F : C ⥤ D) : coreAsSmall.{v, max u (v+1) (w+1)} C
    ⟶ coreAsSmall.{w, max u (v+1) (w+1)} D :=
  Grpd.homOf $ Functor.core $ AsSmall.down ⋙ F ⋙ AsSmall.up

end Ctx

open Ctx

section

variable {Γ Δ : Type u} [Groupoid Γ] [Groupoid Δ] (σ : Δ ⥤ Γ) {C : Type (v+1)} [Category.{v} C]
    {D : Type (v+1)} [Category.{v} D]

def toCoreAsSmallEquiv : (Γ ⥤ coreAsSmall C) ≃ Γ ⥤ C :=
  Core.functorToCoreEquiv.symm.trans functorToAsSmallEquiv

theorem toCoreAsSmallEquiv_apply_comp_left (A : Γ ⥤ coreAsSmall C) :
    toCoreAsSmallEquiv (σ ⋙ A) = σ ⋙ toCoreAsSmallEquiv A := by
  rfl

theorem toCoreAsSmallEquiv_apply_comp_right (A : Γ ⥤ coreAsSmall C) (F : C ⥤ D) :
    toCoreAsSmallEquiv (A ⋙ coreAsSmallFunctor F) = toCoreAsSmallEquiv A ⋙ F := by
  rfl

theorem toCoreAsSmallEquiv_symm_apply_comp_left (A : Γ ⥤ C) :
    toCoreAsSmallEquiv.symm (σ ⋙ A) = σ ⋙ toCoreAsSmallEquiv.symm A := by
  dsimp only [toCoreAsSmallEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Grpd.comp_eq_comp]
  erw [functorToAsSmallEquiv_symm_apply_comp_left, Core.functorToCoreEquiv_apply,
    Core.functorToCore_comp_left]
  rfl

theorem toCoreAsSmallEquiv_symm_apply_comp_right (A : Γ ⥤ C) (F : C ⥤ D) :
    toCoreAsSmallEquiv.symm (A ⋙ F) = toCoreAsSmallEquiv.symm A ⋙ coreAsSmallFunctor F := by
  rfl

end

namespace U

/-- `Ty.{v}` is the object representing the
  universe of `v`-small types. -/
def Ty : Ctx := coreAsSmall Grpd.{v,v}

/-- `Tm.{v}` is the object representing `v`-small terms,
  living over `Ty.{v}`. -/
def Tm : Ctx := coreAsSmall PGrpd.{v,v}

/-- `tp.{v}` is the morphism representing `v`-small `tp`,
  for the universe `U`. -/
def tp : Tm.{v} ⟶ Ty.{v} :=
  coreAsSmallFunctor PGrpd.forgetToGrpd

variable {Γ : Ctx} (A : Γ ⟶ Ty.{v})

def classifier : Γ ⥤ Grpd.{v,v} :=
  toCoreAsSmallEquiv A

def ext : Ctx := Grpd.of (∫ classifier A)

@[reducible]
def disp : ext A ⟶ Γ := forget

def var : ext A ⟶ Tm.{v} :=
  toCoreAsSmallEquiv.symm (toPGrpd (classifier A))

/-- `liftTy` is the base map between two `v`-small universes
               toE
    E.{v} --------------> E.{v+1}
    |                      |
    |                      |
  π |                      | π
    |                      |
    v                      v
    Ty.{v}----liftTy-----> Ty.{v+1}
 -/
def liftTy : Ty.{v, max u (v+2)} ⟶ Ty.{v+1, max u (v+2)} :=
  coreAsSmallFunctor.{v+1,v} Grpd.asSmallFunctor.{v+1}

def liftTm : Tm.{v, max u (v+2)} ⟶ Tm.{v+1,max u (v+2)} :=
  coreAsSmallFunctor.{v+1,v} PGrpd.asSmallFunctor.{v+1}

end U

def repMap : RepMap Ctx where
  Representable := sorry -- isofibrations? coherent isofibrations?
  exponentiableMorphism := sorry
  pullback_stable := sorry

end GroupoidModel

end
