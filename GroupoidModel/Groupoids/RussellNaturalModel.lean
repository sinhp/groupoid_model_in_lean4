import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat

import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal


/-!
Here we construct the natural model for groupoids.
-/

universe w v u v₁ u₁ v₂ u₂

noncomputable section
open CategoryTheory ULift Grothendieck Limits NaturalModelBase


namespace CategoryTheory


instance Groupoid.asSmall (Γ : Type w) [Groupoid.{v} Γ] :
    Groupoid (AsSmall.{max w u v} Γ) where
  inv f := AsSmall.up.map (inv (AsSmall.down.map f))

def Grpd.asSmallFunctor : Grpd.{v, u} ⥤ Grpd.{max w v u, max w v u} where
  obj Γ := Grpd.of $ AsSmall.{max w v u} Γ
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

namespace PGrpd

instance asSmallPointedGroupoid (Γ : Type w) [PointedGroupoid.{v} Γ] :
    PointedGroupoid.{max w v u, max w v u} (AsSmall.{max w v u} Γ) := {
  Groupoid.asSmall.{w,v,u} Γ with
  pt := AsSmall.up.obj PointedGroupoid.pt}

def asSmallFunctor : PGrpd.{v, u} ⥤ PGrpd.{max w v u, max w v u} where
  obj Γ := PGrpd.of $ AsSmall.{max w v u} Γ
  map F := {
    toFunctor := AsSmall.down ⋙ F.toFunctor ⋙ AsSmall.up
    point := AsSmall.up.map F.point}


end PGrpd

namespace Core

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

@[simp]
theorem id_inv (X : C) :
    Iso.inv (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl

@[simp]
theorem comp_inv {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).inv = g.inv ≫ f.inv :=
  rfl

def functor' (F : C ⥤ D) : Core C ⥤ Core D where
  obj := F.obj
  map f := {
    hom := F.map f.hom
    inv := F.map f.inv}
  map_id x := by
    simp only [Grpd.coe_of, id_hom, Functor.map_id, id_inv]
    congr 1
  map_comp f g := by
    simp only [Grpd.coe_of, comp_hom, Functor.map_comp, comp_inv]
    congr 1

lemma functor'_comp_inclusion (F : C ⥤ D) :
    functor' F ⋙ inclusion D = inclusion C ⋙ F :=
  rfl

def functor : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := Grpd.homOf (functor' F)

variable {Γ : Type u} [Groupoid.{v} Γ]

/-  A functor from a groupoid into a category is equivalent
    to a functor from the groupoid into the core -/
def functorToCoreEquiv : Γ ⥤ D ≃ Γ ⥤ Core D where
  toFun := functorToCore
  invFun := forgetFunctorToCore.obj
  left_inv _ := rfl
  right_inv _ := by
    simp [functorToCore, forgetFunctorToCore]
    apply Functor.ext
    · intro x y f
      simp only [inclusion, id_eq, Functor.comp_obj, Functor.comp_map,
        IsIso.Iso.inv_hom, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      congr
    · intro
      rfl

namespace IsPullback

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D)

lemma w' : Cat.homOf (inclusion C) ≫ Cat.homOf F
    = Cat.homOf (Core.functor' F) ⋙ Cat.homOf (inclusion D) := rfl

variable {F} [F.ReflectsIsomorphisms]

def lift (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    s.pt ⥤ Core C := {
  obj := s.fst.obj
  map {x y} f := @asIso _ _ _ _ (s.fst.map f) $ by
    let f' : F.obj (s.fst.obj x) ≅ F.obj (s.fst.obj y) :=
      (eqToIso s.condition).app x ≪≫ s.snd.map f ≪≫ (eqToIso s.condition.symm).app y
    have hnat : F.map (s.fst.map f) ≫ _
      = _ ≫ (inclusion D).map (s.snd.map f)
      := (eqToHom s.condition).naturality f
    have h : F.map (s.fst.map f) = f'.hom := by
      simp only [Cat.eqToHom_app, comp_eqToHom_iff] at hnat
      simp only [hnat, f', Core.inclusion]
      simp
    have : IsIso (F.map (s.fst.map f)) := by rw [h]; exact Iso.isIso_hom f'
    exact Functor.ReflectsIsomorphisms.reflects F (s.fst.map f)
  map_id x := by
    simp only [asIso, Functor.map_id, IsIso.inv_id]
    congr 1
  map_comp f g := by
    simp only [asIso, Functor.map_comp, IsIso.inv_comp]
    congr 1
    simp
}

def fac_left (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    lift s ≫ Cat.homOf (inclusion C) = s.fst := rfl

theorem Core.eqToIso_hom {a b : Core C} (h1 : a = b)
  (h2 : (inclusion C).obj a = (inclusion C).obj b) :
    (eqToHom h1).hom = eqToHom h2 := by
  cases h1
  rfl

def fac_right (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    lift s ≫ Cat.homOf (functor' F) = s.snd := by
  apply Functor.ext
  · intro x y f
    apply Functor.map_injective (inclusion D)
    have h := Functor.congr_hom s.condition f
    unfold Cat.homOf at *
    unfold inclusion at *
    simp only [Cat.of_α, Cat.comp_obj, lift, functor', comp_hom] at *
    convert h
    · apply Core.eqToIso_hom
    · apply Core.eqToIso_hom
  · intro x
    exact Functor.congr_obj s.condition x

def uniq (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D)))
  (m : s.pt ⟶ Cat.of (Core C))
  (fl : m ≫ Cat.homOf (inclusion C) = s.fst) :
    m = lift s := by
  apply Functor.ext
  · intro x y f
    apply Functor.map_injective (inclusion C)
    have h := Functor.congr_hom fl f
    unfold Cat.homOf at *
    unfold inclusion at *
    simp only [Cat.of_α, Cat.comp_map, lift, comp_hom, asIso_hom] at *
    rw [h, Core.eqToIso_hom, Core.eqToIso_hom]
  · intro x
    exact Functor.congr_obj fl x

end IsPullback

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) [F.ReflectsIsomorphisms]

open IsPullback

/--
  In the category of categories,
  if functor `F : C ⥤ D` reflects isomorphisms
  then taking the `Core` is pullback stable along `F`

  Core C ---- inclusion -----> C
    |                          |
    |                          |
    |                          |
 Core.functor' F               F
    |                          |
    |                          |
    V                          V
  Core D ---- inclusion -----> D
-/
theorem isPullback_functor'_self :
    IsPullback
      (Cat.homOf $ inclusion C)
      (Cat.homOf $ functor' F)
      (Cat.homOf F)
      (Cat.homOf $ inclusion D) :=
  IsPullback.of_isLimit $
    PullbackCone.IsLimit.mk
      (w' F) lift fac_left fac_right
      (λ s m fl _ ↦ uniq s m fl)
end Core

instance {C : Type u} [Category.{v} C] :
    Functor.IsEquivalence (AsSmall.up : C ⥤ AsSmall C) :=
  AsSmall.equiv.isEquivalence_functor

namespace ULift
namespace Core

variable {C : Type u} [Category.{v} C]

-- FIXME could be generalized?
def isoCoreULift :
    Cat.of (ULift.{w} (Core C)) ≅
      Cat.of (Core (ULift.{w} C)) where
  hom := Cat.homOf (downFunctor ⋙ Core.functor' upFunctor)
  inv := Cat.homOf (Core.functor' downFunctor ⋙ upFunctor)

end Core
end ULift
namespace LargeUniverse

open PGrpd PGrpd.IsPullback

def CAT : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (Cat.{max u (v+1), max u (v+1)})
def PCAT : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (PCat.{max u (v+1), max u (v+1)})
def GRPD : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (Grpd.{max u (v+1), max u (v+1)})
def PGRPD : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (PGrpd.{max u (v+1), max u (v+1)})
def grpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} Grpd.{v,v})
def pgrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} PGrpd.{v,v})
def coregrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of $ Core $ IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} Grpd.{v,v})
def corepgrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of $ Core $ IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} PGrpd.{v,v})

abbrev grothendieckAsSmallFunctor : Type (max u (v+1)) :=
  Grothendieck $
    Grpd.asSmallFunctor.{max u (v+1), v, v}
    ⋙ Grpd.forgetToCat.{max u (v+1)}

def GROTH : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (ULift.{max u (v+1) + 1, max u (v+1)}
        grothendieckAsSmallFunctor.{v,u})

def PCATFORGETTOCAT : PCAT.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf PCat.forgetToCat.{max u (v+1), max u (v+1)}
def PGRPDFORGETTOGRPD : PGRPD.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf PGrpd.forgetToGrpd.{max u (v+1), max u (v+1)}
def GRPDFORGETTOCAT : GRPD.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf Grpd.forgetToCat.{max u (v+1), max u (v+1)}
def PGRPDFORGETTOPCAT : PGRPD.{v,u} ⟶ PCAT.{v,u} :=
  Cat.homOf PGrpd.forgetToPCat.{max u (v+1), max u (v+1)}

def pgrpdforgettogrpd : pgrpd.{v,u} ⟶ grpd.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor)
def grpdassmallfunctor : grpd.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ Grpd.asSmallFunctor.{max u (v+1)})
def pgrpdassmallfunctor : pgrpd.{v,u} ⟶ PGRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.asSmallFunctor.{max u (v+1)})
def corepgrpdforgettogrpd : corepgrpd.{v,u} ⟶ coregrpd.{v,u} :=
  Cat.homOf $ Core.functor' $
    downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor

def coreFunctorPGrpdForgetToGrpd : corepgrpd.{v,u} ⟶ coregrpd.{v,u} :=
  Cat.homOf (Core.functor.map pgrpdforgettogrpd)
def inclusionGrpdCompAsSmallFunctor : coregrpd.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf (
    Core.inclusion _
    ⋙ downFunctor
    ⋙ AsSmall.down
    ⋙ Grpd.asSmallFunctor.{max u (v+1)})

def inclusionPGrpdCompAsSmallFunctor : corepgrpd.{v,u} ⟶ PGRPD.{v,u} :=
  Cat.homOf (
    Core.inclusion _
    ⋙ downFunctor
    ⋙ AsSmall.down
    ⋙ PGrpd.asSmallFunctor.{max u (v+1)})

def asSmallFunctorCompForgetToCat' :
    AsSmall.{u} Grpd.{v,v} ⥤ Cat.{max u (v+1), max u (v+1)} :=
  AsSmall.down
    ⋙ Grpd.asSmallFunctor.{max u (v+1), v, v}
    ⋙ Grpd.forgetToCat.{max u (v+1)}

-- def asSmallFunctorCompForgetToCat : grpd.{v,u} ⟶ CAT.{v,u} :=
--   Cat.homOf $ ULift.downFunctor ⋙ asSmallFunctorCompForgetToCat'

def grothendieckAsSmallFunctorToPGrpd :
    grothendieckAsSmallFunctor.{v, u} ⥤ PGrpd.{v,v} where
  obj x := PGrpd.fromGrpd x.base
    (AsSmall.down.obj.{v, v, max (v + 1) u} x.fiber)
  map f := {
    toFunctor := f.base
    point := AsSmall.down.map f.fiber}

def pGrpdToGrothendieckAsSmallFunctor :
    PGrpd.{v, v} ⥤ grothendieckAsSmallFunctor.{v,u} where
  obj x := {
    base := Grpd.of x
    fiber := AsSmall.up.obj.{v, v, max (v + 1) u} x.str.pt}
  map f := {
    base := f.toFunctor
    fiber := AsSmall.up.map f.point}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [Grpd.forgetToCat, Grpd.asSmallFunctor]
    · rfl

def grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor' :
    grothendieckAsSmallFunctor.{v,u} ⥤ Grothendieck asSmallFunctorCompForgetToCat'.{v,u} where
  obj x := {
    base := AsSmall.up.obj x.base
    fiber := x.fiber}
  map f := {
    base := AsSmall.up.map f.base
    fiber := f.fiber
    }
  map_comp f g := by
    apply Grothendieck.ext
    · simp [asSmallFunctorCompForgetToCat']
    · rfl

def grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor :
    Grothendieck asSmallFunctorCompForgetToCat'.{v,u} ⥤ grothendieckAsSmallFunctor.{v,u} where
  obj x := {
    base :=  AsSmall.down.obj x.base
    fiber := x.fiber}
  map f := {
    base := AsSmall.down.map f.base
    fiber := f.fiber}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [asSmallFunctorCompForgetToCat']
    · rfl

def pGrpd_iso_GrothendieckAsSmallFunctor :
    pgrpd.{v,u}
      ≅ Cat.of (ULift.{max u (v+1) + 1, max u (v+1)}
        grothendieckAsSmallFunctor.{v,u}) where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGrothendieckAsSmallFunctor
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ grothendieckAsSmallFunctorToPGrpd
    ⋙ AsSmall.up
    ⋙ ULift.upFunctor

def pGrpdIsoULiftGrothendieck :
    pgrpd.{v,u}
      ≅ IsPullback.uLiftGrothendieck
        asSmallFunctorCompForgetToCat'.{v,u} where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGrothendieckAsSmallFunctor
    ⋙ grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor'
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor
    ⋙ grothendieckAsSmallFunctorToPGrpd
    ⋙ AsSmall.up
    ⋙ ULift.upFunctor

/--
The following square is a pullback

Grothendieck (asSmallFunctor...) -- toPGrpd --> PCat.{max v u, max v u}
        |                                     |
        |                                     |
    forget                               PCat.forgetToCat
        |                                     |
        v                                     v
 Grpd.{v,v}--asSmallFunctor ⋙ forgetToCat-->Cat.{max v u, max v u}
-/
theorem isPullback_uLiftGrothendieckForgetAsSmallFunctorCompForgetToCat'_PCATFORGETTOCAT
    : IsPullback
      (IsPullback.uLiftToPCat asSmallFunctorCompForgetToCat'.{v,u}
        ⋙ Cat.ULift_iso_self.hom)
      (IsPullback.uLiftGrothendieckForget asSmallFunctorCompForgetToCat')
      PCATFORGETTOCAT.{v,u}
      (IsPullback.uLiftA asSmallFunctorCompForgetToCat'
        ⋙ Cat.ULift_iso_self.hom)
      :=
  IsPullback.paste_horiz
    (Grothendieck.isPullback.{max u (v+1)} (asSmallFunctorCompForgetToCat'.{v,u}))
    (IsPullback.of_horiz_isIso ⟨rfl⟩)

/--
The following square is a pullback

   PGrpd.{v,v} -- PGrpd.asSmallFunctor ⋙ PGrpd.forgetToPCat --> PCat.{max v u, max v u}
        |                                                           |
        |                                                           |
    PGrpd.forgetToGrpd                                          PCat.forgetToCat
        |                                                           |
        |                                                           |
        v                                                           v
   Grpd.{v,v}  -- Grpd.asSmallFunctor ⋙ Grpd.forgetToCat --> Cat.{max v u, max v u}
-/
theorem isPullback_pgrpdforgettogrpd_PCATFORGETTOCAT :
  IsPullback
    (pgrpdassmallfunctor ≫ PGRPDFORGETTOPCAT.{v,u})
    pgrpdforgettogrpd.{v,u}
    PCATFORGETTOCAT.{v,u}
    (grpdassmallfunctor ≫ GRPDFORGETTOCAT.{v,u}) :=
  IsPullback.of_iso_isPullback
    isPullback_uLiftGrothendieckForgetAsSmallFunctorCompForgetToCat'_PCATFORGETTOCAT
    pGrpdIsoULiftGrothendieck

/--
The following square is a pullback

   PGrpd.{v,v} -- PGrpd.asSmallFunctor --> PGrpd.{max v u, max v u}
        |                                     |
        |                                     |
    PGrpd.forgetToGrpd                    PGrpd.forgetToGrpd
        |                                     |
        v                                     v
   Grpd.{v,v}  -- Grpd.asSmallFunctor --> Grpd.{max v u, max v u}
-/
theorem isPullback_pgrpdforgettogrpd_PGRPDFORGETTOGRPD :
    IsPullback
      pgrpdassmallfunctor.{v,u}
      pgrpdforgettogrpd.{v,u}
      PGRPDFORGETTOGRPD.{v,u}
      grpdassmallfunctor.{v,u} :=
  IsPullback.of_right
    isPullback_pgrpdforgettogrpd_PCATFORGETTOCAT.{v,u}
    rfl
    isPullback_forgetToGrpd_forgetToCat

instance (C : Type u) [Category.{v} C] :
    (downFunctor : ULift.{w} C ⥤ C).ReflectsIsomorphisms :=
  ULift.equivalence.fullyFaithfulInverse.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (upFunctor : C ⥤ ULift.{w} C).ReflectsIsomorphisms :=
  ULift.equivalence.fullyFaithfulFunctor.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (AsSmall.down : AsSmall.{w} C ⥤ C).ReflectsIsomorphisms :=
  AsSmall.equiv.fullyFaithfulInverse.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C).ReflectsIsomorphisms :=
  AsSmall.equiv.fullyFaithfulFunctor.reflectsIsomorphisms

instance : forgetToGrpd.ReflectsIsomorphisms := by
  constructor
  intro A B F hiso
  rcases hiso with ⟨ G , hFG , hGF ⟩
  use ⟨ G , G.map (Groupoid.inv F.point)
    ≫ eqToHom (Functor.congr_obj hFG A.str.pt) ⟩
  constructor
  · apply PointedFunctor.ext
    · simp
    · exact hFG
  · apply PointedFunctor.ext
    · simp
      have h := Functor.congr_hom hGF F.point
      simp [Grpd.id_eq_id, Grpd.comp_eq_comp, Functor.comp_map] at h
      simp [h, eqToHom_map]
    · exact hGF

instance : Functor.ReflectsIsomorphisms pgrpdforgettogrpd := by
  have : (forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor).ReflectsIsomorphisms := by
    rw [← Functor.assoc]
    apply reflectsIsomorphisms_comp
  have : (AsSmall.down
      ⋙ forgetToGrpd
      ⋙ AsSmall.up
      ⋙ upFunctor).ReflectsIsomorphisms := by
    apply reflectsIsomorphisms_comp
  have h : Functor.ReflectsIsomorphisms
    (downFunctor
    ⋙ AsSmall.down
    ⋙ forgetToGrpd
    ⋙ AsSmall.up
    ⋙ upFunctor) := by
    apply reflectsIsomorphisms_comp
  exact h

/--
The following square is a pullback

Core PGrpd.{v,v} -- PGrpd.asSmallFunctor --> PGrpd.{max v u, max v u}
        |                                     |
        |                                     |
Core PGrpd.forgetToGrpd             PGrpd.forgetToGrpd
        |                                     |
        v                                     v
Core Grpd.{v,v}  -- Grpd.asSmallFunctor --> Grpd.{max v u, max v u}
-/
theorem isPullback_corepgrpdforgettogrpd_PGRPDFORGETTOGRPD :
    IsPullback
      inclusionPGrpdCompAsSmallFunctor.{v,u}
      coreFunctorPGrpdForgetToGrpd.{v,u}
      PGRPDFORGETTOGRPD.{v,u}
      inclusionGrpdCompAsSmallFunctor.{v,u} :=
  IsPullback.paste_horiz
    (Core.isPullback_functor'_self pgrpdforgettogrpd.{v,u})
    (isPullback_pgrpdforgettogrpd_PGRPDFORGETTOGRPD.{v,u})

end LargeUniverse

namespace GroupoidNaturalModel

/--
Ctx is
the category of
{small groupoids - size u objects and size u hom sets}
which itself has size u+1 objects (small groupoids)
and size u hom sets (functors).

We want our context category to be a small category so we will use
`AsSmall.{u}` for some large enough `u`
-/
abbrev Ctx := AsSmall.{u} Grpd.{u,u}

namespace Ctx
def ofGrpd : Grpd.{u,u} ⥤ Ctx.{u} := AsSmall.up

def ofGroupoid (Γ : Type u) [Groupoid.{u} Γ] : Ctx.{u} :=
  ofGrpd.obj (Grpd.of Γ)

def toGrpd : Ctx.{u} ⥤ Grpd.{u,u} := AsSmall.down

/-- This is the terminal or empty context. As a groupoid it has a single point
  given by ⟨⟨⟩⟩ -/
def chosenTerminal : Ctx.{u} := AsSmall.up.obj Grpd.chosenTerminal.{u}

def chosenTerminalIsTerminal : IsTerminal Ctx.chosenTerminal.{u} :=
  IsTerminal.isTerminalObj AsSmall.up.{u} Grpd.chosenTerminal
    Grpd.chosenTerminalIsTerminal
def terminalPoint : Ctx.toGrpd.obj Ctx.chosenTerminal := ⟨⟨⟩⟩

-- def Ctx.coreOfCategory (C : Type u) [Category.{v} C] : Ctx.{max w v u} :=
--   Ctx.ofGroupoid (Core (AsSmall.{w} C))

def core : Cat.{v,v+1} ⥤ Ctx.{max u (v+1)} :=
  Core.functor.{v,v+1}
  ⋙ Grpd.asSmallFunctor.{u,v,v+1}
  ⋙ Ctx.ofGrpd.{max u (v+1)}

variable {Γ Δ : Ctx.{max u (v+1)}} {C D : Type (v+1)}
  [Category.{v,v+1} C] [Category.{v,v+1} D]

def yonedaCoreEquiv' :
    (Γ ⟶ core.obj.{v,u} (Cat.of C))
      ≃ Ctx.toGrpd.obj Γ ⥤ Core C where
  toFun A := toGrpd.map A ⋙ AsSmall.down
  invFun A := Ctx.ofGrpd.map (A ⋙ AsSmall.up)
  left_inv _ := rfl
  right_inv _ := rfl

-- /- The bijection y(Γ) → y(core C) ≃ Γ ⥤ C -/
-- def yonedaCoreEquiv :
--     (y(Γ) ⟶ y(core.obj.{v,u} (Cat.of C)))
--       ≃ Ctx.toGrpd.obj Γ ⥤ C :=
--   Yoneda.fullyFaithful.homEquiv.symm.trans
--     (yonedaCoreEquiv'.trans
--     Core.functorToCoreEquiv.symm)

/- The bijection Γ → core C ≃ Γ ⥤ C -/
def yonedaCoreEquiv :
    (Γ ⟶ core.obj.{v,u} (Cat.of C))
      ≃ Ctx.toGrpd.obj Γ ⥤ C :=
  Equiv.trans
    yonedaCoreEquiv'
    Core.functorToCoreEquiv.symm

end Ctx

@[simps] def catLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
  obj x := Cat.of (ULift.{u + 1, u} x)
  map {x y} f := downFunctor ⋙ f ⋙ upFunctor

variable (C D) [Category.{u} C] [Category.{u} D]

abbrev yonedaCat : Cat.{u,u+1} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj
    (AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op

instance yonedaCatPreservesLimits : PreservesLimits yonedaCat :=
  comp_preservesLimits _ _

variable {Γ Δ : Ctx.{u}} {C D : Type (u+1)}
  [Category.{u,u+1} C] [Category.{u,u+1} D]

/- The bijection y(Γ) → [-,C]   ≃   Γ ⥤ C -/
def yonedaCatEquiv :
    (yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C))
      ≃ Ctx.toGrpd.obj Γ ⥤ C :=
  Equiv.trans yonedaEquiv
    {toFun     := λ A ↦ ULift.upFunctor ⋙ A
     invFun    := λ A ↦ ULift.downFunctor ⋙ A
     left_inv  := λ _ ↦ rfl
     right_inv := λ _ ↦ rfl}

lemma yonedaCatEquiv_yonedaEquivSymm {Γ : Ctx}
    (A : (yonedaCat.obj (Cat.of C)).obj (Opposite.op Γ)) :
    yonedaCatEquiv (yonedaEquiv.symm A) = upFunctor ⋙ A := by
  congr

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

abbrev tp : Tm ⟶ Ty := yonedaCat.map (PGrpd.forgetToGrpd)

section Ty
variable {Γ : Ctx.{u}} (A : yoneda.obj Γ ⟶ Ty)

abbrev ext : Ctx := Ctx.ofGrpd.obj $ Grpd.of (Groupoidal (yonedaCatEquiv A))

abbrev disp : ext A ⟶ Γ :=
  AsSmall.up.map (Grothendieck.forget _)

abbrev var : (y(ext A) : Psh Ctx) ⟶ Tm :=
  yonedaCatEquiv.symm (Groupoidal.toPGrpd (yonedaCatEquiv A))

/-- The image of (roughly) `Groupoidal.toPGrpd : Grothendieck A ⥤ PGrpd`
  under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
  -/
abbrev yonedaCatMapToPGrpd :
    yonedaCat.obj (IsPullback.uLiftGrothendieck $
      Groupoid.compForgetToCat (yonedaCatEquiv A)) ⟶ Tm :=
  yonedaCat.map
      (Cat.homOf (ULift.downFunctor ⋙ Groupoidal.toPGrpd (yonedaCatEquiv A)))

/-- The image of (roughly) `Grothendieck.forget : Grothendieck A ⥤ Γ` under
  `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapGrothendieckForget :=
      (yonedaCat.map $ IsPullback.uLiftGrothendieckForget
        (Groupoid.compForgetToCat.{u} $ yonedaCatEquiv A))

/-- The image of `yonedaCatEquiv A` under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapYonedaCatEquiv :
    yonedaCat.obj (IsPullback.uLiftΓ.{u,u} $ Ctx.toGrpd.obj Γ) ⟶ Ty :=
  yonedaCat.map (Cat.homOf (ULift.downFunctor.{u,u} ⋙ (yonedaCatEquiv A)))

/-- The image of the pullback `Grothendieck.Groupoidal.isPullback` under `yonedaCat` -/
theorem isPullback_yonedaCatGrothendieckForget_tp :
    IsPullback
      (yonedaCatMapToPGrpd A)
      (yonedaCatMapGrothendieckForget A)
      tp
      (yonedaCatMapYonedaCatEquiv A) :=
  Functor.map_isPullback yonedaCat (Groupoidal.isPullback (yonedaCatEquiv A))

/-- This is a natural isomorphism between functors in the following diagram
  Ctx.{u}------ yoneda -----> Psh Ctx
   |                              Λ
   |                              |
   |                              |
  inclusion                 precomposition with inclusion
   |                              |
   |                              |
   |                              |
   V                              |
Cat.{big univ}-- yoneda -----> Psh Cat

-/
def asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat :
    (AsSmall.up) ⋙ (yoneda : Ctx.{u} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1))
    ≅ Grpd.forgetToCat ⋙ catLift ⋙ yonedaCat where
  hom := {app Γ := yonedaEquiv.symm (CategoryStruct.id _)}
  inv := {
    app Γ := {
      app Δ := λ F ↦
        AsSmall.up.map $ ULift.upFunctor ⋙ F ⋙ ULift.downFunctor}}

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
      (asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.app
        $ Ctx.toGrpd.obj Γ)
      :=
    IsPullback.of_horiz_isIso ⟨
      asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.naturality
      (AsSmall.down.map (disp A))⟩

/-- The pullback required for the natural model `GroupoidNaturalModel.base`-/
theorem isPullback_yonedaDisp_tp :
    IsPullback (var A) (yoneda.map (disp A)) tp A := by
  convert IsPullback.paste_horiz
    (isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget A)
    (isPullback_yonedaCatGrothendieckForget_tp _)
  ext Δ F
  exact congr_fun (@A.naturality (Opposite.op Γ) Δ F.op) (CategoryStruct.id Γ)

end Ty

-- TODO link to this in blueprint
/-- The natural model that acts as the ambient
  model in which the other universes live.
  Note that unlike the other universes this is *not* representable,
  but enjoys having representable fibers that land in itself.
-/
def base : NaturalModelBase Ctx.{u} where
  Ty := Ty
  Tm := Tm
  tp := tp
  ext := ext
  disp := disp
  var := var
  disp_pullback := isPullback_yonedaDisp_tp

def U' : Grpd.{max u (v+1),max u (v+1)} :=
  Grpd.of (Core (AsSmall.{u} Grpd.{v,v}))

/-- `U.{v}` is the object representing the
  universe of `v`-small types
  i.e. `y(U) = Ty` for the small natural models `baseU`. -/
def U : Ctx.{max u (v+1)} :=
  Ctx.ofGrpd.obj U'.{v,u}

def E' : Grpd.{max u (v+1),max u (v+1)} :=
  Grpd.of (Core (AsSmall.{u} PGrpd.{v,v}))

/-- `E.{v}` is the object representing `v`-small terms,
  living over `U.{v}`
  i.e. `y(E) = Tm` for the small natural models `baseU`. -/
def E : Ctx.{max (v + 1) u} :=
  Ctx.ofGrpd.obj E'.{v,u}

def π'' : AsSmall.{u} PGrpd.{v,v} ⥤ AsSmall.{u} Grpd.{v,v} :=
  AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up

abbrev π' : E'.{v,u} ⥤ U'.{v,u} :=
  Grpd.homOf (Core.functor' π'')

/-- `π.{v}` is the morphism representing `v`-small `tp`,
  for the small natural models `baseU`. -/
abbrev π : E.{v,u} ⟶ U.{v,u} :=
  Ctx.ofGrpd.map π'

open PGrpd LargeUniverse

-- FIXME this has an error without the `dsimp` saying it has
-- two non-defeq category instances
def U.isoYonedaCatGrpd : y(U.{v,u}) ≅ yonedaCat.obj (coregrpd.{v,u}) :=
  asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.app U'.{v,u}
    ≪≫ Functor.mapIso yonedaCat (by
      dsimp [Grpd.forgetToCat, U, U']
      exact ULift.Core.isoCoreULift)

-- FIXME this has an error without the `dsimp` saying it has
-- two non-defeq category instances
def E.isoYonedaCatPGrpd : y(E.{v,u}) ≅ yonedaCat.obj (corepgrpd.{v,u}) :=
  asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.app E'.{v,u}
    ≪≫ Functor.mapIso yonedaCat (by
      dsimp [Grpd.forgetToCat, E, E']
      exact ULift.Core.isoCoreULift)

/-- `toTy` is the map that classifies the universe
  `U` of `v`-small types as a map into the type classifier `Ty`.
  This will fit into the pullback square

    E --------toTm---> Tm
    |                   |
    |                   |
    |                   |
    |                   |
    v                   v
    U---------toTy----->Ty

-/
def U.toTy : y(U.{v,u}) ⟶ Ty.{max u (v+1)} :=
  isoYonedaCatGrpd.hom.{v,u} ≫ yonedaCat.map inclusionGrpdCompAsSmallFunctor.{v,u}

def E.toTm : y(E.{v,u}) ⟶ Tm.{max u (v+1)} :=
  isoYonedaCatPGrpd.hom.{v,u} ≫ yonedaCat.map inclusionPGrpdCompAsSmallFunctor.{v,u}

namespace U

open E

/--
The image of `isPullback_corepgrpdforgettogrpd_PGRPDFORGETTOGRPD`
under `yonedaCat` is a pullback

yonedaCat (Core PGrpd.{v,v}) ----> yonedaCat (PGrpd.{max v u, max v u}) = Tm
        |                                     |
        |                                     |
        |                                     tp
        |                                     |
        v                                     v
yonedaCat (Core Grpd.{v,v})  ----> yonedaCat (Grpd.{max v u, max v u}) = Ty
-/
theorem isPullback_yonedaCatCorePGrpdForgetToGrpd_tp :
    IsPullback
      (yonedaCat.map (inclusionPGrpdCompAsSmallFunctor.{v,u}))
      (yonedaCat.map (coreFunctorPGrpdForgetToGrpd.{v,u}))
      tp
      (yonedaCat.map (inclusionGrpdCompAsSmallFunctor.{v,u})) :=
  Functor.map_isPullback yonedaCat (isPullback_corepgrpdforgettogrpd_PGRPDFORGETTOGRPD)

theorem isPullback_yπ_yonedaCatCorepgrpdforgettogrpd :
    IsPullback
      E.isoYonedaCatPGrpd.{v,u}.hom
      ym(π.{v,u})
      (yonedaCat.map (corepgrpdforgettogrpd.{v,u}))
      U.isoYonedaCatGrpd.{v,u}.hom :=
  IsPullback.of_horiz_isIso ⟨rfl⟩

/--
The small universe and the ambient natural model form a pullback
      y(E) ------------ toTm --------------> Tm
        |                                     |
        |                                     |
      y(π)                                    tp
        |                                     |
        v                                     v
      y(U) ------------ toTy --------------> Ty
-/
theorem isPullback_yπ_tp :
    IsPullback toTm.{v,u} ym(π.{v,u}) tp toTy.{v,u} :=
  IsPullback.paste_horiz
    isPullback_yπ_yonedaCatCorepgrpdforgettogrpd
    isPullback_yonedaCatCorePGrpdForgetToGrpd_tp.{v,u}

variable {Γ : Ctx.{max u (v+1)}} (A : y(Γ) ⟶ y(U.{v}))

abbrev ext : Ctx.{max u (v+1)} :=
  GroupoidNaturalModel.ext (A ≫ toTy)

abbrev disp : ext A ⟶ Γ :=
  GroupoidNaturalModel.disp (A ≫ toTy)

/--
  `U.var` is the universal lift from the following diagram

  y(Γ.A) -.-.- var -.-,-> y(E) ------ toTm ------> Tm
   |                       |                       |
   |                       |                       |
ym(disp)                  y(π)                     tp
   |                       |                       |
   V                       V                       V
  y(Γ) ------- A ---> y(U) ------ toTy ------> Ty

  where the top map is `base.var` from the ambient natural model
-/
abbrev var : y(ext A) ⟶ y(E.{v}) :=
  isPullback_yπ_tp.{v,u}.lift (base.var (A ≫ toTy)) (ym(disp A) ≫ A)
    (base.disp_pullback (A ≫ toTy)).w

/--
  The induced pullback square on the left

  y(Γ.A) -.-.- var -.-,-> y(E) ------ toTm ------> Tm
   |                       |                       |
   |                       |                       |
ym(disp)                  y(π)                     tp
   |                       |                       |
   V                       V                       V
  y(Γ) ------- A -------> y(U) ------ toTy ------> Ty

  where the top map is `base.var` from the ambient natural model
-/
theorem isPullback_yoneda_disp_yoneda_π :
    IsPullback
      (U.var (A))
      ym(U.disp (A))
      ym(π)
      A :=
  IsPullback.of_right'
    (base.disp_pullback (A ≫ toTy))
    isPullback_yπ_tp.{v,u}

def toU'' : AsSmall.{max u (v+2)} Grpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} Grpd.{v+1,v+1} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def toU' : U'.{v, max u (v+2)} ⟶ U'.{v+1,max u (v+2)} :=
  Core.functor.map (Cat.homOf toU'')

/-- `toU` is the base map between two `v`-small universes
    E.{v} --------------> E.{v+1}
    |                      |
    |                      |
    |                      |
    |                      |
    v                      v
    U.{v}-------toU-----> U.{v+1}
 -/
def toU : U.{v, max u (v+2)} ⟶ U.{v+1, max u (v+2)} :=
  Ctx.ofGrpd.map toU'

def toE'' : AsSmall.{max u (v+2)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} PGrpd.{v+1,v+1} :=
  AsSmall.down ⋙ PGrpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def toE' : E'.{v, max u (v+2)} ⟶ E'.{v+1,max u (v+2)} :=
  Core.functor.map $ Cat.homOf toE''

def toE : E.{v, max u (v+2)} ⟶ E.{v+1,max u (v+2)} :=
  Ctx.ofGrpd.map toE'

namespace SmallUniverse

theorem comm_sq : Cat.homOf toE''.{v,u} ≫ Cat.homOf π'' =
  Cat.homOf π'' ≫ Cat.homOf toU''.{v,u} := rfl

section IsPullbackInCat

variable (c : Cat.{max u (v+2), max u (v+2)})
  (fst : c ⥤ PGrpd.{v+1,v+1})
  (snd : c ⥤ Grpd.{v,v})
  (condition : fst ⋙ PGrpd.forgetToGrpd.{v+1,v+1}
    = snd ⋙ Grpd.asSmallFunctor.{v+1, v, v})

def fac_left' :
    c ⥤ PGrpd.{v,v} := by
  let k := Functor.congr_obj condition 
  exact {
    obj x := PGrpd.ofGrpd (snd.obj x) sorry
    map f := sorry
}

end IsPullbackInCat

theorem comp_asSmallUp_inj {C : Type u} [Category.{v} C]
  {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ D}
    (h : F ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D) =
      G ⋙ AsSmall.up)
    : F = G := by
  convert_to F ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D)
    ⋙ AsSmall.down
    = G ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D)
    ⋙ AsSmall.down
  simp [← Functor.assoc, h]

def fac_left (s : PullbackCone
    (Cat.homOf (π''.{v+1,max u (v+2)}))
    (Cat.homOf (toU''.{v,max u (v+2)}))) :
    s.pt ⟶ Cat.of (AsSmall.{max u (v+2)} PGrpd.{v,v}) := by
  let c : Cat.{max u (v+2), max u (v+2)} := s.pt
  let fst : c ⥤ PGrpd.{v+1,v+1} := s.fst ⋙ AsSmall.down
  let snd : c ⥤ Grpd.{v,v} := s.snd ⋙ AsSmall.down
  let condition : fst ⋙ PGrpd.forgetToGrpd.{v+1,v+1}
      = snd ⋙ Grpd.asSmallFunctor.{v+1, v, v} :=
    comp_asSmallUp_inj s.condition
  

  sorry

-- NOTE unfortunately, because of universe variable difficulties
-- (namely `Ulift.{v} (ULift.{u} α) ≢ ULift.{max v u} α`)
-- I don't see a way to prove this using what we have already
/--
The following square is a pullback
 
 AsSmall PGrpd.{v} ------- toE'' ------> AsSmall PGrpd.{v+1}
        |                                     |
        |                                     |
        π'                                    π'
        |                                     |
        v                                     v
 AsSmall Grpd.{v}  ------- toU'' -----> AsSmall Grpd.{v+1}

in the category `Cat.{max u (v+2), max u (v+2)}`
-/
theorem isPullback_pgrpdforgettogrpd_pgrpdforgettogrpd :
    IsPullback
      (Cat.homOf toE''.{v,u})
      (Cat.homOf π'')
      (Cat.homOf π''.{v+1,max u (v+2)})
      (Cat.homOf toU''.{v,u}) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm_sq ?_ ?_ ?_ ?_)
  · intro s
    -- let djka := s.pt.α
    let x : s.pt := sorry
    let y := ((s.fst ≫ Cat.homOf π''.{v+1,max u (v+2)}).obj x)
    let z := Functor.congr_obj s.condition x
    -- let G : (s.snd.obj x).1 := (s.snd.obj x).1
    -- let ljsdlakf := s.condition
    exact {
      obj x := (⟨ ⟨ _, (PointedGroupoid.of (s.snd.obj x).1 sorry) ⟩⟩ : AsSmall.{max u (v+2)} PGrpd) 
      map := sorry
      map_id := sorry
      map_comp := sorry}
    -- -- convert_to s.pt.α ⥤ AsSmall.PGrpd
    
  · sorry
  · sorry
  · sorry

/--
The following square is a pullback

 E'.{v,max u (v+2)} ------- toE' ------> E'.{v+1,u}
        |                                     |
        |                                     |
        π'                                    π'
        |                                     |
        v                                     v
 U'.{v,max u (v+2)}  ------- toU' -----> U'.{v+1,u}

in the category `Grpd.{max u (v+2), max u (v+2)}`
-/
theorem isPullback_π'_π' :
    IsPullback
      toE'.{v,u}
      π'.{v}
      π'.{v+1}
      toU'.{v,u} := sorry

end SmallUniverse

variable {Γ : Ctx.{max u (v+2)}} (A : y(Γ) ⟶ y(U.{v,max u (v+2)}))

/--
The small universes form pullbacks
      y(E.{v}) ------------ toE ---------> y(E.{v+1})
        |                                     |
        |                                     |
      y(π.{v})                              y(π.{v+1})
        |                                     |
        v                                     v
      y(U.{v}) ------------ toU ---------> y(U.{v+1})
-/
theorem isPullback_yπ_yπ :
    IsPullback
      ym(toE.{v,u})
      ym(π.{v, max u (v+2)})
      ym(π.{v+1,max u (v+2)})
      ym(toU.{v,u}) :=
  sorry

end U

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that unlike `GroupoidNaturalModel.base` this is representable,
  but since representables are `max u (v+1)`-large,
  its representable fibers can be larger than itself.

  This natural model is given by pullback of the natural model `base`.
  TODO However, we likely want to use the explicit `Tm = y(E)` and
  `tp = ym(π)` instead of the grothendieck construction provided.
-/
def U1 : NaturalModelBase Ctx.{max u (v+1)} :=
  NaturalModelBase.ofIsPullback base U.isPullback_yπ_tp.{v,u}

def U0 : NaturalModelBase Ctx.{max u (v+2)} :=
  U1.ofIsPullback U.isPullback_yπ_yπ.{v,u}

-- def baseUU : NaturalModelBase Ctx.{max u (v+1)} :=
  -- NaturalModelBase.ofIsPullback base U.isPullback_yπ_yπ.{v,u}

def uHomSeqObjs (i : Nat) (h : i < 3) : NaturalModelBase Ctx.{2} :=
  match i with
  | 0 => U0.{0,2}
  | 1 => U1.{1,2}
  | 2 => base.{2}
  | (n+3) => by omega

def U.asSmallClosedType :
    y(Ctx.chosenTerminal.{max u (v+2)}) ⟶ U1.{v+1, max u (v+2)}.Ty :=
  sorry

def U.isoExtAsSmallClosedType :
    U.{v+1,max u (v+2)} ≅ U1.{v+1,max u (v+2)}.ext U.asSmallClosedType.{v,u} where
  hom := Ctx.ofGrpd.map sorry
  inv := Ctx.ofGrpd.map sorry

def uHom01 : UHom U0.{v, max u (v+2)} U1.{v+1, max u (v+2)} :=
  UHom.ofRepChosenTerminal Ctx.chosenTerminalIsTerminal $
    @UHomRepTerminal.ofTyIsoExt _ _ _ _ _ _
    (isPullbackHom U1.{v+1, max u (v+2)} U.isPullback_yπ_yπ.{v, max u (v+2)})
    sorry
    sorry -- (Functor.mapIso yoneda U.isoExtAsSmallClosedType.{v,u})

/- -- might not need this anymore
def coreAsSmallEquivAsSmallCoreFunctor (C : Type u) [Category.{v} C] :
    Core (AsSmall.{w} C) ⥤ AsSmall.{w} (Core C) where
  obj x := { down := (AsSmall.down.obj x : C) }
  map {x y} f :=
    let x' := (AsSmall.down.obj x : C)
    let y' := (AsSmall.down.obj y : C)
    let f' : x' ⟶ y' := AsSmall.down.map f.hom
    let inv := AsSmall.down.map f.inv
    { down :=
      { hom := AsSmall.down.map f.hom
        inv := AsSmall.down.map f.inv
        inv_hom_id := by rw [← Functor.map_comp]; aesop_cat
        hom_inv_id := by rw [← Functor.map_comp]; aesop_cat}}
-/

def U.asClosedType :
    yoneda.obj Ctx.chosenTerminal ⟶ base.Ty :=
  yonedaCatEquiv.invFun ((CategoryTheory.Functor.const _).obj
    (Grpd.of U'.{v,u}))

def U.isoExtAsClosedTypeFun : Core (AsSmall Grpd)
    ⥤ Groupoidal (yonedaCatEquiv U.asClosedType.{v,u}) where
  obj X := ⟨ ⟨⟨⟩⟩ , X ⟩
  map {X Y} F := ⟨ id _ , F ⟩

def U.isoExtAsClosedTypeInv : Groupoidal (yonedaCatEquiv U.asClosedType.{v,u})
    ⥤ Core (AsSmall Grpd) where
  obj X := X.fiber
  map {X Y} F := F.fiber

def U.isoExtAsClosedType :
    U.{v,u} ≅ base.ext asClosedType.{v,u} where
  hom := Ctx.ofGrpd.map isoExtAsClosedTypeFun
  inv := Ctx.ofGrpd.map isoExtAsClosedTypeInv

def uHom12 : UHom U1.{v,u} base :=
  UHom.ofRepChosenTerminal Ctx.chosenTerminalIsTerminal $
    UHomRepTerminal.ofTyIsoExt _
    (isPullbackHom base U.isPullback_yπ_tp)
    (Functor.mapIso yoneda U.isoExtAsClosedType)

def uHomSeqHomSucc' (i : Nat) (h : i < 2) :
    (uHomSeqObjs i (by omega)).UHom (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => uHom01.{0,2}
  | 1 => uHom12.{1,2}
  | (n+2) => by omega

/--
  The groupoid natural model with two nested representable universes
-/
def uHomSeq : NaturalModelBase.UHomSeq Ctx.{2} where
  length := 2
  objs := uHomSeqObjs
  homSucc' := uHomSeqHomSucc'

end GroupoidNaturalModel

end CategoryTheory

end
