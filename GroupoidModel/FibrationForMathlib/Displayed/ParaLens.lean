/-
Copyright (c) 2024 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Algebra.PUnitInstances

/-!
# Para construction

The Para construction associates to a monoidal category `C` a bicategory of parametric morphisms
in `C`. A morphism in `Para C` consists of a paramater `P : C` and a morphism `f : P ⊗ X ⟶ Y` in
`C`. We call `f` a `P`-parametrized morphism from `X` to `Y`.

The composition of of morphisms in `Para C` is weakly unital and weakly associatve and this makes
`Para C` a bicategory.
-/

open CategoryTheory Category MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

namespace MonoidalCategory

variable (C)

abbrev Para := C

namespace Para

variable {C}

/-- A morphism in `Para C` from `X` to `Y` consists of a paramater `P : C` and `f : P ⊗ X ⟶ Y`. -/
structure Hom (X Y : Para C) where
/-- The paramter -/
  par : C
/-- The parametrized morphism -/
  par_hom : X ⊗ par ⟶ Y

/-- The identity parametrized morphism from `X` to `X`. -/
@[simps]
def id (X : Para C) : Hom X X := ⟨𝟙_ C, (ρ_ X).hom⟩

/-- The composition of parametrized morphisms. -/
@[simps]
def comp {X Y Z : Para C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.1 ⊗ g.1, (α_ _ _ _).inv ≫ (f.2 ▷ g.1) ≫ g.2⟩

namespace Hom

instance inhabited {X : Para C} : Inhabited (Hom X X) := ⟨id X⟩

-- structure homCategory {X Y : Para C} (f f' : Hom X Y) where
--   α : f.par ⟶ f'.par
--   w : (X ◁ α) ≫ f'.hom = f.hom := by aesop_cat

instance category (X Y : Para C) : Category (Para.Hom X Y) where
  Hom f f' := {h : f.par ⟶ f'.par // (X ◁ h) ≫ f'.par_hom = f.par_hom}
  id f := ⟨𝟙 _, by simp only [MonoidalCategory.whiskerLeft_id, id_comp]⟩
  comp := @fun f f' f'' α α' =>
    ⟨α.1 ≫ α'.1, by simp only [MonoidalCategory.whiskerLeft_comp, assoc, α'.2, α.2]⟩

@[simp]
lemma hom_def {X Y : Para C} {f f' : Hom X Y} {α : f ⟶ f'} :
    (X ◁ α.1) ≫ f'.par_hom = f.par_hom := by
  exact α.2

@[ext]
theorem ext {X Y : Para C} {f g : Hom X Y} (h : f.par = g.par)
    (w : f.par_hom = eqToHom (by rw [h]) ≫ g.par_hom) : f = g :=
  by
    cases f
    cases g
    dsimp at h
    subst h
    aesop


end Hom


-- lemma whiskerLeft {X Y Z : Para C} (f : X ⟶ Y) (g g' : Y ⟶ Z) (α : g ⟶ g') :
--     f ≫ g ⟶ f ≫ g' :=
--   by
--     sorry

#check comp_par_hom

instance bicategory : Bicategory (Para C) where
  Hom X Y := Para.Hom X Y
  id X := Para.id X
  comp := Para.comp
  homCategory X Y := inferInstanceAs (Category (Para.Hom X Y))
  whiskerLeft := @fun X Y Z f g g' α =>
    ⟨ f.par ◁ α.1, by simp [comp_par_hom]; sorry   ⟩

  whiskerRight := _
  associator := _
  leftUnitor := _
  rightUnitor := _
  whiskerLeft_id := _
  whiskerLeft_comp := _
  id_whiskerLeft := _
  comp_whiskerLeft := _
  id_whiskerRight := _
  comp_whiskerRight := _
  whiskerRight_id := _
  whiskerRight_comp := _
  whisker_assoc := _
  whisker_exchange := _
  pentagon := _
  triangle := _



  -- Hom X Y := Para.Hom X Y
  -- id X := Para.id X
  -- comp := Para.comp
  -- whiskerLeft X Y Z f := sorry
  -- whiskerRight := sorry
  -- associator := sorry
  -- leftUnitor := sorry
  -- rightUnitor := sorry


end Para

end MonoidalCategory
