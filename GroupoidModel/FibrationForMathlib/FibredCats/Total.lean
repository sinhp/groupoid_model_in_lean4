/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Basic
import GroupoidModel.FibrationForMathlib.FibredCats.Basic
import GroupoidModel.FibrationForMathlib.FibredCats.CartesianLift


namespace CategoryTheory
open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] [Category E]

abbrev TotalCat {C E : Type*} [Category C] [Category E] (P : E ⥤ C) := Fiber.Total P.obj

prefix:75 " ∫ "  => TotalCat

@[ext]
structure TotalCatHom {P : E ⥤ C} (X Y : ∫ P) where
base : X.base ⟶ Y.base
fiber : X.fiber.1 ⟶ Y.fiber.1
eq : (P.map fiber) ≫ eqToHom (Y.fiber.over) = eqToHom (X.fiber.over) ≫ base

namespace TotalCat

def BasedLiftOf {P : E ⥤ C} {X Y : ∫ P} (g : TotalCatHom X Y) : X.fiber ⟶[g.base] Y.fiber where
  hom := g.fiber
  over := g.eq

@[simp]
lemma over_base {P : E ⥤ C} {X Y : ∫ P} (g : TotalCatHom X Y) :
    P.map g.fiber = eqToHom (X.fiber.over) ≫ g.base ≫ (eqToHom (Y.fiber.over).symm) := by
  simp [← Category.assoc _ _ _, ← g.eq]


instance instCatOfTotal (P : E ⥤ C) : Category (∫ P) where
  Hom X Y := TotalCatHom X Y
  id X := ⟨𝟙 X.base, 𝟙 X.fiber.1, by simp⟩
  comp := @fun X Y Z f g => ⟨f.1 ≫ g.1, f.2  ≫ g.2, by
    rw [map_comp, assoc, over_base g, over_base f]
    slice_lhs 3 4 =>
      rw [eqToHom_trans, eqToHom_refl]
    simp
   ⟩
  id_comp := by intro X Y f; dsimp; congr 1 <;> simp
  comp_id := by intro X Y f; dsimp; congr 1 <;> simp
  assoc := by intro X Y Z W f g h; dsimp; congr 1 <;> simp

end TotalCat

end CategoryTheory
