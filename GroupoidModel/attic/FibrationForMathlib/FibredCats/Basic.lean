/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sigma.Basic
import GroupoidModel.FibrationForMathlib.Data.Fiber

/-!
# Basic

We provide the category instance on the fibers of a functor.
We show that for a functor `P`, the fiber of the opposite functor
`P.op` are isomorphic to the opposites of the fiber categories of `P`.

We provide the following notations:
* `P ⁻¹ c` for the fiber of `P` at `c`.
-/

set_option autoImplicit true

namespace CategoryTheory

open Category Opposite Functor Fiber

/-- The fiber of a functor at a given object in the base category. -/
abbrev FiberCat {C E : Type*} [Category C] [Category E] (P : E ⥤ C) (c : C) := Fiber P.obj c
notation:75 (name := FiberCat_stx) P " ⁻¹ " c => FiberCat P c

namespace FiberCat
variable {C E : Type*} [Category C] [Category E] {P : E ⥤ C}

/-- The category structure on the fibers of a functor. -/
instance instCategoryFiber {c : C} : Category (P ⁻¹ c) where
  Hom x y := { g : (x : E) ⟶ (y : E) // P.map g = eqToHom (over_eq x y) }
  id x := ⟨𝟙 (x : E), by simp only [Functor.map_id, eqToHom_refl]⟩
  comp g h := ⟨g.1 ≫ h.1, by simp only [Functor.map_comp, Fiber.over, eqToHom_trans]⟩

lemma id_coe {c : C} (x : P⁻¹ c) : (𝟙 x : x ⟶ x).val = 𝟙 (x : E) := rfl

lemma comp_coe {c : C} {x y z : P⁻¹ c} (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp, aesop forward safe]
lemma fiber_hom_over {c: C} (x y : P⁻¹ c) (g : x ⟶ y) :
P.map g.1 = eqToHom (Fiber.over_eq x y) := g.2

/-- The forgetful functor from a fiber to the domain category. -/
@[simps]
def forget {c : C} : (P⁻¹ c) ⥤ E where
  obj := fun x => x
  map := @fun x y f => f.1

lemma fiber_comp_obj {c: C} (x y z : P⁻¹ c) (f: x ⟶ y) (g: y ⟶ z) :
(f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp]
lemma fiber_comp_obj_eq {c: C} {x y z : P⁻¹ c} {f: x ⟶ y} {g: y ⟶ z} {h : x ⟶ z} :
(f ≫ g = h) ↔  f.1 ≫ g.1  = h.1 := by
  constructor
  · intro H; cases H; rfl
  · intro H; cases f; cases g; cases h; simp at H; subst H; rfl

@[simp]
lemma fiber_id_obj {c: C} (x : P⁻¹ c) : (𝟙 x : x ⟶ x).val = 𝟙 (x : E) := rfl

/- Two morphisms in a fiber P⁻¹ c are equal if their underlying morphisms in E are equal. -/
lemma hom_ext {c : C} {x y : P⁻¹ c} {f g : x ⟶ y} (h : f.1 = g.1) : f = g := by
  cases f; cases g; simp at h; subst h; rfl

@[simps]
lemma is_iso {c : C} {x y : P⁻¹ c} (f : x ⟶ y) : IsIso f ↔ IsIso f.1 :=
  ⟨fun h ↦ (asIso f) |> forget.mapIso |> Iso.isIso_hom,
    fun h ↦ ⟨⟨⟨inv f.1, by simp⟩, by simp⟩⟩⟩

namespace Op

@[simp]
lemma obj_over (x : P.op ⁻¹ (op c)) : P.obj (unop (x.1)) = c := by
cases' x with e h
simpa [Functor.op] using h

/-- The fibres of the opposite functor `P.op` are in bijection with the the fibres of `P`.  -/
@[simps]
def equiv (c : C) : (P.op ⁻¹ (op c)) ≃ (P⁻¹ c) where
  toFun := fun x =>  (⟨unop x.1, by rw [obj_over] ⟩)
  invFun := fun x => ⟨op x.1 , by simp only [Functor.op_obj, unop_op, Fiber.over]⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The fibres of the opposite functor `P.op` are isomorphic
to the the fibres of `P`.  -/
@[simps]
def iso (c : C) : (P.op ⁻¹ (op c)) ≅ (P⁻¹ c) where
  hom := fun x =>  (⟨unop x.1, by rw [obj_over] ⟩)  -- ⟨x.obj, by simp⟩
  inv := fun x => ⟨op x.1 , by simp only [Functor.op_obj, unop_op, Fiber.over]⟩  -- aesop generated

@[simp]
lemma unop_op_map  {c : C} {x y : (P.op) ⁻¹ (op c)} (f : x ⟶ y) :
    unop (P.op.map f.1) = P.map f.1.unop := rfl

@[simp]
lemma op_map_unop  {c : C} {x y : (P ⁻¹ c)ᵒᵖ} (f : x ⟶ y) : P.op.map (f.unop.1.op) = (P.map (f.unop.1)).op := rfl

/-- The fiber categories of the opposite functor `P.op` are isomorphic
to the opposites of the fiber categories of `P`. -/
def Iso (P : E ⥤ C) (c : C) : Cat.of (P.op ⁻¹ (op c) ) ≅ Cat.of ((P⁻¹ c)ᵒᵖ)  where
  hom := {
    obj := fun x => op (⟨unop x.1, by rw [obj_over] ⟩)
    map := @fun x y f => ⟨f.1.unop, by dsimp; rw [← (unop_op_map f), f.2]; apply eqToHom_unop ⟩
  }
  inv := {
    obj := fun x => ⟨op x.unop.1 , by simp only [Functor.op_obj, unop_op, Fiber.over]⟩
    map := @fun x y f => ⟨(f.unop.1).op , by dsimp;  simp [Functor.op_map]⟩
  }
  hom_inv_id := rfl
  inv_hom_id := rfl

end Op
end FiberCat

end CategoryTheory
