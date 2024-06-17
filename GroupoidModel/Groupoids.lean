/-
The category Grpd of (small) groupoids, as needed for the groupoid model of HoTT.
See the thesis of Jakob Vidmar:
https://etheses.whiterose.ac.uk/22517/1/Vidmar_J_Mathematics_PhD_2018.pdf
for a modern exposition of the groupoid model, including polynomial functors and W-types.
-/
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Bicategory.Strict

import Mathlib.CategoryTheory.Groupoid

universe u v

namespace CategoryTheory

noncomputable section

/-
Modified from: mathlib4/Mathlib/CategoryTheory/Category
/Cat.lean
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

/-!
# Category of groupoids

This file contains the definition of the category `Grpd` of all (small) groupoids.
In this category objects are groupoids and
morphisms are functors between these as categories.

## Implementation notes

Though `Grpd` is not a concrete category, we use `bundled` to define
its carrier type.
-/

-- SH: The development below is not necessary, we alrady have the category of groupoids in mathlib.
-- See Mathlib/CategoryTheory/Category/Grpd.lean

-- intended to be used with explicit universe parameters
/-- Category of groupoids. -/
@[nolint checkUnivs]
def Grpd := Bundled Category.{v, u}
--set_option linter.uppercaseLean3 false in
--#align category_theory.Cat CategoryTheory.Cat

namespace Grpd

instance : Inhabited Grpd :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

-- Porting note: maybe this coercion should be defined to be `objects.obj`?
instance : CoeSort Grpd (Type u) :=
  ⟨Bundled.α⟩

instance str (G : Grpd.{v, u}) : Groupoid.{v, u} G :=
  Bundled.str G
-- set_option linter.uppercaseLean3 false in
-- #align category_theory.Cat.str CategoryTheory.Cat.str

/-- Construct a bundled `Grpd` from the underlying type and the typeclass. -/
def of (G : Type u) [Category.{v} C] : Groupoid.{v, u} :=
  Bundled.of C
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.of CategoryTheory.Cat.of

/-- Bicategory structure on `Grpd` -/
instance bicategory : Bicategory.{max v u, max v u} Cat.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  homCategory := fun _ _ => Functor.category
  whiskerLeft {C} {D} {E} F G H η := whiskerLeft F η
  whiskerRight {C} {D} {E} F G η H := whiskerRight η H
  associator {A} {B} {C} D := Functor.associator
  leftUnitor {A} B := Functor.leftUnitor
  rightUnitor {A} B := Functor.rightUnitor
  pentagon := fun {A} {B} {C} {D} {E}=> Functor.pentagon
  triangle {A} {B} {C} := Functor.triangle
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.bicategory CategoryTheory.Cat.bicategory

/-- `Cat` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict Cat.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.bicategory.strict CategoryTheory.Cat.bicategory.strict

/-- Category structure on `Cat` -/
instance category : LargeCategory.{max v u} Cat.{v, u} :=
  StrictBicategory.category Cat.{v, u}
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.category CategoryTheory.Cat.category

@[simp]
theorem id_map {C : Cat} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
  Functor.id_map f
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.id_map CategoryTheory.Cat.id_map

@[simp]
theorem comp_obj {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  Functor.comp_obj F G X
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.comp_obj CategoryTheory.Cat.comp_obj

@[simp]
theorem comp_map {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) :=
  Functor.comp_map F G f
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.comp_map CategoryTheory.Cat.comp_map

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := F.obj
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.objects CategoryTheory.Cat.objects

-- Porting note: this instance was needed for CategoryTheory.Category.Cat.Limit
instance (X : Cat.{v, u}) : Category (objects.obj X) := (inferInstance : Category X)

section

attribute [local simp] eqToHom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom
  inverse := γ.inv
  unitIso := eqToIso <| Eq.symm γ.hom_inv_id
  counitIso := eqToIso γ.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.equiv_of_iso CategoryTheory.Cat.equivOfIso

end

end Cat

/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map := fun {X} {Y} f => by
    dsimp
    exact Discrete.functor (Discrete.mk ∘ f)
  map_id X := by
    apply Functor.ext
    · intro X Y f
      cases f
      simp only [id_eq, eqToHom_refl, Cat.id_map, Category.comp_id, Category.id_comp]
      apply ULift.ext
      aesop_cat
    · aesop_cat
  map_comp f g := by apply Functor.ext; aesop_cat
set_option linter.uppercaseLean3 false in
#align category_theory.Type_to_Cat CategoryTheory.typeToCat

instance : Functor.Faithful typeToCat.{u} where
  map_injective {_X} {_Y} _f _g h :=
    funext fun x => congr_arg Discrete.as (Functor.congr_obj h ⟨x⟩)

instance : Functor.Full typeToCat.{u} where
  map_surjective F := ⟨Discrete.as ∘ F.obj ∘ Discrete.mk, by
    apply Functor.ext
    · intro x y f
      dsimp
      apply ULift.ext
      aesop_cat
    · rintro ⟨x⟩
      apply Discrete.ext
      rfl⟩

end CategoryTheory
