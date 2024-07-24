/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import GroupoidModel.FibrationForMathlib.FibredCats.Basic

/-!
# Displayed Category Of A Functor

Given a type family `F : C → Type*` on a category `C` we then define the displayed category `Display F`.

For a functor `P : E ⥤ C`, we define the structure `BasedLift f src tgt` as the type of
lifts in `E` of a given morphism `f  : c ⟶ d` in `C` which have a fixed source `src` and a
fixed target `tgt` in the fibers of `c` and `d` respectively. We call the elements of
`BasedLift f src tgt` based-lifts of `f` with source `src` and target `tgt`.

We also provide various useful constructors for based-lifts:
* `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
  tautological based-lift of its image `P.map g`.
* `BasedLift.id` and `BasedLift.comp` provide the identity and composition of
  based-lifts, respectively.
* We can cast a based-lift along an equality of the base morphisms using the equivalence `BasedLift.cast`.

We provide the following notations:
* `X ⟶[f] Y` for `DisplayStruct.HomOver f x y`
* `f ≫ₗ g` for `DisplayStruct.comp_over f g`

We show that for a functor `P`, the type `BasedLift P` induces a display category structure on the fiber family `fun c => P⁻¹ c`.

-/

set_option autoImplicit true

namespace CategoryTheory

open Category

variable {C : Type*} [Category C] (F : C → Type*)

/-- Cast an element of a fiber along an equality of the base objects. -/
def fiberCast {I I' : C} (w : I = I') (X : F I)  : F I' :=
  w ▸ X

/-- Transporting a morphism `f : I ⟶ J` along equalities `w : I = I'` and  `w' : J = J'`.
Note: It might be a good idea to add this to eqToHom file. -/
@[simp]
def eqToHomMap {I I' J J' : C} (w : I = I') (w' : J = J') (f : I ⟶ J) : I' ⟶ J' :=
  w' ▸ (w ▸ f)
--eqToHom (w.symm) ≫ f ≫ eqToHom w'

@[simp]
def eqToHomMapId {I I' : C} (w : I = I') : w ▸ 𝟙 I = 𝟙 I' := by
  subst w
  rfl

@[simp]
lemma eqToHomMap_naturality {I I' J J' : C} {w : I = I'} {w' : J = J'} (f : I ⟶ J) :
    eqToHom w ≫ eqToHomMap w w' f = f ≫ eqToHom w' := by
  subst w' w
  simp

@[simp]
lemma fiber_cast_trans (X : F I) {w : I = I'} {w' : I' = I''} {w'' : I = I''} :
    w' ▸ (w ▸ X) = w'' ▸ X := by
  subst w'
  rfl

lemma fiber_cast_cast (X : F I) {w : I = I'} {w' : I' = I} : w' ▸ w ▸ X = X := by
  simp only [fiber_cast_trans]

class DisplayStruct where
  /-- The type of morphisms indexed over morphisms of `C`. -/
  HomOver : ∀ {I J : C}, (I ⟶ J) → F I → F J → Type*
  /-- The identity morphism overlying the identity morphism of `C`. -/
  id_over : ∀ {I : C} (X : F I), HomOver (𝟙 I) X X
  /-- Composition of morphisms overlying composition of morphisms of `C`. -/
  comp_over : ∀ {I J K : C} {f₁ : I ⟶ J} {f₂ : J ⟶ K} {X : F I} {Y : F J} {Z : F K}, HomOver f₁ X Y → HomOver f₂ Y Z → HomOver (f₁ ≫ f₂) X Z

notation X " ⟶[" f "] " Y => DisplayStruct.HomOver f X Y
notation " 𝟙ₗ " => DisplayStruct.id_over
scoped infixr:80 "  ≫ₗ "  => DisplayStruct.comp_over

variable {F}

class DisplayStruct.CastEq [DisplayStruct F] {I J : C} {f f' : I ⟶ J} {X : F I} {Y : F J}
    (g : X ⟶[f] Y) (g' : X ⟶[f'] Y) : Prop where
  base_eq : f = f'
  cast_eq : base_eq ▸ g = g'

scoped infixr:50 " =▸= "  => DisplayStruct.CastEq

variable (F)

class Display extends DisplayStruct F where
  id_comp_cast {I J : C} {f : I ⟶ J} {X : F I} {Y : F J}
  (g : X ⟶[f] Y) : (𝟙ₗ X) ≫ₗ g =▸= g := by aesop_cat
  comp_id_cast {I J : C} {f : I ⟶ J} {X : F I} {Y : F J}
  (g : X ⟶[f] Y) : g ≫ₗ (𝟙ₗ Y) =▸= g := by aesop_cat
  assoc_cast {I J K L : C} {f₁ : I ⟶ J} {f₂ : J ⟶ K} {f₃ : K ⟶ L} {X : F I}
  {Y : F J} {Z : F K} {W : F L} (g₁ : X ⟶[f₁] Y)
  (g₂ : Y ⟶[f₂] Z) (g₃ : Z ⟶[f₃] W) :
  (g₁ ≫ₗ g₂) ≫ₗ g₃ =▸= (g₁ ≫ₗ (g₂ ≫ₗ g₃)) := by aesop_cat

attribute [simp] Display.id_comp_cast Display.comp_id_cast Display.assoc_cast
attribute [trans] Display.assoc_cast

namespace HomOver

open Display

variable {F}
variable [Display F] {I J : C}

@[simp]
def cast {f f' : I ⟶ J} {X : F I} {Y : F J} (w : f = f') (g : X ⟶[f] Y) : X ⟶[f'] Y :=
  w ▸ g

@[simp]
lemma cast_trans {f f' f'' : I ⟶ J} {X : F I} {Y : F J} {w : f = f'} {w' : f' = f''}
    (g : X ⟶[f] Y) : w' ▸ w ▸ g = (w.trans w') ▸ g := by
  subst w'
  rfl

lemma cast_unique {f f' : I ⟶ J} {X : F I} {Y : F J} {w w' : f = f'} (g : X ⟶[f] Y) :
    w ▸ g = w' ▸ g := by
  rfl

lemma cast_cast {f f' : I ⟶ J} {X : F I} {Y : F J} (w : f = f') (w' : f' = f) (g : X ⟶[f'] Y) :
    w' ▸ w ▸ g = g := by
  simp only [cast_trans] --subst w'; rfl

lemma comp_id_eq_cast_id_comp {f : I ⟶ J} {X : F I} {Y : F J} (g : X ⟶[f] Y) :
    g ≫ₗ 𝟙ₗ Y =▸= (𝟙ₗ X  ≫ₗ g) where
  base_eq := (comp_id f).trans (id_comp f).symm
  cast_eq := by sorry -- rw [comp_id_cast]

    --by
  --use (comp_id f).trans (id_comp f).symm
  --simp only [comp_id_cast, cast, id_comp_cast, comp_id, cast_trans]

/-- `EqToHom w X` is a hom-over `eqToHom w` from `X` to `w ▸ X`. -/
def eqToHom (w : I = I') (X : F I) : X ⟶[eqToHom w] (w ▸ X) := by
  subst w
  exact 𝟙ₗ X

@[simp]
def eqToHomMap (w : I = I') (w' : J = J') {f : I ⟶ J} {X : F I } {Y : F J} (g : X ⟶[f] Y) :
    (w ▸ X) ⟶[eqToHomMap w w' f] (w' ▸ Y) := by
  subst w
  subst w'
  exact g

@[simp]
def eqToHomMapId (w : I = I') {X : F I } {Y : F I} (g : X ⟶[𝟙 I] Y) :
    (w ▸ X) ⟶[𝟙 I'] (w ▸ Y) := by
  subst w
  exact g

lemma eqToHom_naturality {X : F I} {Y : F J} (w : I = I') (w' : J = J') (f : I ⟶ J) (g : X ⟶[f] Y) :
    g ≫ₗ eqToHom w' Y = cast (eqToHomMap_naturality f) (eqToHom w X ≫ₗ eqToHomMap w w' g)  := by
  subst w' w
  simp only [eqToHom, comp_id_eq_cast_id_comp, cast]
  -- rfl
  sorry

@[simps!]
def castEquiv {I J : C} {f f' : I ⟶ J} {X : F I} {Y : F J} (w : f = f') : (X ⟶[f] Y) ≃ (X ⟶[f'] Y) where
  toFun := fun g ↦ w ▸ g
  invFun := fun g ↦ w.symm ▸ g
  left_inv := by aesop_cat
  right_inv := by aesop_cat

#check HEq

end HomOver
