/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Preorder
import GroupoidModel.FibrationForMathlib.Displayed.Fiber

import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.PenroseDiagram
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel

/-!
# Widget test for fibred category theory
-/

namespace CategoryTheory

open Category CategoryTheory ProofWidgets

variable {C : Type*} [Category C] (F : C → Type*)

show_panel_widgets [local GoalTypePanel]

/-- Transporting a morphism `f : I ⟶ J` along equalities `w : I = I'` and  `w' : J = J'`.
Note: It might be a good idea to add this to eqToHom file. -/
@[simp]
def eqToHomMap {I I' J J' : C} (w : I = I') (w' : J = J') (f : I ⟶ J) : I' ⟶ J' :=
  w' ▸ (w ▸ f) --eqToHom (w.symm) ≫ f ≫ eqToHom w'

/--
The diagram below commutes:
```
    I --eqToHom w --> J
    |                 |
  f |                 | eqToHomMap w w' f
    v                 v
    I' --eqToHom w'-> J'
```
-/
@[simp]
lemma eqToHomMap_naturality' {I I' J J' : C} {w : I = I'} {w' : J = J'} (f : I ⟶ J) :
    eqToHom w ≫ eqToHomMap w w' f = f ≫ eqToHom w' := by
  subst w' w
  simp

/-- Transporting a morphism `f : I ⟶ J` along equalities `w : I = I'` and  `w' : J = J'`.
Note: It might be a good idea to add this to eqToHom file. -/
@[simp]
def eqToHomMap' {I I' J J' : C} (w : I = I') (w' : J = J') (f : I ⟶ J) : I' ⟶ J' := by
  let a : I' ⟶ J := eqToHom (w.symm) ≫ f
  let b : I' ⟶ J' := a ≫ eqToHom w'
  exact b

class DisplayStruct where
  /-- The type of morphisms indexed over morphisms of `C`. -/
  HomOver : ∀ {I J : C}, (I ⟶ J) → F I → F J → Type*
  /-- The identity morphism overlying the identity morphism of `C`. -/
  id_over : ∀ {I : C} (X : F I), HomOver (𝟙 I) X X
  /-- Composition of morphisms overlying composition of morphisms of `C`. -/
  comp_over : ∀ {I J K : C} {f₁ : I ⟶ J} {f₂ : J ⟶ K} {X : F I} {Y : F J}
  {Z : F K}, HomOver f₁ X Y → HomOver f₂ Y Z → HomOver (f₁ ≫ f₂) X Z

notation X " ⟶[" f "] " Y => DisplayStruct.HomOver f X Y
notation " 𝟙ₗ " => DisplayStruct.id_over
scoped infixr:80 "  ≫ₗ "  => DisplayStruct.comp_over

class Display extends DisplayStruct F where
  id_comp_cast {I J : C} {f : I ⟶ J} {X : F I} {Y : F J}
  (g : X ⟶[f] Y) : (𝟙ₗ X) ≫ₗ g = (id_comp f).symm ▸ g := by aesop_cat
  comp_id_cast {I J : C} {f : I ⟶ J} {X : F I} {Y : F J}
  (g : X ⟶[f] Y) : g ≫ₗ (𝟙ₗ Y) = ((comp_id f).symm ▸ g) := by aesop_cat
  assoc_cast {I J K L : C} {f₁ : I ⟶ J} {f₂ : J ⟶ K} {f₃ : K ⟶ L} {X : F I}
  {Y : F J} {Z : F K} {W : F L} (g₁ : X ⟶[f₁] Y)
  (g₂ : Y ⟶[f₂] Z) (g₃ : Z ⟶[f₃] W) :
  (g₁ ≫ₗ g₂) ≫ₗ g₃ = (assoc f₁ f₂ f₃).symm ▸ (g₁ ≫ₗ (g₂ ≫ₗ g₃)) := by aesop_cat

attribute [simp] Display.id_comp_cast Display.comp_id_cast Display.assoc_cast
attribute [trans] Display.assoc_cast

variable {E : Type*} [Category E] {P : E ⥤ C}

/-- The type of lifts of a given morphism in the base
with fixed source and target in the Fibres of the domain and codomain respectively.-/
structure BasedLift {I J : C} (f : I ⟶ J) (X : P⁻¹ I) (Y : P⁻¹ J) where
  hom : (X : E) ⟶ (Y : E)
  over_eq : (P.map hom) ≫ eqToHom (Y.2) = eqToHom (X.2) ≫ f

/--
The structure of based-lifts up to an isomorphism of the domain objects in the base.
```              g
     X -------------------->    Y
     _                          -
     |            |             |
     |            |             |
     v            v             v
P.obj X ---------> I ---------> J
           ≅             f
```
-/
structure EBasedLift {I J : C} (f : I ⟶ J) (X : EFiber P I) (Y : EFiber P J) where
  hom : X.obj ⟶ Y.obj
  iso_over_eq : (P.map hom) ≫ Y.iso.hom = X.iso.hom ≫ f := by aesop_cat

attribute [reassoc] EBasedLift.iso_over_eq

namespace BasedLift

variable {E : Type*} [Category E] {P : E ⥤ C}

@[simp]
lemma over_base {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} (g : BasedLift f X Y) :
    P.map g.hom = eqToHom (X.2) ≫ f ≫ (eqToHom (Y.2).symm)  := by
  simp only [← Category.assoc _ _ _, ← g.over_eq, assoc, eqToHom_trans, eqToHom_refl, comp_id]

/-- The identity based-lift. -/
@[simps!]
def id {I : C} (X : P⁻¹ I) : BasedLift (𝟙 I) X X := ⟨𝟙 _, by simp⟩

/-- The composition of based-lifts -/
@[simps]
def comp {I J K : C} {f₁ : I ⟶ J} {f₂ : J ⟶ K} {X : P⁻¹ I} {Y : P⁻¹ J} {Z : P⁻¹ K}
    (g₁ : BasedLift f₁ X Y) (g₂ : BasedLift f₂ Y Z) :
    BasedLift (f₁ ≫ f₂) X Z := by
  with_panel_widgets [SelectionPanel]
  refine ⟨g₁.hom ≫ g₂.hom, ?_⟩
  have := by
    calc
      P.map (g₁.hom ≫ g₂.hom) = P.map g₁.hom ≫ P.map g₂.hom := by
        rw [P.map_comp]
      _   = (eqToHom (X.2) ≫ f₁ ≫ eqToHom (Y.2).symm) ≫ P.map g₂.hom := by
        rw [g₁.over_base]
      _   = eqToHom (X.2) ≫ f₁ ≫ (eqToHom (Y.2).symm ≫ P.map g₂.hom) := by
        simp only [assoc]
      _   = eqToHom (X.2) ≫ f₁ ≫ (eqToHom (Y.2).symm ≫ eqToHom (Y.2) ≫ f₂ ≫ eqToHom (Z.2).symm) := by
        rw [g₂.over_base]
  simp [this]

@[simps!]
def cast {I J : C} {f f' : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} (w : f = f')
  (g : BasedLift f X Y) : BasedLift f' X Y := ⟨g.hom, by rw [←w, g.over_eq]⟩

end BasedLift
namespace EBasedLift

@[simp]
lemma iso_over_eq' {I J : C} {f : I ⟶ J} {X : EFiber P I} {Y : EFiber P J} (g : EBasedLift f X Y) :
    P.map g.hom = X.iso.hom ≫ f ≫ Y.iso.inv := by
  simpa using g.iso_over_eq_assoc (Y.iso.inv)

def id {I : C} (X : EFiber P I) : EBasedLift (𝟙 I) X X where
  hom := 𝟙 _

def comp {I J K : C} {f₁ : I ⟶ J} {f₂ : J ⟶ K} {X : EFiber P I} {Y : EFiber P J} {Z : EFiber P K}
    (g₁ : EBasedLift f₁ X Y) (g₂ : EBasedLift f₂ Y Z) :
    EBasedLift (f₁ ≫ f₂) X Z := by
  with_panel_widgets [SelectionPanel]
  refine ⟨g₁.hom ≫ g₂.hom, ?_⟩
  have := by
    calc
      P.map (g₁.hom ≫ g₂.hom) = P.map (g₁.hom) ≫ P.map (g₂.hom) := by rw [P.map_comp]
      _   = (X.iso.hom ≫ f₁ ≫ Y.iso.inv) ≫ P.map (g₂.hom) := by rw [g₁.iso_over_eq']
      _   = X.iso.hom ≫ f₁ ≫ (Y.iso.inv ≫ P.map (g₂.hom)) := by
        simp only [iso_over_eq', assoc, Iso.inv_hom_id_assoc]
      _   = X.iso.hom ≫ f₁ ≫ (Y.iso.inv ≫ Y.iso.hom ≫ f₂ ≫ Z.iso.inv) := by rw [g₂.iso_over_eq']
      _   = X.iso.hom ≫ f₁ ≫ (𝟙 J ≫ f₂ ≫ Z.iso.inv) := by rw [Iso.inv_hom_id_assoc, id_comp]
      _   = X.iso.hom ≫ f₁ ≫ f₂ ≫ Z.iso.inv := by rw [id_comp]
  simp [this]

end EBasedLift

end CategoryTheory
