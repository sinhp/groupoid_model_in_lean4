/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import GroupoidModel.FibrationForMathlib.Displayed.Fibre
import GroupoidModel.FibrationForMathlib.Displayed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Cartesian lifts

There are also typeclasses `Display.Cartesian` and `Display.CoCartesian`
carrying data witnessing that a given lift is cartesian and cocartesian, respectively.

Specialized to the display category structure of a functor `P : E ⥤ C`,
we obtain the class `CartMor` of cartesian morphisms in `E`.
The type `CartMor P` is defined in terms of the predicate `isCartesianMorphism`.

In this file we shall refer to a hom-over `g : X ⟶[f] Y` as a "lift" of
`f : I ⟶ J` to `X : F I` and `Y : F J`, since the map application of cartesianness concerns
the display structure of a functor `P : E ⥤ C`, where `I J : C` are objects of the base category `C`.

We prove the following closure properties of the class `CartMor` of cartesian morphisms:
- `cart_id` proves that the identity morphism is cartesian.
- `cart_comp` proves that the composition of cartesian morphisms is cartesian.
- `cart_iso_closed` proves that the class of cartesian morphisms is closed under isomorphisms.
- `cart_pullback` proves that, if `P` preserves pullbacks, then
the pullback of a cartesian morphism is cartesian.

`instCatCart` provides a category instance for the class of cartesian morphisms,
and `Cart.forget` provides the forgetful functor from the category of cartesian morphisms
to the domain category `E`.

-/

set_option autoImplicit true

namespace CategoryTheory

open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] {F : C → Type*} [Display F]

namespace Display

variable {I J : C} {f : I ⟶ J} {X : F I} {Y : F J}

/-- A hom-over `g : X ⟶[f] Y` is cartesian if for every morphism `u : K ⟶ I`
in the base and every hom-over `g' : Z ⟶[u ≫ f] Y` over the composite
 `u ≫ f`, there is a unique morphism `k : Z ⟶[u] X` over `u` such that
 `k ≫ g = g'`.
```
       _ _ _ _ _ _ _ _ _ _ _
      /         [g']        \
     |                      v
     Z - - - - > X --------> Y
     _   ∃![k]   _   [g]     _
     |           |           |
     |           |           |
     v           v           v

     K --------> I --------> J
          u            f
```
-/
class Cartesian (g : X ⟶[f] Y) where
  uniq_lift : ∀ ⦃K : C⦄ ⦃Z : F K⦄ (u : K ⟶ I) (g' : Z ⟶[u ≫ f] Y),
  Unique {k : Z ⟶[u] X // (k ≫ₗ g) = g'}

/-- A morphism `g : X ⟶[f] Y` over `f` is cocartesian if for all morphisms `u` in the
base and `g' : X ⟶[f ≫ u] Z` over the composite `f ≫ u`, there is a unique morphism
`k : Y ⟶[u] Z` over `u` such that `g ≫ k = g'`.
```
       _ _ _ _ _ _ _ _ _ _ _
      /         [g']        \
     |                      v
     X ------- > Y - - - - > Z
     _   [g]     _   ∃![k]   _
     |           |           |
     |           |           |
     v           v           v

     I --------> J --------> K
          f            u
```
-/
class CoCartesian (g : X ⟶[f] Y) where
  uniq_lift : ∀ ⦃K : C⦄ ⦃Z : F K⦄ (u : J ⟶ K) (g' : X ⟶[f ≫ u] Z),
  Unique {k : Y ⟶[u] Z // (g ≫ₗ k) = g'}

namespace Cartesian

open Display

variable (g : X ⟶[f] Y) [Cartesian g] {K : C} {Z : F K}

/-- `gap g u g'` is the canonical map from a lift `g' : Z ⟶[u ≫ f] X` to a
cartesian lift `g` of `f`. -/
def gap (u : K ⟶ I) (g' : Z ⟶[u ≫ f] Y) : Z ⟶[u] X :=
  (Cartesian.uniq_lift (g:= g) (Z:= Z) u g').default.val

/-- A variant of `gaplift` for `g' : Z ⟶[f'] X` with casting along
`f' = u ≫ f` baked into the definition. -/
def gapCast (u : K ⟶ I) {f' : K ⟶ J} (g' : Z ⟶[f'] Y) (w : f' = u ≫ f) :
  Z ⟶[u] X :=
  (Cartesian.uniq_lift (g:= g) (Z:= Z) u (w ▸ g')).default.val

@[simp]
lemma gap_cast (u : K ⟶ I) {f' : K ⟶ J} (g' : Z ⟶[f'] Y)
    (w : f' = u ≫ f) : gapCast g u g' w = gap g u (w ▸ g') := by
  rfl

/-- The composition of the gap lift and the cartesian hom-over is the given hom-over. -/
@[simp]
lemma gap_prop (u : K ⟶ I) (g' : Z ⟶[u ≫ f] Y) :
    ((gap g u g') ≫ₗ g) = g' :=
  (Cartesian.uniq_lift (f:= f) (g:= g) (Z := Z) u g').default.property

/-- The uniqueness part of the universal property of the gap lift. -/
@[simp]
lemma gaplift_uniq {u : K ⟶ I} (g' : Z ⟶[u ≫ f] Y) (v : Z ⟶[u] X)
  (hv : v ≫ₗ g = g') : v = gap (g:= g) u g' := by
  simp [gap]
  rw [← (Cartesian.uniq_lift u g').uniq ⟨v,hv⟩]

/-- The identity hom-over is cartesian. -/
instance instId {X : F I} : Cartesian (𝟙ₗ X) where
  uniq_lift := fun K Z u g' => {
    default := ⟨(comp_id u) ▸ g', by simp⟩
    uniq := by aesop
  }

/-- Cartesian based-lifts are closed under composition. -/
instance instComp {X : F I} {Y : F J} {Z : F K} {f₁ : I ⟶ J} {f₂ : J ⟶ K}
  (g₁ : X ⟶[f₁] Y) [Cartesian g₁] (g₂ : Y ⟶[f₂] Z) [Cartesian g₂] :
  Cartesian (g₁ ≫ₗ g₂) where
  uniq_lift := fun I' W u g' => {
    default := ⟨ gap g₁ u (gap g₂ (u ≫ f₁) (assoc u f₁ f₂ ▸ g')), by
      rw [← Display.cast_assoc_symm, gap_prop g₁ _ _, gap_prop g₂ _ _]
      simp ⟩
    uniq := by
      intro ⟨l, hl⟩
      simp
      apply gaplift_uniq
      apply gaplift_uniq
      simp [assoc_cast, hl] }

end Cartesian

/-- The type of cartesian lifts of a morphism `f` with fixed target. -/
class CartLift (f : I ⟶ J) (tgt : F J) extends Lift f tgt where
  is_cart : Cartesian homOver

/--Mere existence of a cartesian lift with fixed target. -/
def HasCartLift (f : I ⟶ J) (tgt : F J) := Nonempty (CartLift f tgt)

end Display

end CategoryTheory
