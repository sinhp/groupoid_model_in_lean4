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
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import GroupoidModel.FibrationForMathlib.Data.Fiber
import GroupoidModel.FibrationForMathlib.FibredCats.Basic
import GroupoidModel.FibrationForMathlib.FibredCats.CartesianLift

/-
open BasedLift

variable {P : E ⥤ C} {c' c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {x' : P⁻¹ c'} (g : x ⟶[f] y) [CartesianBasedLift (P:= P) g]

def gaplift_aux (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : x' ⟶[u] x :=
(CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').default.val

/-- `gaplift g u g'` is the canonical map from a lift `g' : x' ⟶[u ≫ f] y` to a
cartesian lift `g` of `f`. -/
def gaplift (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y) (h : f' = u ≫ f) : x' ⟶[u] x :=
(CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u (BasedLift.cast h g')).default.val

/-- The composition of the gap lift and the cartesian lift is the given lift. -/
@[simp]
lemma gaplift_property (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y)
(h : f' = u ≫ f) : ((gaplift g u g' h) ≫[l] g) = BasedLift.cast h g':=
(CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u
(BasedLift.cast h g')).default.property

/-- A variant of the gaplift property for equality of the underlying morphisms. -/
@[simp]
lemma gaplift_hom_property (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y)
(h : f' = u ≫ f) : (gaplift g u g' h).hom ≫  g.hom = g'.hom := by rw [← BasedLift.comp_hom _ _]; simp only [gaplift_property g u g' h, cast_hom]

end BasedLift
-/
