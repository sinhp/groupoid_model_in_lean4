import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-! This file contains declarations missing from mathlib,
to be upstreamed. -/

universe u v

namespace CategoryTheory.Limits.PullbackCone.IsLimit

@[reassoc]
theorem comp_lift {C : Type u} [Category.{v, u} C]
    {X Y Z W' W : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g}
    (σ : W' ⟶ W) (ht : Limits.IsLimit t) (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    σ ≫ ht.lift (PullbackCone.mk h k w) =
      ht.lift (PullbackCone.mk (σ ≫ h) (σ ≫ k) (by simp [w])) := by
  refine ht.hom_ext fun j => ?_
  rcases j with _ | _ | _ <;> simp

end CategoryTheory.Limits.PullbackCone.IsLimit
