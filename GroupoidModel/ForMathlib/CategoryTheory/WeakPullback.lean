import Mathlib.CategoryTheory.CommSq

namespace CategoryTheory

structure WeakPullback {C : Type*} [Category C]
    {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    extends CommSq fst snd f g where
  lift (W : C) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : W ⟶ P
  fac_left (W : C) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : lift W a b h ≫ fst = a
  fac_right (W : C) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : lift W a b h ≫ snd = b

end CategoryTheory
