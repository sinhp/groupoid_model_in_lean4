import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Groupoid

universe u v

noncomputable section
namespace CategoryTheory
namespace Quotient

section
variable {G : Type u} [Groupoid.{v} G] (r : HomRel G)

protected def inv {X Y : Quotient r} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun f' => Quot.mk _ (inv f')) (fun _ _ con => by
    rcases con with ⟨ _, f, g, _, hfg ⟩
    have := Quot.sound <| CompClosure.intro (inv g) f g (inv f) hfg
    simp only [IsIso.hom_inv_id, Category.comp_id, IsIso.inv_hom_id_assoc] at this
    simp only [IsIso.inv_comp, Category.assoc]
    repeat rw [← comp_mk]
    rw [this])

@[simp]
theorem inv_mk {X Y : Quotient r} (f : X.as ⟶ Y.as) :
    Quotient.inv r (Quot.mk _ f) = Quot.mk _ (inv f) :=
  rfl

instance groupoid : Groupoid.{v} (Quotient r) where
  inv f := Quotient.inv r f
  inv_comp f := Quot.inductionOn f <| by simp [CategoryStruct.comp, CategoryStruct.id]
  comp_inv f := Quot.inductionOn f <| by simp [CategoryStruct.comp, CategoryStruct.id]

end
end Quotient
end CategoryTheory
