import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.Data.Part
import Mathlib.Tactic.CategoryTheory.Coherence

/-! This file contains small compatibility declarations not yet available under the names used by
HoTTLean.  Declarations that have been upstreamed to mathlib should be removed from here rather
than duplicated. -/

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

namespace Cat

/-- Compatibility lemma for the object function of an `eqToHom` in `Cat`. -/
theorem eqToHom_obj {C D : Cat.{v, u}} (eq : C = D) (x : C) :
    (eqToHom eq).toFunctor.obj x = cast (congrArg Bundled.α eq) x := by
  subst eq
  rfl

/-- Mapping along an `eqToHom` in `Cat` is heterogeneously equal to the original morphism. -/
theorem eqToHom_map_heq {C D : Cat.{v, u}} (eq : C = D) {x y : C} (f : x ⟶ y) :
    (eqToHom eq).toFunctor.map f ≍ f := by
  subst eq
  rfl

end Cat

attribute [reassoc (attr := simp)] Limits.IsTerminal.comp_from
attribute [reassoc (attr := simp)] Limits.IsInitial.to_comp

end CategoryTheory

@[simp]
theorem Part.assert_dom {α : Type*} (P : Prop) (x : P → Part α) :
    (Part.assert P x).Dom ↔ ∃ h : P, (x h).Dom :=
  Iff.rfl

namespace CategoryTheory

open Limits

namespace IsPullback

variable {C : Type u₁} [Category.{v₁} C]
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem of_iso_isPullback (h : IsPullback fst snd f g) {Q} (i : Q ≅ P) :
    IsPullback (i.hom ≫ fst) (i.hom ≫ snd) f g := by
  have : HasPullback f g := ⟨h.cone, h.isLimit⟩
  refine IsPullback.of_iso_pullback (by simp [h.w]) (i ≪≫ h.isoPullback) (by simp) (by simp)

end IsPullback

theorem pullback_map_eq_eqToHom {C : Type u₁} [Category.{v₁} C]
    {X Y Z : C} {f f' : X ⟶ Z} (hf : f = f') {g g' : Y ⟶ Z} (hg : g = g')
    [H : HasPullback f g] :
    letI : HasPullback f' g' := hf ▸ hg ▸ H
    pullback.map f g f' g' (𝟙 _) (𝟙 _) (𝟙 _) (by simp [hf]) (by simp [hg]) =
    eqToHom (by subst hf hg; rfl) := by
  subst hf hg
  apply pullback.hom_ext <;> simp

namespace AsSmall

@[simp] theorem up_comp_down
    {C : Type u₁} [Category.{v₁, u₁} C] :
    AsSmall.up ⋙ AsSmall.down = Functor.id C := rfl

@[simp] theorem down_comp_up
    {C : Type u₁} [Category.{v₁, u₁} C] :
    AsSmall.down ⋙ AsSmall.up = Functor.id (AsSmall C) := rfl

instance {C : Type u} [Category.{v} C] :
    Functor.IsEquivalence (AsSmall.up : C ⥤ AsSmall C) :=
  AsSmall.equiv.isEquivalence_functor

end AsSmall

namespace Groupoid

noncomputable instance asSmallGroupoid (Γ : Type u) [Groupoid.{v} Γ] :
    Groupoid (AsSmall.{w} Γ) where
  inv f := AsSmall.up.map (inv (AsSmall.down.map f))
  inv_comp := by sorry
  comp_inv := by sorry

end Groupoid

/- We have a nice, specific terminal object in some categories, and this class allows us to use it
rather than pass through an isomorphism with `Limits.terminal`. -/
class ChosenTerminal (C : Type u) [Category.{v} C] where
  terminal : C
  isTerminal : Limits.IsTerminal terminal

namespace ChosenTerminal
noncomputable section
open MonoidalCategory CartesianMonoidalCategory

scoped notation "𝟭_ " X:arg => ChosenTerminal.terminal (C := X)

def isTerminal_yUnit {C : Type u} [Category.{v} C] [ChosenTerminal C] :
    Limits.IsTerminal (yoneda.obj (𝟭_ C)) :=
  ChosenTerminal.isTerminal.isTerminalObj yoneda (𝟭_ C)

instance (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] : ChosenTerminal C where
  terminal := 𝟙_ C
  isTerminal := isTerminalTensorUnit

end
end ChosenTerminal

section equivalence

def functorToAsSmallEquiv {D : Type u₁} [Category.{v₁} D] {C : Type u} [Category.{v} C] :
    D ⥤ AsSmall.{w} C ≃ D ⥤ C where
  toFun A := A ⋙ AsSmall.down
  invFun A := A ⋙ AsSmall.up
  left_inv _ := rfl
  right_inv _ := rfl

variable {D : Type u₁} [Category.{v₁} D] {C : Type u} [Category.{v} C]
  {E : Type u₂} [Category.{v₂} E] (A : D ⥤ AsSmall.{w} C) (B : D ⥤ C)

lemma functorToAsSmallEquiv_apply_comp_left (F : E ⥤ D) :
    functorToAsSmallEquiv (F ⋙ A) = F ⋙ functorToAsSmallEquiv A := rfl

lemma functorToAsSmallEquiv_symm_apply_comp_left (F : E ⥤ D) :
    functorToAsSmallEquiv.symm (F ⋙ B) = F ⋙ functorToAsSmallEquiv.symm B := rfl

lemma functorToAsSmallEquiv_apply_comp_right (F : C ⥤ E) :
    functorToAsSmallEquiv (A ⋙ AsSmall.down ⋙ F ⋙ AsSmall.up) = functorToAsSmallEquiv A ⋙ F := rfl

lemma functorToAsSmallEquiv_symm_apply_comp_right (F : C ⥤ E) :
    functorToAsSmallEquiv.symm (B ⋙ F) =
    functorToAsSmallEquiv.symm B ⋙ AsSmall.down ⋙ F ⋙ AsSmall.up := rfl

end equivalence

namespace Limits

variable {𝒞 : Type u} [Category.{v} 𝒞]

noncomputable def pullbackHomEquiv {A B C : 𝒞} {Γ : 𝒞} {f : A ⟶ C} {g : B ⟶ C}
    [HasPullback f g] :
    (Γ ⟶ pullback f g) ≃
    (fst : Γ ⟶ A) × (snd : Γ ⟶ B) ×' (fst ≫ f = snd ≫ g) where
  toFun h := ⟨h ≫ pullback.fst f g, h ≫ pullback.snd f g, by simp [pullback.condition]⟩
  invFun x := pullback.lift x.1 x.2.1 x.2.2
  left_inv x := by
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]
  right_inv x := by
    rcases x with ⟨fst, snd, w⟩
    sorry

end Limits

namespace IsPullback

variable {C : Type*} [Category C]

@[simp]
lemma lift_fst_snd {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (pb : IsPullback fst snd f g) w : pb.lift fst snd w = 𝟙 _ := by
  apply pb.hom_ext <;> simp

end IsPullback

namespace Functor

theorem precomp_heq_of_heq_id {A B : Type u} {C : Type*} [Category.{v} A] [Category.{v} B]
    [Category C] (hAB : A = B) (h0 : HEq (inferInstance : Category A) (inferInstance : Category B))
    {F : A ⥤ B} (h : HEq F (𝟭 B)) (G : B ⥤ C) : HEq (F ⋙ G) G := by
  subst hAB; subst h0; subst h; rfl

theorem comp_heq_of_heq_id {A B : Type u} {C : Type*} [Category.{v} A] [Category.{v} B]
    [Category C] (hAB : A = B) (h0 : HEq (inferInstance : Category A) (inferInstance : Category B))
    {F : B ⥤ A} (h : HEq F (𝟭 B)) (G : C ⥤ B) : HEq (G ⋙ F) G := by
  subst hAB; subst h0; subst h; rfl

end Functor

lemma eqToHom_heq_id {C : Type*} [Category C] (x y z : C) (h : x = y)
    (hz : z = x) : eqToHom h ≍ 𝟙 z := by cat_disch

lemma inv_heq_of_heq_inv {C : Type*} [Groupoid C] {X Y X' Y' : C}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : Y' ⟶ X'} (hf : f ≍ inv g) :
    inv f ≍ g := by
  aesop_cat

lemma inv_heq_inv {C : Type*} [Category C] {X Y : C} {X' Y' : C}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : f ≍ f') [IsIso f] :
    have : IsIso f' := by aesop
    inv f ≍ inv f' := by
  subst hX hY hf
  rfl

lemma Discrete.as_heq_as {α α' : Type u} (hα : α ≍ α') (x : Discrete α) (x' : Discrete α')
    (hx : x ≍ x') : x.as ≍ x'.as := by
  aesop_cat

lemma Discrete.hext {X Y : Type u} (a : Discrete X) (b : Discrete Y) (hXY : X ≍ Y)
    (hab : a.1 ≍ b.1) : a ≍ b := by
  aesop_cat

lemma Discrete.Hom.hext {α β : Type u} {x y : Discrete α} (x' y' : Discrete β) (hαβ : α ≍ β)
    (hx : x ≍ x') (hy : y ≍ y') (f : x ⟶ y) (f' : x' ⟶ y') : f ≍ f' := by
  aesop_cat

open Prod in
lemma Prod.sectR_comp_snd {C : Type u₁} [Category.{v₁} C] (Z : C)
    (D : Type u₂) [Category.{v₂} D] : sectR Z D ⋙ snd C D = 𝟭 D := rfl

theorem ObjectProperty.lift_comp_inclusion_eq {C : Type u} [Category.{v} C]
    {D : Type u₁} [Category.{v₁} D] (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    P.lift F hF ⋙ P.ι = F := rfl

lemma eqToHom_heq_eqToHom {C : Type*} [Category C] (x y x' y' : C) (hx : x = x')
    (h : x = y) (h' : x' = y') : eqToHom h ≍ eqToHom h' := by aesop

end CategoryTheory

lemma hcongr_fun {α α' : Type u} (hα : α ≍ α') (β : α → Type v) (β' : α' → Type v) (hβ : β ≍ β')
    (f : (x : α) → β x) (f' : (x : α') → β' x) (hf : f ≍ f')
    {x : α} {x' : α'} (hx : x ≍ x') : f x ≍ f' x' := by
  subst hα hβ hf hx
  rfl

lemma fun_hext {α α' : Type u} (hα : α ≍ α') (β : α → Type v) (β' : α' → Type v) (hβ : β ≍ β')
    (f : (x : α) → β x) (f' : (x : α') → β' x)
    (hf : {x : α} → {x' : α'} → (hx : x ≍ x') → f x ≍ f' x') : f ≍ f' := by
  aesop

lemma Subtype.hext {α α' : Sort u} (hα : α ≍ α') {p : α → Prop} {p' : α' → Prop}
    (hp : p ≍ p') {a : { x // p x }} {a' : { x // p' x }} (ha : a.1 ≍ a'.1) : a ≍ a' := by
  subst hα hp
  simp only [heq_eq_eq]
  ext
  simpa [← heq_eq_eq]
