import Mathlib.Tactic.DepRewrite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Logic.Function.ULift
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.Data.Part
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Adjunction.Limits

/-! This file contains declarations missing from mathlib,
to be upstreamed. -/


/-

This comment space is for notes about mathlib definitions/theorems that should be fixed, refactored,
or redesigned.

- AsSmall.down and AsSmall.up should have their universe level order changed so that the third value comes first.
- currently I often write AsSmall.{_,_,w} because the first two can be inferred but not the max universe.

-/

namespace CategoryTheory

attribute [reassoc (attr := simp)] Limits.IsTerminal.comp_from
attribute [reassoc (attr := simp)] Limits.IsInitial.to_comp

@[reassoc]
theorem Limits.PullbackCone.IsLimit.comp_lift {C : Type*} [Category C]
    {X Y Z W' W : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g}
    (σ : W' ⟶ W) (ht : Limits.IsLimit t) (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    σ ≫ ht.lift (PullbackCone.mk h k w) =
      ht.lift (PullbackCone.mk (σ ≫ h) (σ ≫ k) (by simp [w])) := by
  refine ht.hom_ext fun j => ?_
  rcases j with _ | _ | _ <;> simp

end CategoryTheory

@[simp]
theorem Part.assert_dom {α : Type*} (P : Prop) (x : P → Part α) :
    (Part.assert P x).Dom ↔ ∃ h : P, (x h).Dom :=
  Iff.rfl

/-
  Mathlib.CategoryTheory.Category.ULift
-/
universe w v u v₁ u₁ v₂ u₂ v₃ u₃

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory.ULift

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/- Composing with downFunctor is injective.
   This requires an explicit universe variable in its fifth universe argument `u`. -/
theorem comp_downFunctor_inj (F G : C ⥤ ULift.{u} D) :
    F ⋙ downFunctor = G ⋙ downFunctor ↔ F = G := by
  constructor
  · intro hFG
    apply Functor.ext
    · intro x y
      exact Functor.congr_hom hFG
    · intro x
      have h := Functor.congr_obj hFG x
      simp only [downFunctor, Functor.comp_obj, ULift.down_inj] at h
      exact h
  · intro hFG
    subst hFG
    rfl

-- TODO change this to first universe argument

/- Composing with upFunctor is injective.
   This requires an explicit universe variable in its fifth universe paargument. -/
theorem comp_upFunctor_inj (F G : C ⥤ D) : F ⋙ upFunctor = G ⋙ upFunctor ↔ F = G := by
  constructor
  · intro hFG
    apply Functor.ext
    · intro _ _
      exact Functor.congr_hom hFG
    · intro x
      have h := Functor.congr_obj hFG x
      simp only [upFunctor, Functor.comp_obj, ULift.up_inj] at h
      exact h
  · intro hFG
    subst hFG
    rfl

end CategoryTheory.ULift

/-
  Cat
-/

namespace CategoryTheory.Cat

/-- This is the proof of equality used in the eqToHom in `Cat.eqToHom_hom` -/
theorem eqToHom_hom_aux {C1 C2 : Cat.{v,u}} (x y: C1) (eq : C1 = C2) :
    (x ⟶ y) = ((eqToHom eq).toFunctor.obj x ⟶ (eqToHom eq).toFunctor.obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem eqToHom_hom {C1 C2 : Cat.{v,u}} {x y: C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).toFunctor.map f = (cast (Cat.eqToHom_hom_aux x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

/-- This turns the object part of eqToHom functors into casts -/
theorem eqToHom_obj {C1 C2 : Cat.{v,u}} (x : C1) (eq : C1 = C2) :
    (eqToHom eq).toFunctor.obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp[CategoryStruct.id]

abbrev homOf {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := ⟨F⟩

@[simps] def ULift_lte_iso_self {C : Type (max u u₁)} [Category.{v} C] :
    Cat.of (ULift.{u} C) ≅ Cat.of C where
  hom := homOf ULift.downFunctor
  inv := homOf ULift.upFunctor

@[simp] def ULift_succ_iso_self {C : Type (u + 1)} [Category.{v} C] :
    of (ULift.{u, u + 1} C) ≅ of C := ULift_lte_iso_self.{v,u,u+1}

@[simp] def ULift_iso_self {C : Type u} [Category.{v} C] :
    of (ULift.{u, u} C) ≅ of C := ULift_lte_iso_self

def ofULift (C : Type u) [Category.{v} C] : Cat.{v, max u w} :=
  of $ ULift.{w} C

def uLiftFunctor : Cat.{v,u} ⥤ Cat.{v, max u w} where
  obj X := ofULift.{w} X
  map F := homOf $ ULift.downFunctor ⋙ F.toFunctor ⋙ ULift.upFunctor

end CategoryTheory.Cat

/-
  CategoryTheory.Grothedieck

-/

namespace CategoryTheory

section

variable (C : Type*) [Category C] (D : Type*) [Category D]

@[simp] lemma prod.eqToHom_fst (x y : C × D) (h : x = y) :
    (eqToHom h).1 = eqToHom (by aesop) := by
  subst h
  rfl

@[simp] lemma prod.eqToHom_snd (x y : C × D) (h : x = y) :
    (eqToHom h).2 = eqToHom (by aesop) := by
  subst h
  rfl

end

open Limits
namespace IsPullback

variable {C : Type u₁} [Category.{v₁} C]

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem of_iso_isPullback (h : IsPullback fst snd f g) {Q} (i : Q ≅ P) :
      IsPullback (i.hom ≫ fst) (i.hom ≫ snd) f g := by
  have : HasPullback f g := ⟨ h.cone , h.isLimit ⟩
  refine IsPullback.of_iso_pullback (by simp [h.w]) (i ≪≫ h.isoPullback) (by simp) (by simp)

@[simp] theorem isoPullback_refl [HasPullback f g] :
    isoPullback (.of_hasPullback f g) = Iso.refl _ := by ext <;> simp

theorem isoPullback_eq_eqToIso_left
    {X Y Z : C} {f f' : X ⟶ Z} (hf : f = f') (g : Y ⟶ Z) [H : HasPullback f g] :
    letI : HasPullback f' g := hf ▸ H
    isoPullback (fst := pullback.fst f g) (snd := pullback.snd f g) (f := f')
      (by subst hf; exact .of_hasPullback f g) =
    eqToIso (by subst hf; rfl) := by subst hf; simp

end IsPullback

theorem pullback_map_eq_eqToHom {C : Type u₁} [Category.{v₁} C]
    {X Y Z : C} {f f' : X ⟶ Z} (hf : f = f') {g g' : Y ⟶ Z} (hg : g = g')
    [H : HasPullback f g] :
    letI : HasPullback f' g' := hf ▸ hg ▸ H
    pullback.map f g f' g' (𝟙 _) (𝟙 _) (𝟙 _) (by simp [hf]) (by simp [hg]) =
    eqToHom (by subst hf hg; rfl) := by subst hf hg; simp

end CategoryTheory

namespace CategoryTheory

namespace AsSmall

@[simp] theorem up_map_down_map
    {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) :
  AsSmall.down.map (AsSmall.up.map f) = f := rfl

@[simp] theorem down_map_up_map
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : AsSmall C} (f : X ⟶ Y) :
  AsSmall.up.map (AsSmall.down.map f) = f := rfl

theorem comp_up_inj {C : Type u} [Category.{v} C]
  {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ D}
    (h : F ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D) =
      G ⋙ AsSmall.up)
    : F = G := by
  convert_to F ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D)
    ⋙ AsSmall.down
    = G ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D)
    ⋙ AsSmall.down
  simp only [← Functor.assoc, h]

theorem comp_down_inj {C : Type u} [Category.{v} C]
  {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ AsSmall.{w} D}
    (h : F ⋙ AsSmall.down = G ⋙ AsSmall.down)
    : F = G := by
  convert_to F ⋙ AsSmall.down
    ⋙ AsSmall.up
    = G ⋙ AsSmall.down ⋙ AsSmall.up
  simp only [← Functor.assoc, h]

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

instance asSmallGroupoid (Γ : Type u) [Groupoid.{v} Γ] :
    Groupoid (AsSmall.{w} Γ) where
  inv f := AsSmall.up.map (inv (AsSmall.down.map f))

end Groupoid

namespace Grpd

abbrev homOf {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D] (F : C ⥤ D) :
    Grpd.of C ⟶ Grpd.of D := F

lemma homOf_id {A : Type u} [Groupoid.{v} A] : Grpd.homOf (𝟭 A) = 𝟙 _ :=
  rfl

lemma homOf_comp {A B C : Type u} [Groupoid.{v} A] [Groupoid.{v} B] [Groupoid.{v} C]
    (F : A ⥤ B) (G : B ⥤ C) : Grpd.homOf (F ⋙ G) = Grpd.homOf F ≫ Grpd.homOf G :=
  rfl

def asSmallFunctor : Grpd.{v, u} ⥤ Grpd.{max w v u, max w v u} where
  obj Γ := Grpd.of $ AsSmall.{max w v u} Γ
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

end Grpd

/- We have a 'nice', specific terminal object in `Ctx`,
and this instance allows use to use it directly
rather than through an isomorphism with `Limits.terminal`. -/
class ChosenTerminal (C : Type u) [Category.{v} C] where
  terminal : C
  /-- The tensor unit is a terminal object. -/
  isTerminal : Limits.IsTerminal terminal

namespace ChosenTerminal
noncomputable section
open MonoidalCategory CartesianMonoidalCategory

/-- Notation for `terminal` -/
scoped notation "𝟭_ " X:arg => ChosenTerminal.terminal (C := X)

def isTerminal_yUnit {C : Type u} [Category.{v} C] [ChosenTerminal C] :
    Limits.IsTerminal (yoneda.obj (𝟭_ C)) :=
  ChosenTerminal.isTerminal.isTerminalObj yoneda (𝟭_ C)

instance (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] : ChosenTerminal C where
  terminal := 𝟙_ C
  isTerminal := isTerminalTensorUnit

end
end ChosenTerminal

namespace Equivalence
noncomputable section
open Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [CartesianMonoidalCategory C]
  (e : Equivalence C D)

/-- The chosen terminal object in `D`. -/
abbrev chosenTerminal : D :=
  e.functor.obj (𝟙_ C)

/-- The chosen terminal object in `D` is terminal. -/
def chosenTerminalIsTerminal :
    IsTerminal (e.chosenTerminal : D) :=
  (IsTerminal.ofUnique _).isTerminalObj e.functor

/-- Product cones in `D` are defined using chosen products in `C` -/
def prodCone (X Y : D) : BinaryFan X Y :=
  .mk
  (P := e.functor.obj (MonoidalCategory.tensorObj
    (e.inverse.obj X) (e.inverse.obj Y)))
  (e.functor.map (fst _ _) ≫ (e.counit.app _))
  (e.functor.map (snd _ _) ≫ (e.counit.app _))

/-- The chosen product cone in `D` is a limit. -/
def isLimitProdCone (X Y : D) : IsLimit (e.prodCone X Y) :=
  IsLimit.ofIsoLimit (
  BinaryFan.isLimitCompRightIso _ (e.counit.app _) (
  BinaryFan.isLimitCompLeftIso _ (e.counit.app _) (
  isLimitCartesianMonoidalCategoryOfPreservesLimits e.functor
    (e.inverse.obj X) (e.inverse.obj Y))))
  (BinaryFan.ext (eqToIso rfl) (by aesop_cat) (by aesop_cat))

def chosenFiniteProducts [CartesianMonoidalCategory C] : CartesianMonoidalCategory D :=
  .ofChosenFiniteProducts
    { cone := asEmptyCone e.chosenTerminal
      isLimit := e.chosenTerminalIsTerminal }
    (fun X Y => {
      cone := e.prodCone X Y
      isLimit := e.isLimitProdCone X Y })

end
end Equivalence

section equivalence

def functorToAsSmallEquiv {D : Type u₁} [Category.{v₁} D] {C : Type u} [Category.{v} C]
    : D ⥤ AsSmall.{w} C ≃ D ⥤ C where
  toFun A := A ⋙ AsSmall.down
  invFun A := A ⋙ AsSmall.up
  left_inv _ := rfl
  right_inv _ := rfl

section

variable {D : Type u₁} [Category.{v₁} D] {C : Type u} [Category.{v} C]
  {E : Type u₂} [Category.{v₂} E] (A : D ⥤ AsSmall.{w} C) (B : D ⥤ C)

lemma functorToAsSmallEquiv_apply_comp_left (F : E ⥤ D) :
    functorToAsSmallEquiv (F ⋙ A) = F ⋙ functorToAsSmallEquiv A :=
  rfl

lemma functorToAsSmallEquiv_symm_apply_comp_left (F : E ⥤ D) :
    functorToAsSmallEquiv.symm (F ⋙ B) = F ⋙ functorToAsSmallEquiv.symm B :=
  rfl

lemma functorToAsSmallEquiv_apply_comp_right (F : C ⥤ E) :
    functorToAsSmallEquiv (A ⋙ AsSmall.down ⋙ F ⋙ AsSmall.up) = functorToAsSmallEquiv A ⋙ F :=
  rfl

lemma functorToAsSmallEquiv_symm_apply_comp_right (F : C ⥤ E) :
    functorToAsSmallEquiv.symm (B ⋙ F) =
    functorToAsSmallEquiv.symm B ⋙ AsSmall.down ⋙ F ⋙ AsSmall.up :=
  rfl

end

open ULift

instance (C : Type u) [Category.{v} C] :
    (downFunctor : ULift.{w} C ⥤ C).ReflectsIsomorphisms :=
  ULift.equivalence.fullyFaithfulInverse.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (upFunctor : C ⥤ ULift.{w} C).ReflectsIsomorphisms :=
  ULift.equivalence.fullyFaithfulFunctor.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (AsSmall.down : AsSmall.{w} C ⥤ C).ReflectsIsomorphisms :=
  AsSmall.equiv.fullyFaithfulInverse.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C).ReflectsIsomorphisms :=
  AsSmall.equiv.fullyFaithfulFunctor.reflectsIsomorphisms

end equivalence

section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}

@[simp] theorem Cat.map_id_obj {A : Γ ⥤ Cat.{v₁,u₁}}
    {x : Γ} {a : A.obj x} :
    (A.map (𝟙 x)).toFunctor.obj a = a := by
  simp

theorem Cat.map_id_map {A : Γ ⥤ Cat.{v₁,u₁}}
    {x : Γ} {a b : A.obj x} {f : a ⟶ b} :
    (A.map (𝟙 x)).toFunctor.map f = eqToHom Cat.map_id_obj
      ≫ f ≫ eqToHom Cat.map_id_obj.symm := by
  rw! [show A.map (𝟙 x) = 𝟙 (A.obj x) by simp]
  simp

end

section
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {B : Type u} [Category.{v} B]

@[simp]
theorem isoWhiskerLeft_eqToIso (F : C ⥤ D) {G H : D ⥤ E} (η : G = H) :
    Functor.isoWhiskerLeft F (eqToIso η) = eqToIso (by subst η; rfl) := by
  subst η
  rfl

end
end CategoryTheory

namespace Equiv
def psigmaCongrProp {α₁ α₂} {β₁ : α₁ → Prop} {β₂ : α₂ → Prop} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ↔ β₂ (f a)) : PSigma β₁ ≃ PSigma β₂ where
  toFun x := .mk (f x.1) (by rw [← F]; exact x.2)
  invFun x := .mk (f.symm x.1) (by
    simp only [F, apply_symm_apply]; exact x.2)
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem sigmaCongr_apply_fst {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ≃ β₂ (f a)) (x : Sigma β₁) : (sigmaCongr f F x).fst = f x.fst := by
  simp [sigmaCongr]

@[simp] def sigmaCongr_apply_snd {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ≃ β₂ (f a)) (x : Sigma β₁) : (sigmaCongr f F x).snd = F x.fst x.snd := by
  simp [sigmaCongr]

end Equiv

namespace CategoryTheory.Limits

variable {𝒞 : Type u} [Category.{v} 𝒞]

noncomputable def pullbackHomEquiv {A B C: 𝒞} {Γ : 𝒞} {f : A ⟶ C} {g : B ⟶ C} [HasPullback f g] :
    (Γ ⟶ pullback f g) ≃
    (fst : Γ ⟶ A) × (snd : Γ ⟶ B) ×' (fst ≫ f = snd ≫ g) where
  toFun h := ⟨h ≫ pullback.fst f g, h ≫ pullback.snd f g, by simp[pullback.condition]⟩
  invFun x := pullback.lift x.1 x.2.1 x.2.2
  left_inv _ := pullback.hom_ext (by simp) (by simp)
  right_inv := by rintro ⟨_,_,_⟩; congr!; simp; simp

end CategoryTheory.Limits

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category C]

@[simp]
lemma lift_fst_snd {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (pb : IsPullback fst snd f g) w : pb.lift fst snd w = 𝟙 _ := by
  apply pb.hom_ext <;> simp

end CategoryTheory.IsPullback

namespace CategoryTheory

def ofYoneda {C : Type*} [Category C] {X Y : C}
    (app : ∀ {Γ}, (Γ ⟶ X) ⟶ (Γ ⟶ Y))
    (naturality : ∀ {Δ Γ} (σ : Δ ⟶ Γ) (A), app (σ ≫ A) = σ ≫ app A) :
    X ⟶ Y :=
  Yoneda.fullyFaithful.preimage {
    app Γ := app
    naturality Δ Γ σ := by ext; simp [naturality] }

@[simp]
lemma ofYoneda_comp_left {C : Type*} [Category C] {X Y : C}
    (app : ∀ {Γ}, (Γ ⟶ X) ⟶ (Γ ⟶ Y))
    (naturality : ∀ {Δ Γ} (σ : Δ ⟶ Γ) (A), app (σ ≫ A) = σ ≫ app A)
    {Γ} (A : Γ ⟶ X) : A ≫ ofYoneda app naturality = app A := by
  apply Yoneda.fullyFaithful.map_injective
  ext
  simp [ofYoneda, naturality]

lemma ofYoneda_comm_sq {C : Type*} [Category C] {TL TR BL BR : C}
    (left : TL ⟶ BL) (right : TR ⟶ BR)
    (top : ∀ {Γ}, (Γ ⟶ TL) ⟶ (Γ ⟶ TR))
    (top_comp : ∀ {Δ Γ} (σ : Δ ⟶ Γ) (tr), top (σ ≫ tr) = σ ≫ top tr)
    (bottom : ∀ {Γ}, (Γ ⟶ BL) ⟶ (Γ ⟶ BR))
    (bottom_comp : ∀ {Δ Γ} (σ : Δ ⟶ Γ) (br), bottom (σ ≫ br) = σ ≫ bottom br)
    (comm_sq : ∀ {Γ} (ab : Γ ⟶ TL), top ab ≫ right = bottom (ab ≫ left)) :
  (ofYoneda top top_comp) ≫ right = left ≫ (ofYoneda bottom bottom_comp) := by
  apply Yoneda.fullyFaithful.map_injective
  ext Γ ab
  simp [comm_sq, ofYoneda]

open Limits in
lemma ofYoneda_isPullback {C : Type u} [Category.{v} C] {TL TR BL BR : C}
    (left : TL ⟶ BL) (right : TR ⟶ BR)
    (top : ∀ {Γ}, (Γ ⟶ TL) ⟶ (Γ ⟶ TR))
    (top_comp : ∀ {Δ Γ} (σ : Δ ⟶ Γ) (tr), top (σ ≫ tr) = σ ≫ top tr)
    (bot : ∀ {Γ}, (Γ ⟶ BL) ⟶ (Γ ⟶ BR))
    (bot_comp : ∀ {Δ Γ} (σ : Δ ⟶ Γ) (br), bot (σ ≫ br) = σ ≫ bot br)
    (comm_sq : ∀ {Γ} (ab : Γ ⟶ TL), top ab ≫ right = bot (ab ≫ left))
    (lift : ∀ {Γ} (t : Γ ⟶ TR) (p), t ≫ right = bot p → (Γ ⟶ TL))
    (top_lift : ∀ {Γ} (t : Γ ⟶ TR) (p) (ht : t ≫ right = bot p), top (lift t p ht) = t)
    (lift_comp_left : ∀ {Γ} (t : Γ ⟶ TR) (p) (ht : t ≫ right = bot p), lift t p ht ≫ left = p)
    (lift_uniq : ∀ {Γ} (t : Γ ⟶ TR) (p) (ht : t ≫ right = bot p) (m : Γ ⟶ TL),
      top m = t → m ≫ left = p → m = lift t p ht) :
    IsPullback (ofYoneda top top_comp) left right (ofYoneda bot bot_comp) := by
  let c : PullbackCone right (ofYoneda bot bot_comp) :=
    PullbackCone.mk (ofYoneda top top_comp) left
    (ofYoneda_comm_sq _ _ _ _ _ _ comm_sq)
  apply IsPullback.of_isLimit (c := c)
  apply c.isLimitAux (fun s => lift (PullbackCone.fst s) (PullbackCone.snd s) (by
      simp [PullbackCone.condition s]))
  · simp [c, top_lift]
  · simp [c, lift_comp_left]
  · intro s m h
    apply lift_uniq
    · specialize h (some .left)
      simpa [c] using h
    · specialize h (some .right)
      exact h

variable {C : Type u₁} [SmallCategory C] {F G : Cᵒᵖ ⥤ Type u₁}
  (app : ∀ {X : C}, (yoneda.obj X ⟶ F) → (yoneda.obj X ⟶ G))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y) (α : yoneda.obj Y ⟶ F),
    app (yoneda.map f ≫ α) = yoneda.map f ≫ app α)

variable (F) in
/--
  A presheaf `F` on a small category `C` is isomorphic to
  the hom-presheaf `Hom(y(•),F)`.
-/
def yonedaIso : yoneda.op ⋙ yoneda.obj F ≅ F :=
  NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv)
    (fun f => by ext : 1; dsimp; rw [yonedaEquiv_naturality'])

def yonedaIsoMap : yoneda.op ⋙ yoneda.obj F ⟶ yoneda.op ⋙ yoneda.obj G where
  app _ := app
  naturality _ _ _ := by ext : 1; apply naturality

/-- Build natural transformations between presheaves on a small category
  by defining their action when precomposing by a morphism with
  representable domain -/
def NatTrans.yonedaMk : F ⟶ G :=
  (yonedaIso F).inv ≫ yonedaIsoMap app naturality ≫ (yonedaIso G).hom

theorem NatTrans.yonedaMk_app {X : C} (α : yoneda.obj X ⟶ F) :
    α ≫ yonedaMk app naturality = app α := by
  rw [← yonedaEquiv.apply_eq_iff_eq, yonedaEquiv_comp]
  simp [yonedaMk, yonedaIso, yonedaIsoMap]

namespace Functor

theorem precomp_heq_of_heq_id {A B : Type u} {C : Type*} [Category.{v} A] [Category.{v} B] [Category C]
    (hAB : A = B) (h0 : HEq (inferInstance : Category A) (inferInstance : Category B)) {F : A ⥤ B}
    (h : HEq F (𝟭 B)) (G : B ⥤ C) : HEq (F ⋙ G) G := by
  subst hAB
  subst h0
  subst h
  rfl

theorem comp_heq_of_heq_id {A B : Type u} {C : Type*} [Category.{v} A] [Category.{v} B] [Category C]
    (hAB : A = B) (h0 : HEq (inferInstance : Category A) (inferInstance : Category B))
    {F : B ⥤ A}
    (h : HEq F (𝟭 B)) (G : C ⥤ B) : HEq (G ⋙ F) G := by
  subst hAB
  subst h0
  subst h
  rfl

end Functor

lemma eqToHom_heq_id {C : Type*} [Category C] (x y z : C) (h : x = y)
    (hz : z = x) : eqToHom h ≍ 𝟙 z := by cat_disch

lemma Cat.inv_heq_inv {C C' : Cat} (hC : C ≍ C') {X Y : C} {X' Y' : C'}
    (hX : X ≍ X') (hY : Y ≍ Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : f ≍ f') [IsIso f] :
    have : IsIso f' := by aesop
    inv f ≍ inv f' := by
  subst hC hX hY hf
  rfl

lemma inv_heq_of_heq_inv {C : Grpd} {X Y X' Y' : C}
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

lemma Discrete.functor_ext' {X C : Type*} [Category C] {F G : X → C} (h : ∀ x : X, F x = G x) :
    Discrete.functor F = Discrete.functor G := by
  have : F = G := by aesop
  subst this
  rfl

lemma Discrete.functor_eq {X C : Type*} [Category C] {F : Discrete X ⥤ C} :
    F = Discrete.functor fun x ↦ F.obj ⟨x⟩ := by
  fapply CategoryTheory.Functor.ext
  · aesop
  · intro x y f
    cases x ; rcases f with ⟨⟨h⟩⟩
    cases h
    simp

lemma Discrete.hext {X Y : Type u} (a : Discrete X) (b : Discrete Y) (hXY : X ≍ Y)
    (hab : a.1 ≍ b.1) : a ≍ b := by
  aesop_cat

lemma Discrete.Hom.hext {α β : Type u} {x y : Discrete α} (x' y' : Discrete β) (hαβ : α ≍ β)
    (hx : x ≍ x') (hy : y ≍ y') (f : x ⟶ y) (f' : x' ⟶ y') : f ≍ f' := by
  aesop_cat

open Prod in
lemma Prod.sectR_comp_snd {C : Type u₁} [Category.{v₁} C] (Z : C)
    (D : Type u₂) [Category.{v₂} D] : sectR Z D ⋙ snd C D = 𝟭 D :=
  rfl

section
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (P Q : ObjectProperty D)
  (F : C ⥤ D) (hF : ∀ X, P (F.obj X))

theorem ObjectProperty.lift_comp_inclusion_eq :
    P.lift F hF ⋙ P.ι = F :=
  rfl

end

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
