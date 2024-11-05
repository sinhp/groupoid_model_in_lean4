/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Preorder
import GroupoidModel.FibrationForMathlib.FibredCats.Basic
--import GroupoidModel.FibrationForMathlib.FibredCats.CartesianLift
--import GroupoidModel.FibrationForMathlib.FibredCats.VerticalLift

/-!
# Displayed Category

Given a type family `F : C → Type*` on a category `C` we define the type class `Display F` of
displayed categories over `F`. A displayed category structure associates to each morphism `f` in `C`
and terms `X : F c` and `Y : F d` a type `HomOver f X Y` whose terms are to be thought of as
morphisms lying over `f` starting from `X` and ending at `Y`. The data of a displayed category
structure also provides the dependent operations of identity and composition for `HomOver`.
Finally, the modified laws of associativity and unitality hold, up to casting, dependently over
the associativity and unitality equalities in `C`.

Our main construction is the displayed category of a functor. Given a functor `P : E ⥤ C`, the
associated displayed category on the fiber family `fun c => P⁻¹ c` is provided by the instance
`instDisplayOfFunctor`. Here `HomOver f X Y ` is given by the type `BasedLift f src tgt` carrying
data witnessing morphisms in `E` starting from `src` and ending at `tgt` and are mapped to `f`
under `P`.

We also provide various useful constructors for based-lifts:
* `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
  tautological based-lift of its image `P.map g`.
* `BasedLift.id` and `BasedLift.comp` provide the identity and composition of
  based-lifts, respectively.
* We can cast a based-lift along an equality of the base morphisms using the equivalence
`BasedLift.cast`.

We provide the following notations:
* `X ⟶[f] Y` for `DisplayStruct.HomOver f x y`
* `f ≫ₗ g` for `DisplayStruct.comp_over f g`

We show that for a functor `P`, the type `BasedLift P` induces a display category structure on the
fiber family `fun c => P⁻¹ c`.

-/

set_option autoImplicit true

namespace CategoryTheory

open Category CategoryTheory

variable {C : Type*} [Category C] (F : C → Type*)

def Fiber (I : C) := F I

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
    w ▸ g = w' ▸ g := rfl

lemma cast_cast {f f' : I ⟶ J} {X : F I} {Y : F J} (w : f = f') (w' : f' = f) (g : X ⟶[f'] Y) :
    w' ▸ w ▸ g = g := fiber_cast_cast (fun {f'} ↦ X ⟶[f'] Y) g

lemma comp_id_eq_cast_id_comp {f : I ⟶ J} {X : F I} {Y : F J} (g : X ⟶[f] Y) :
    g ≫ₗ 𝟙ₗ Y = cast (by simp) (𝟙ₗ X  ≫ₗ g) := by
  simp only [comp_id_cast, cast, id_comp_cast, comp_id, cast_trans]

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
  rfl

@[simps!]
def castEquiv {I J : C} {f f' : I ⟶ J} {X : F I} {Y : F J} (w : f = f') : (X ⟶[f] Y) ≃ (X ⟶[f'] Y) where
  toFun := fun g ↦ w ▸ g
  invFun := fun g ↦ w.symm ▸ g
  left_inv := by aesop_cat
  right_inv := by aesop_cat

end HomOver

namespace Display

variable [Display F]

/-- The total space of a displayed category consists of pairs `(I, X)` where `I` is an object of `C`
and `X` is an object of the fiber over `I`. -/
def Total := Σ I : C, F I

prefix:75 " ∫ "  => Total

variable {F}

abbrev TotalHom (X Y : ∫ F) := Σ (f : X.1 ⟶ Y.1), X.2 ⟶[f] Y.2


@[simp]
instance : CategoryStruct (∫ F) where
  Hom := TotalHom
  id X := ⟨𝟙 X.1, 𝟙ₗ X.2⟩
  comp u u' := ⟨u.1 ≫ u'.1, u.2 ≫ₗ u'.2⟩

instance {X Y : ∫ F} : PartialOrder (X ⟶ Y) where
  le u u' := ∃ (w : u.1 = u'.1), (w ▸ u.2) = u'.2
  le_refl g := ⟨rfl, rfl⟩
  le_trans := @fun f g h α β =>
    ⟨α.1.trans β.1, by
      rw [← HomOver.cast_trans (w:= α.1) (w':= β.1) f.snd]
      simp_rw [α.2, β.2]⟩
  le_antisymm := @fun f g α β => by
    cases f
    cases g
    aesop

instance instCategoryTotalHom {X Y : ∫ F} : SmallCategory (X ⟶ Y) := by
  infer_instance

@[simp]
lemma cast_exchange_comp {I J K : C} {f f' : I ⟶ J} {h h' : J ⟶ K} {X : F I} {Y : F J} {Z : F K}
    (g : X ⟶[f] Y) (k : Y ⟶[h] Z) (w : f = f') (w' : h = h') :
    w' ▸ (g ≫ₗ k) = (w ▸ g) ≫ₗ (w' ▸ k) := by
  subst w w'
  rfl

@[simp]
lemma whisker_left_cast_comp {I J K : C} {f : I ⟶ J} {h h' : J ⟶ K} {X : F I} {Y : F J} {Z : F K}
    (g : X ⟶[f] Y) (k : Y ⟶[h] Z) (w : h = h') : (f ≫= w) ▸ (g ≫ₗ k) = g ≫ₗ (w ▸ k) := by
  subst w
  rfl

@[simp]
lemma whisker_right_cast_comp {I J K : C} {f f' : I ⟶ J} {h : J ⟶ K} {X : F I} {Y : F J} {Z : F K}
    (g : X ⟶[f] Y) (k : Y ⟶[h] Z) (w : f = f') : (w =≫ h) ▸ (g ≫ₗ k) = (w ▸ g) ≫ₗ k := by
  subst w
  rfl

instance : Bicategory (∫ F) where
  homCategory := fun X Y => by infer_instance
  whiskerLeft := @fun X Y Z g k k' α => by
    use g.1 ≫= α.1.1.1
    have : k'.2 = (α.1.1.1 ▸ k.2)  := by rw [α.1.1.2]
    simp [this] -- i don't understand why `rw [this]` doesn't work
    apply whisker_left_cast_comp
  whiskerRight := @fun X Y Z g g' α k => by
    use α.1.1.1 =≫ k.1
    have : g'.2 = (α.1.1.1 ▸ g.2)  := by rw [α.1.1.2]
    simp [this] -- i don't understand why `rw [this]` doesn't work
    apply whisker_right_cast_comp
  associator := @fun X Y Z W g k m => {
    hom := by
      use assoc g.1 k.1 m.1
      aesop
    inv := by
      use (assoc g.1 k.1 m.1).symm
      aesop
  }
  leftUnitor := @fun X Y g => {
    hom := by
      use id_comp g.1
      aesop
    inv := by
      use (id_comp g.1).symm
      aesop
  }
  rightUnitor := @fun X Y g => {
    hom := by
      use comp_id g.1
      aesop
    inv := by
      use (comp_id g.1).symm
      aesop
  }
  whiskerLeft_id := by aesop_cat
  whiskerLeft_comp := by aesop_cat
  id_whiskerLeft := by aesop_cat
  comp_whiskerLeft := by aesop_cat
  id_whiskerRight := by aesop_cat
  comp_whiskerRight := by aesop_cat
  whiskerRight_id := by aesop_cat
  whiskerRight_comp := by aesop_cat
  whisker_assoc := by aesop_cat
  whisker_exchange := sorry
  pentagon := sorry
  triangle := sorry

instance : Category (∫ F) where
  Hom X Y := TotalHom X Y
  id X := ⟨𝟙 X.1, 𝟙ₗ X.2⟩
  comp g₁ g₂ := ⟨g₁.1 ≫ g₂.1, g₁.2 ≫ₗ g₂.2⟩
  id_comp g := by cases' g with g₁ g₂; dsimp; congr 2 <;> simp
  comp_id g := by sorry
  assoc g₁ g₂ g₃ := by aesop_cat


#check Bicategory


/-- The category structure on the fibers of a display category. -/
instance instCategoryFiber {I : C} : Category (F I) where
  Hom X Y := X ⟶[𝟙 I] Y
  id X := 𝟙ₗ X
  comp g₁ g₂ := HomOver.cast (id_comp (𝟙 I)) (g₁ ≫ₗ g₂)
  id_comp g := by aesop_cat
  comp_id g := by aesop_cat
  assoc g₁ g₂ g₃ := by
    simp; sorry


variable (F) in
def Vert := Σ I : C, F I

structure VertHom (X Y : Vert F) where
  base_eq : X.1 = Y.1
  over_id : X.2 ⟶[𝟙 X.1] (base_eq.symm ▸ Y.2)

instance : Category (Vert F) where
  Hom := fun X Y => VertHom X Y
  id := fun X => ⟨rfl, 𝟙ₗ X.2⟩
  comp := @fun X Y Z f g => sorry
    --⟨f.base_eq ▸ g.base_eq, HomOver.cast (comp_id (𝟙 X)).symm (f.over_id ≫ₗ (HomOver.eqToHomMapId (f.base_eq).symm g.over_id))⟩

/-- A hom-over of an isomorphism is invertible if -/
class IsIso {I J : C} {f : I ⟶ J} [IsIso f] {X : F I} {Y : F J} (g : X ⟶[f] Y) : Prop where
  /-- The existence of an inverse hom-over. -/
  out : ∃ inv : Y ⟶[inv f] X, (IsIso.hom_inv_id f) ▸ (g ≫ₗ inv) = 𝟙ₗ X ∧ (IsIso.inv_hom_id f) ▸ (inv ≫ₗ g) = 𝟙ₗ Y

end Display

/-- The IsoDisplay structure associated to a family `F` of types over a category `C`: A display category is iso-display if every hom-over an isomorphism is itself a display isomorphism.  -/
class IsoDisplay extends Display F where
  iso_HomOver : ∀ {I J : C} {f : I ⟶ J} [IsIso f] {X : F I} {Y : F J} (g : X ⟶[f] Y), Display.IsIso g

variable  {E : Type*} [Category E] {P : E ⥤ C}

/-

/-- The type of lifts of a given morphism in the base
with fixed source and target in the fibers of the domain and codomain respectively.-/
structure BasedLift {I J : C} (f : I ⟶ J) (src : P⁻¹ c) (tgt : P⁻¹ d) where
hom : (src : E) ⟶ (tgt : E)
over : (P.map hom) ≫ eqToHom (tgt.over) = eqToHom (src.2) ≫ f

namespace BasedLift

variable {E : Type*} [Category E] {P : E ⥤ C}

@[simp]
lemma over_base {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d} (g : BasedLift f x y) : P.map g.hom = eqToHom (x.2) ≫ f ≫ (eqToHom (y.over).symm)  := by
  simp only [← Category.assoc _ _ _, ← g.over, assoc, eqToHom_trans, eqToHom_refl, comp_id]

/-- The identity based-lift. -/
@[simps!]
def id (X : P⁻¹ I) : BasedLift (𝟙 c) x x := ⟨𝟙 _, by simp⟩

/-- The composition of based-lifts -/
@[simps]
def comp {I J K: C} {f₁ : I ⟶ J} {f₂ : J ⟶ K} {x : P⁻¹ I} {y : P⁻¹ J} {z : P⁻¹ K} (g₁ : BasedLift f₁ x y) (g₂ : BasedLift f₂ y z) : BasedLift (f₁ ≫ f₂) x z :=
⟨g₁.hom ≫ g₂.hom, by simp only [P.map_comp]; rw [assoc, over_base g₁, over_base g₂]; simp⟩

@[simps!]
def cast {I J : C} {f f' : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d} (w : f = f')
(g : BasedLift f x y) : BasedLift f' x y
 := ⟨g.hom, by rw [←w, g.over]⟩

end BasedLift

variable (P)

/-- The display structure `DisplayStruct P` associated to a functor `P : E ⥤ C`. This instance makes the display notations `_ ⟶[f] _`, `_ ≫ₗ _` and `𝟙ₗ` available for based-lifts.   -/
instance instDisplayStructOfFunctor : DisplayStruct (fun c => P⁻¹ c) where
  HomOver := fun f x y => BasedLift f x y
  id_over x := sorry -- BasedLift.id x
  comp_over := fun g₁ g₂ => BasedLift.comp g₁ g₂

namespace BasedLift

variable {P}

section
variable {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} {d} {y : P⁻¹ d} (g g' : X ⟶[f] Y)
#check g
#reduce g
#check (g : BasedLift f x y)
end

@[ext]
theorem ext {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d} (g g' : X ⟶[f] Y)
(w : g.hom = g'.hom)  : g = g' := by
  cases' g with g hg
  cases' g' with g' hg'
  congr

@[simp]
lemma cast_rec {I J : C} {f f' : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d} {w : f = f'} (g : X ⟶[f] Y) : g.cast w  = w ▸ g := by
  subst w; rfl

@[simps!]
def castEquiv {I J : C} {f f' : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d} (w : f = f') : (X ⟶[f] Y) ≃ (x ⟶[f'] y) := Display.castEquiv (fun c => P⁻¹ c) w

-- where
--   toFun := fun g ↦ g.cast w
--   invFun := fun g ↦ g.cast w.symm
--   left_inv := by aesop_cat
--   right_inv := by aesop_cat

/-- `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
based-lift of its image `P g` under functor `P`. -/
@[simps!]
def tauto {e e' : E} (g : e ⟶ e') : (Fiber.tauto e) ⟶[P.map g] (Fiber.tauto e') := ⟨g, by simp only [Fiber.tauto, eqToHom_refl, id_comp, comp_id]⟩

lemma tauto_over_base (f : (P.obj x) ⟶ (P.obj y)) (e : (Fiber.tauto x) ⟶[f] (Fiber.tauto y)) : P.map e.hom = f := by
  simp only [Fiber.coe_mk, over_base, eqToHom_refl, comp_id, id_comp]

lemma tauto_comp_hom {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} : (tauto (P:= P) g ≫ₗ  tauto g').hom = g ≫ g' := rfl

lemma comp_tauto_hom {x y z : E} {f : P.obj x ⟶ P.obj y} {l : Fiber.tauto x ⟶[f] (Fiber.tauto y)} {g : y ⟶ z} : (l ≫ₗ tauto g).hom = l.hom ≫ g := rfl

/-- A morphism of `E` coerced as a tautological based-lift. -/
@[simps]
instance instCoeTautoBasedLift {e e' : E} {g : e ⟶ e'} :
CoeDep (e ⟶ e') (g) (Fiber.tauto e  ⟶[P.map g] Fiber.tauto e') where
  coe := tauto g

lemma eq_id_of_hom_eq_id {c : C} {X : P⁻¹ I} {g : x ⟶[𝟙 c] x} :
(g.hom = 𝟙 x.1) ↔ (g = id x) := by
  aesop

@[simp]
lemma id_comp_cast {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d}
{g : X ⟶[f] Y} : 𝟙ₗ x  ≫ₗ g = g.cast (id_comp f).symm := by ext; simp only [cast_hom, DisplayStruct.comp_over, DisplayStruct.id_over, comp_hom, id_hom, id_comp]

@[simp]
lemma comp_id_cast {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d} {g : X ⟶[f] Y} : g ≫ₗ 𝟙ₗ y = g.cast (comp_id f).symm := by ext; simp only [cast_hom, DisplayStruct.comp_over, DisplayStruct.id_over, comp_hom, id_hom, comp_id]

@[simp]
lemma assoc {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'}
{X : P⁻¹ I} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :  ((g₁ ≫ₗ  g₂) ≫ₗ g₃) = (g₁ ≫ₗ g₂ ≫ₗ g₃).cast (assoc f₁ f₂ f₃).symm  := by
  ext; simp only [cast_hom, DisplayStruct.comp_over, comp_hom, Category.assoc]

lemma hom_comp_cast  {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {f : I ⟶ J'}
{w : f = f₁ ≫ f₂} {X : P⁻¹ I} {y : P⁻¹ d} {z : P⁻¹ d'} {g₁ : x ⟶[f₁] y}
{g₂ : y ⟶[f₂] z} {g : x ⟶[f] z} :
g₁.hom ≫ g₂.hom = g.hom ↔ g₁ ≫ₗ g₂ = g.cast w  := by
  constructor
  intro; aesop
  intro h; aesop

@[simps]
def castOfeqToHom {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {y : P⁻¹ d} :
(X ⟶[f] Y) ≃ (x.1 ⟶[(eqToHom x.2) ≫ f] y) where
  toFun := fun g => ⟨g.hom, by simp [g.over]⟩
  invFun := fun g => ⟨g.hom, by simp [g.over]⟩
  left_inv := by aesop_cat
  right_inv := by aesop_cat

end BasedLift

/-- The display category of a functor `P : E ⥤ C`. -/
def instDisplayOfFunctor : Display (fun c => P⁻¹ c) where
  id_comp_cast := by simp  --simp_all only [BasedLift.comp, BasedLift.id, id_comp]; rfl
  comp_id_cast := by simp
  assoc_cast := by simp

variable {P}

/-- The type of iso-based-lifts of an isomorphism in the base with fixed source
and target. -/
class IsoBasedLift  {I J : C} (f : I ⟶ J) [IsIso f] (X : P⁻¹ I) (y : P⁻¹ d) extends BasedLift f x y where
  is_iso_hom : IsIso hom

notation x " ⟶[≅" f "] " y => IsoBasedLift f x y





end CategoryTheory
-/
