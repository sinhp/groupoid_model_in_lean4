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

/-!
# Cartesian Lifts

For a functor `P : E ⥤ C`, the structure `BasedLift` provides the type of lifts
of a given morphism in the base with fixed source and target in the fibers of `P`:
More precisely, `BasedLift P f` is the type of morphisms in the domain category `E`
which are lifts of `f`.

We provide various useful constructors:
* `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
  based-lift of its image `P g` under functor `P`.
* `BasedLift.id` and `BasedLift.comp` provide the identity and composition of
  based-lifts, respectively.
* We can cast a based-lift along an equality of the base morphisms using the equivalence
`BasedLift.cast`.

There are also typeclasses `CartesianBasedLift` and `CoCartesianBasedLift`
carrying data witnessing that a given based-lift is cartesian and cocartesian, respectively.

For a functor `P : E ⥤ C`, we provide the class `CartMor` of cartesian morphisms in `E`.
The type `CartMor P`is defined in terms of the predicate `isCartesianMorphism`.

We prove the following closure properties of the class `CartMor` of cartesian morphisms:
- `cart_id` proves that the identity morphism is cartesian.
- `cart_comp` proves that the composition of cartesian morphisms is cartesian.
- `cart_iso_closed` proves that the class of cartesian morphisms is closed under isomorphisms.
- `cart_pullback` proves that, if `P` preserves pullbacks, then
the pullback of a cartesian morphism is cartesian.

`instCatCart` provides a category instance for the class of cartesian morphisms,
and `Cart.forget` provides the forgetful functor from the category of cartesian morphisms to
the domain category `E`.

Finally, We provide the following notations:
* `x ⟶[f] y` for `BasedLift P f x y`
* `f ≫[l] g` for the composition of based-lifts given by `BasedLift.comp f g`

-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
--set_option trace.simps.verbose true

namespace CategoryTheory

open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] [Category E]

-- @[ext]
-- structure BasedLift (P : E ⥤ C) {I J : C} (f : I ⟶ J) (src : P⁻¹ I) (tgt : P⁻¹ J) where
--   hom : (src : E) ⟶ (tgt : E)
--   over : (P.map hom) = f

/-- The type of lifts of a given morphism in the base
with fixed source and target in the fibers of the domain and codomain respectively.-/
@[ext]
structure BasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) where
hom : (src : E) ⟶ (tgt : E)
over : (P.map hom) ≫ eqToHom (tgt.over) = eqToHom (src.2) ≫ f

section BasedLiftNotation

variable (P : E ⥤ C) {c d : C} (f : c ⟶ d) {x : P⁻¹ c} {y : P⁻¹ d}

notation x " ⟶[" f "] " y => BasedLift (P:= _) f x y

end BasedLiftNotation

/-- A lift of a morphism in the base with a fixed target in the fiber of
the codomain -/
@[ext]
structure Lift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (tgt : P⁻¹ d) where
src : P⁻¹ c
based_lift : BasedLift P f src tgt

/-- A lift of a morphism in the base with a fixed source in the fiber of
the domain -/
@[ext]
structure CoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) where
tgt : P⁻¹ d
based_colift : BasedLift P f src tgt

/-- `HasLift P f y` represents the mere existence of a lift of the morphism `f` with target `y`. -/
def HasLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (y : P⁻¹ d) := Nonempty (Lift P f y)

/-- `HasColift P f x` represents the mere existence of a lift of the morphism `f` with source `x`. -/
def HasCoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) := Nonempty (CoLift P f x)

namespace BasedLift

variable {P : E ⥤ C}

/-- Two based-lifts of the same base morphism are equal if their underlying morphisms are
equal in the domain category. -/
lemma hom_ext {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {g₁ g₂ : x ⟶[f] y}
    (h : g₁.hom = g₂.hom) : g₁ = g₂ := (BasedLift.ext_iff g₁ g₂).mpr h

@[simp]
lemma over_base {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : BasedLift P f x y) :
    P.map g.hom = eqToHom (x.2) ≫ f ≫ (eqToHom (y.over).symm) := by
  simp only [← Category.assoc _ _ _, ← g.over, assoc, eqToHom_trans, eqToHom_refl, comp_id]

/-- Coercion from BasedLift to the domain category. -/
instance (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) (y : P⁻¹ d) :
    CoeOut (BasedLift P f x y) ((x : E) ⟶ (y : E)) where
  coe := fun l ↦ l.hom

/-- `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
based-lift of its image `P g` under functor `P`. -/
@[simps]
def tauto {e e' : E} (g : e ⟶ e') : (Fiber.tauto e) ⟶[P.map g] (Fiber.tauto e') :=
  ⟨g, by simp only [Fiber.tauto, eqToHom_refl, id_comp, comp_id]⟩

lemma tauto_over_base (f : (P.obj x) ⟶ (P.obj y)) (e : (Fiber.tauto x) ⟶[f] (Fiber.tauto y)) :
    P.map e.hom = f := by simp only [Fiber.coe_mk, over_base, eqToHom_refl, comp_id, id_comp]

/-- A tautological based-lift associated to a given morphism in the domain `E`. -/
@[simps]
instance instCoeTautoBasedLift {e e' : E} {g : e ⟶ e'} :
CoeDep (e ⟶ e') (g) (Fiber.tauto e  ⟶[P.map g] Fiber.tauto e') where
  coe := tauto g

/-- Regarding a based-lift `x ⟶[𝟙 c] y` of the identity morphism `𝟙 c`
as a morphism in the fiber `P⁻¹ c` .-/
@[simp]
instance instCoeFiberHom {c : C} {x y : P⁻¹ c} : Coe (x ⟶[𝟙 c] y) (x ⟶ y) where
  coe := fun f ↦ ⟨ f.hom , by simp [f.over]⟩

/-- `BasedLift.ofFiberHom` regards a morphism in the fiber category `P⁻¹ c`
as a based-lift of the identity morphism of `c`. -/
@[simps]
def ofFiberHom {c : C} {x y : P⁻¹ c} (f : x ⟶ y) : x ⟶[𝟙 c] y := ⟨f.1, by simp [f.2]⟩

/-- The identity based-lift. -/
@[simp]
def id (x : P⁻¹ c) : BasedLift P (𝟙 c) x x := ⟨𝟙 _, by simp⟩

lemma id_hom {x : P⁻¹ c} : (id x).hom = 𝟙 x.1 := rfl

/-- The composition of based-lifts -/
@[simp]
def comp {I J K : C} {f : I ⟶ J} {f' : J ⟶ K} {X : P⁻¹ I} {Y : P⁻¹ J} {Z : P⁻¹ K} (g : X ⟶[f] Y) (g' : Y ⟶[f'] Z) :
  X ⟶[f ≫ f'] Z :=
⟨g.hom ≫ g'.hom, by
  simp only [P.map_comp]
  rw [assoc, over_base g, over_base g']
  simp⟩

section
variable (P : E ⥤ C) {c d d': C} {x: P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (u : c ⟶ d) (v: d ⟶ d') (f : x ⟶[u] y) (g : y ⟶[v] z)

scoped infixr:80 "  ≫ₗ "  => BasedLift.comp

notation f " ≫[l] " g => BasedLift.comp f g
end

/-- The underlying morphism of a composition of based-lifts is the composition
of the underlying morphisms. -/
lemma comp_hom  {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : x ⟶[f₁] y) (g₂ : y ⟶[f₂] z) : (g₁ ≫[l] g₂).hom = g₁.hom ≫ g₂.hom := rfl

@[simp]
lemma comp_hom' {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'}
    {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} {h : x ⟶[f₁ ≫ f₂] z} :
    (g₁ ≫[l] g₂) = h ↔ g₁.hom ≫ g₂.hom = h.hom := ⟨fun H ↦ H ▸ rfl, fun H ↦ hom_ext H⟩

lemma tauto_comp_hom {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} :
    (tauto (P:= P) g ≫[l] tauto g').hom = g ≫ g' := rfl

lemma comp_tauto_hom {x y z : E} {f : P.obj x ⟶ P.obj y} {l : Fiber.tauto x ⟶[f] (Fiber.tauto y)}
    {g : y ⟶ z} : (l ≫[l] tauto g).hom = l.hom ≫ g := rfl

/-- Casting a based-lift along an equality of the base morphisms induces
an equivalence of the based-lifts. -/
@[simps]
def cast {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (h : f = f') :
(x ⟶[f] y) ≃ (x ⟶[f'] y) where
  toFun := fun g ↦ ⟨g.hom, by rw [←h, g.over]⟩
  invFun := fun g ↦ ⟨g.hom, by rw [h, g.over]⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

lemma cast_hom {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {g : x ⟶[f] y} {h : f = f'} :
    (cast h g).hom = g.hom := rfl

lemma eq_id_of_hom_eq_id {c : C} {x : P⁻¹ c} {g : x ⟶[𝟙 c] x} :
(g.hom = 𝟙 x.1) ↔ (g = id x) := by aesop

/-
lemma hom_comp_cast  {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {f : c ⟶ d'}
{h₁ : f = f₁ ≫ f₂} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} {g₁ : x ⟶[f₁] y}
{g₂ : y ⟶[f₂] z} {g : x ⟶[f] z} : g₁.hom ≫ g₂.hom = g.hom ↔
g₁ ≫[l] g₂ = cast h₁ g := by
  constructor
  intro
  simp_all only [comp]
  rfl
  intro h
  rw [← comp_hom, h, cast_hom]

@[simp]
lemma id_comp_cast {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d}
{g : x ⟶[f] y} : BasedLift.id x  ≫[l] g = (BasedLift.cast ((id_comp f).symm : f = 𝟙 c ≫ f)) g := by
  simp_all only [comp, id, id_comp]; rfl
-/

/-- Casting equivalence along postcomposition with the identity morphism. -/
@[simp]
def castIdComp  {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} :
    (x ⟶[(𝟙 c) ≫ f] y) ≃ (x ⟶[f] y) := cast (id_comp f)

/-- Casting equivalence along precomposition with the identity morphism. -/
@[simp]
def castCompId  {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} :
    (x ⟶[f ≫ (𝟙 d) ] y)  ≃ (x ⟶[f] y) := cast (comp_id f)

@[simp]
def castAssoc {c' c d d' : C} {u' : c' ⟶ c} {f : c ⟶ d} {u : d ⟶ d'} {x : P⁻¹ c'}
{y : P⁻¹ d'} : (x ⟶[(u' ≫ f) ≫ u] y) ≃ (x ⟶[u' ≫ (f ≫ u)] y) := cast (Category.assoc u' f u)

@[simps]
def castOfeqToHom {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} :
(x ⟶[f] y) ≃ (x.1 ⟶[(eqToHom x.2) ≫ f] y) where
  toFun := fun g => ⟨g.hom, by simp [g.over]⟩
  invFun := fun g => ⟨g.hom, by simp [g.over]⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-
lemma assoc {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'}
{x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :
    ((g₁ ≫ₗ g₂) ≫ₗ g₃) =  (g₁ ≫ₗ g₂ ≫ₗ g₃) := by
  simp only [comp, Category.assoc, castAssoc, cast]
-/

/-- The composition of based-lifts is associative up to casting along equalities
of the base morphisms. -/
@[simp]
lemma assoc {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'} {x : P⁻¹ c}
    {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :
    ((g₁ ≫[l] g₂) ≫[l] g₃) = castAssoc.invFun (g₁ ≫[l] g₂ ≫[l] g₃) := by
  simp only [comp, Category.assoc, castAssoc, cast]

@[simp]
lemma assoc_inv {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'}
{x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :
castAssoc.toFun ((g₁ ≫[l] g₂) ≫[l] g₃) =  (g₁ ≫[l] (g₂ ≫[l] g₃)) := by
  simp only [comp, Category.assoc, castAssoc, cast]

lemma tauto_comp_cast {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} :
    tauto (g ≫ g') = cast (P.map_comp g g').symm (tauto g ≫[l] tauto g') := rfl
end BasedLift

namespace Lift

variable {P : E ⥤ C}

instance  : CoeOut (Lift P f y) (Σ x : E, (x : E) ⟶ y) where
  coe := fun l ↦ ⟨l.src, l.based_lift.hom⟩

@[simp]
lemma over_base (f : c ⟶ d) (y : P⁻¹ d) (g : Lift P f y) :
    P.map g.based_lift.hom = (eqToHom (g.src.over)) ≫ f ≫ eqToHom (y.over).symm :=
  BasedLift.over_base g.based_lift

def homOf (g : Lift P f y) : (g.src : E) ⟶ y := g.based_lift.hom

/-- Regarding a morphism in Lift P f as a morphism in the total category E. -/
instance {g : Lift P f y} : CoeDep (Lift P f y) (g) ((g.src : E) ⟶ (y : E)) where
  coe := g.based_lift.hom

/-- The identity lift. -/
def id {c : C} (x : P⁻¹ c) : Lift P (𝟙 c) x := ⟨x, BasedLift.id x⟩

/-The composition of lifts -/
-- def comp {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {y : P⁻¹ d} {z : P⁻¹ d'}
-- (g₁ : Lift P f₁ y) (g₂ : Lift P f₂ z) : Lift P (f₁ ≫ f₂) z :=
-- ⟨g₁.src, BasedLift.comp g₁.based_lift g₂.based_lift⟩

end Lift

/-- The type of iso-based-lifts of an isomorphism in the base with fixed source
and target. -/
class IsoBasedLift {C E : Type*} [Category C] [Category E] {P : E ⥤ C} {c d : C} (f : c ⟶ d) [IsIso f] (x : P⁻¹ c) (y : P⁻¹ d) extends (x ⟶[f] y) where
  is_iso_hom : IsIso hom

namespace IsoBasedLift

variable {P : E ⥤ C} {c d : C} {f : c ⟶ d} [IsIso f] {x : P⁻¹ c} {y : P⁻¹ d}

notation x " ⟶[≅" f "] " y => IsoBasedLift (P:= _) f x y

/-- Any iso-based-lift is in particular an isomorphism. -/
instance instIsoOfIsoBasedLift (g : (x ⟶[≅f] y)) : IsIso g.hom := g.is_iso_hom

/-- Coercion from IsoBasedLift to BasedLift -/
instance : Coe (x ⟶[≅f] y) (x ⟶[f] y) where
  coe := fun l => ⟨l.hom, l.over⟩

noncomputable
def Inv (g : x ⟶[≅f] y) : (y ⟶[≅ inv f] x) where
  hom := inv g.hom
  over := by simp only [Iso.symm_hom, Functor.map_inv, BasedLift.over_base, IsIso.inv_comp,
    inv_eqToHom, IsIso.Iso.inv_hom,
  assoc, eqToHom_trans, eqToHom_refl, comp_id]
  is_iso_hom := IsIso.inv_isIso

end IsoBasedLift

/-- A lift `g : x ⟶[f] y` over a base morphism `f` is cartesian if for every
morphism `u` in the base and every lift `g' : x ⟶[u ≫ f] z` over the composite
 `u ≫ f`, there is a unique morphism `l : y ⟶[u] z` over `u` such that
 `l ≫ g = g'`. -/
class CartesianBasedLift {P : E ⥤ C} {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) where
uniq_lift : ∀ ⦃c' : C⦄ ⦃z : P⁻¹ c'⦄ (u : c' ⟶ c) (g' : z ⟶[u ≫ f]  y), Unique { l :  z ⟶[u] x // (BasedLift.comp l g) = g' }

/-- A morphism `g : x ⟶[f] y` over `f` is cocartesian if for all morphisms `u` in the base and
`g' : x ⟶[f ≫ u] z` over the composite `f ≫ u`, there is a unique morphism `l : y ⟶[u] z`
over `u` such that `g ≫ l = g'`. -/
class CoCartesianBasedLift {P : E ⥤ C} {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) where
uniq_colift : ∀ ⦃d' : C⦄ ⦃z : P⁻¹ d'⦄ (u : d ⟶ d') (g' : x ⟶[f ≫ u]  z), Unique { l :  y ⟶[u] z // (BasedLift.comp g l) = g' }

namespace CartesianBasedLift

open BasedLift

variable {P : E ⥤ C} {c' c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {x' : P⁻¹ c'} (g : x ⟶[f] y) [CartesianBasedLift (P:= P) g]

/-- `gaplift g u g'` is the canonical map from a lift `g' : x' ⟶[u ≫ f] y` to a
cartesian lift `g` of `f`. -/
def gaplift (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : x' ⟶[u] x :=
(CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').default.val

/-- A variant of `gaplift` for `g' : x' ⟶[f'] y` with casting along `f' = u ≫ f` baked into the definition. -/
def gaplift' (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y) (h : f' = u ≫ f) : x' ⟶[u] x :=
(CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u (BasedLift.cast h g')).default.val

@[simp]
lemma gaplift_cast (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y)
(h : f' = u ≫ f) : gaplift' g u g' h = gaplift g u (BasedLift.cast h g') := rfl

/-- The composition of the gap lift and the cartesian lift is the given lift -/
@[simp]
lemma gaplift_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) :
((gaplift g u g') ≫[l] g) = g' :=
(CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').default.property

/-- A variant of the gaplift property for equality of the underlying morphisms. -/
@[simp]
lemma gaplift_hom_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : (gaplift g u g').hom ≫  g.hom = g'.hom := by rw [← BasedLift.comp_hom _ _]; congr 1; exact gaplift_property g u g'

/-- The uniqueness part of the universal property of the gap lift. -/
@[simp]
lemma gaplift_uniq {u : c' ⟶ c} (g' : x' ⟶[u ≫ f] y) (v : x' ⟶[u] x)
(hv : (v ≫[l] g) = g') : v = gaplift (g:= g) u g' := by
  simp [gaplift]; rw [← (CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').uniq ⟨v,hv⟩]

/-- A variant of the  uniqueness lemma. -/
@[simp]
lemma gaplift_uniq' {u : c' ⟶ c} (v : x' ⟶[u] x) (v' : x' ⟶[u] x) (hv : (v ≫[l] g) = v' ≫[l] g) :
    v = v' := gaplift_uniq g (v' ≫[l] g) v hv ▸ (gaplift_uniq _ _ _ rfl).symm

/-- The gaplift of any cartesian based-lift with respect to itself is the identity. -/
@[simp]
lemma gaplift'_self : gaplift' g (𝟙 c) g (id_comp f).symm = BasedLift.id x := by
  rw [gaplift_cast]
  apply (gaplift_uniq _ _ _ _).symm
  simp only [BasedLift.comp, BasedLift.id, id_comp]
  rfl

variable {g}

/-
/-- The composition of gaplifts with respect to morphisms `u' : c'' ⟶ c` and
`u : c' ⟶ c` is the gap lift of the composition `u' ≫ u`. -/
@[simp]
lemma gaplift_comp {u : c' ⟶ c} {u' : c'' ⟶ c'} {x'' : P⁻¹ c''}
{g' : x' ⟶[u ≫ f] y} [CartesianBasedLift (P:= P) (f:= u ≫ f) g']
{g'' : x'' ⟶[u' ≫ u ≫ f] y} :
(gaplift  (g:= g') u' g'') ≫[l] (gaplift (g:= g) u g') =
gaplift (g:= g) (u' ≫ u) (BasedLift.castAssoc.invFun g'') := by
  refine gaplift_uniq (f:= f) g (castAssoc.invFun g'') ((gaplift (g:= g') u' g'') ≫[l] (gaplift (g:= g) u g')) (by rw [BasedLift.assoc]; simp only [gaplift_property])

/-- The identity based-lift is cartesian. -/
instance instId {x : P⁻¹ c} : CartesianBasedLift (P:= P) (BasedLift.id x) where
  uniq_lift := fun c' z u g' => {
    default := ⟨castCompId g', by simp_all only [BasedLift.comp, castCompId, cast_apply_hom, BasedLift.id, comp_id]⟩
    uniq := by aesop
  }

/-- Cartesian based-lifts are closed under composition. -/
instance instComp  {c d d' : C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : x ⟶[f₁] y) [CartesianBasedLift (P:= P) g₁] (g₂ : y ⟶[f₂] z) [CartesianBasedLift (P:= P) g₂] : CartesianBasedLift (P:= P) (g₁ ≫[l] g₂) where
  uniq_lift := fun c' w u g' => {
    default := ⟨gaplift g₁ u (gaplift g₂ (u ≫ f₁) (castAssoc.invFun g')), by rw [← BasedLift.assoc_inv, gaplift_property g₁ _ _, gaplift_property g₂ _ _]; simp⟩
    uniq := by intro ⟨l, hl⟩; simp; apply gaplift_uniq; apply gaplift_uniq; rw [BasedLift.assoc]; simp; exact hl}

/-- The cancellation lemma for cartesian based-lifts. If  `g₂ : y ⟶[f₂] z` and
`g₁ ≫[l] g₂ : z ⟶[f₂] z` are cartesian then `g₁` is cartesian. -/
@[simp]
lemma instCancel {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} [CartesianBasedLift (P:= P) g₂] [CartesianBasedLift (g₁ ≫[l] g₂)] : CartesianBasedLift g₁ where
  uniq_lift := fun c' z' u₁ g₁' => {
    default := {
      val := gaplift (g:= g₁ ≫[l]  g₂) u₁ (castAssoc (g₁' ≫[l] g₂))
      property := by apply gaplift_uniq' g₂ _ (g₁'); rw [BasedLift.assoc]; rw [ gaplift_property _ _ _]; simp
    }
    uniq := by intro l
               cases' l with l hl
               have : (l ≫[l] (g₁ ≫[l] g₂)) = castAssoc (g₁' ≫[l] g₂) := by simp only [← BasedLift.assoc_inv]; rw [hl]; simp
               simp
               apply gaplift_uniq (g₁ ≫[l] g₂) (castAssoc (g₁' ≫[l] g₂)) l (this)
  }
-/

end CartesianBasedLift

/-- A morphism is cartesian if the gap map is unique. -/
def isCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) : Prop :=
∀ ⦃z: E⦄ (u : P.obj z ⟶ P.obj x) (g' : Fiber.tauto z ⟶[u ≫ P.map g] y),
∃! (l : Fiber.tauto z ⟶[u] x), (l.hom ≫ g) = g'.hom

/-- The class of cartesian morphisms -/
def CartMor (P : E ⥤ C) : MorphismProperty E :=  fun _ _ g => isCartesianMorphism (P:= P) g

section CartMor

open MorphismProperty CartesianBasedLift BasedLift

variable {P : E ⥤ C} {x y : E}

/--   `gapmap g gcart u g'` is a unique morphism `l` over `u` such that `l ≫ g = g'`. -/
noncomputable
def gapmap (g : x ⟶ y) (gcart : CartMor P g) {z : E} (u : P.obj z ⟶ P.obj x) (g' : Fiber.tauto z ⟶[u ≫ P.map g] y) : (z : E) ⟶ x :=  (Classical.choose (gcart u g')).hom

@[simp]
lemma gapmap_over {z : E} {u : P.obj z ⟶ P.obj x} {g' : Fiber.tauto z ⟶[u ≫ P.map g] Fiber.tauto y} : P.map (gapmap g gcart u g') = u := by simp [gapmap]

/-- The composition of the gap map of a map g' and the cartesian lift g is the given map g'. -/
@[simp]
lemma gapmap_property {g : x ⟶ y} {gcart : CartMor P g} {z : E} {u : P.obj z ⟶ P.obj x} {g' :
    Fiber.tauto z ⟶[u ≫ P.map g] y} : (gapmap g gcart u g') ≫ g = g'.hom :=
  (Classical.choose_spec (gcart u g')).1

/-
@[simp]
lemma gapmap_uniq {z : E} {u : P.obj z ⟶ P.obj x} {g' : Fiber.tauto z ⟶[u ≫ P.map g] Fiber.tauto y}
    (v : Fiber.tauto z ⟶[u] x) (hv : v.hom ≫ g = g'.hom) : v.hom = gapmap g gcart u g' := by
  have : v = Classical.choose (gcart u g') := by
    refine (Classical.choose_spec (gcart u g')).2 v hv
  rw [this]
  simp [gapmap]

@[simp]
lemma gapmap_uniq' (g : x ⟶ y) (gcart : CartMor P g) {c : C} {z : P⁻¹ c}
(v₁ : (z : E) ⟶ x) (v₂ : (z : E) ⟶ x) (hv : v₁ ≫ g = v₂ ≫ g)
(hv' : P.map v₁ = P.map v₂) : v₁ = v₂ := by
  let v₁' := tauto (P:= P) v₁
  let v₂' := tauto (P:= P) v₂
  let g' := v₂' ≫[l] tauto g
  have : P.map v₁ ≫ P.map g = P.map v₂ ≫ P.map g  := by rw [← P.map_comp, ← P.map_comp, hv]
  have hv₁ : v₁'.hom ≫ g = g'.hom := by simp_all only [Fiber.tauto_over, tauto_hom, BasedLift.comp]
  have hv₂' : (BasedLift.cast hv'.symm v₂').hom ≫ g = (BasedLift.cast  (this.symm) g').hom := by
    simp only [Fiber.tauto_over, tauto_hom, BasedLift.comp, cast_apply_hom]
  have H' := (gcart (P.map v₁) (BasedLift.cast (this.symm) g')).unique hv₁ hv₂'
  injection H'
-/

/-- `cart_id e` says that the identity morphism `𝟙 e` is cartesian. -/
lemma cart_id (e : E) : CartMor P (𝟙 e) := fun z u g' ↦ by
  stop
  use ⟨(BasedLift.cast ((whisker_eq u (P.map_id e)).trans (comp_id _))).toFun g', by aesop⟩
  constructor
  simp_all only [Fiber.tauto, Equiv.toFun_as_coe, cast_apply_hom, comp_id]
  intro v hv; ext; aesop

/-
/-- Cartesian morphisms are closed under composition. -/
@[simp]
lemma cart_comp : StableUnderComposition (CartMor P) := fun x y z f g hf hg w u g' => by
  cases' (hg (u ≫ P.map f) ((BasedLift.cast ((u ≫= P.map_comp f g).trans (Category.assoc u _ _).symm )).toFun g')) with lg hlg
  cases' (hf u lg) with lf hlf
  use lf
  constructor
  · simp only [Fiber.tauto_over, CartMor, ← Category.assoc, hlf.1, hlg.1, BasedLift.cast]
  · intro v hv
    have : v.hom ≫ f = lg.hom := (BasedLift.comp_hom').mp (hlg.2 (v ≫[l] f) (hv ▸ assoc v.hom f g))
    apply hlf.2 v this

/-- Every isomorphism is cartesian. -/
@[simp]
lemma cart_iso {x y : E} (g : x ⟶ y) [IsIso g] : CartMor P g := fun z u g' => by
  use (BasedLift.cast (by simp)).toFun (g' ≫[l] BasedLift.tauto (inv g))
  simp
  intro v hv
  congr! 1
  aesop

/-- The property CartMor respect isomorphisms -/
lemma cart_iso_closed : RespectsIso (CartMor P) where
  left := fun e g hg => by apply cart_comp; exact cart_iso e.hom; assumption
  right := fun e g hg => by apply cart_comp; assumption; exact cart_iso e.hom

open IsPullback
/--Cartesian morphisms are closed under base change: Given a pullback square
```
  P---g'-->X
  |        |
 f'        f
  |        |
  v        v
  Y---g--->Z
```
if g is cartesian, then so is g'.-/
lemma cart_pullback [PreservesLimitsOfShape WalkingCospan P] : StableUnderBaseChange (CartMor P) := fun x y w z f g f' g' pb gcart  => by
intro w' u k
have pbw : P.map g' ≫ P.map f = P.map f' ≫ P.map g := by rw [← P.map_comp, ← P.map_comp, pb.w]
have pbw' : P.map k.hom ≫ P.map f  = (u ≫ P.map f') ≫ P.map g := by rw [Category.assoc]; rw [u ≫= pbw.symm]; simp only [Fiber.tauto_over, over_base, eqToHom_refl, comp_id, id_comp, Category.assoc]
have hk : P.map k.hom = u ≫ P.map g' := by simp only [Fiber.tauto_over, over_base, eqToHom_refl, comp_id, id_comp, Category.assoc]
let v' :  w' ⟶ y := gapmap g gcart (u ≫ P.map f') (BasedLift.cast pbw' (BasedLift.cast (hk.symm) k ≫[l] tauto f))
have : k.hom ≫ f = v' ≫ g := by simp [v', gapmap_property]
let pbc₁ : PullbackCone f g := PullbackCone.mk k.hom v' this
let pb₁ := pb |> IsPullback.flip |> isLimit
let pb₂ := isLimitPullbackConeMapOfIsLimit P (f:= f) (g:= g) pb.w.symm (pb |> IsPullback.flip |> isLimit)
let v : w' ⟶ w := pb₁.lift pbc₁
have hv₁ : P.map v ≫ P.map g' = P.map k.hom := by rw [← P.map_comp]; congr 1; exact pb₁.fac pbc₁ WalkingCospan.left
have hu₁ : u ≫ P.map g' = P.map k.hom := by simp only [Fiber.tauto_over, over_base, eqToHom_refl, comp_id, id_comp]
have hv₂' : v ≫ f' = v' := pb₁.fac pbc₁ WalkingCospan.right
have hv₂ : P.map v ≫ P.map f' = u ≫ P.map f' := by rw [← P.map_comp, hv₂']; simp only [gapmap_over]
have hv₃ : P.map v = u := by apply PullbackCone.IsLimit.hom_ext pb₂; simp only [PullbackCone.mk_π_app_left]; rw [hv₁, ← hu₁]; simp only [PullbackCone.mk_π_app_right]; rw [hv₂]
use ⟨v, by rw [hv₃]; simp⟩
--dsimp
constructor
· apply pb₁.fac pbc₁ WalkingCospan.left
. intro l hl
  have : (l ≫[l] tauto f').hom ≫ g = (k ≫[l] tauto f).hom := by simp [comp_hom]; rw [pb.w, ← Category.assoc, hl, ← comp_tauto_hom]
  have : l.hom ≫ f' = v' := by rw [← comp_tauto_hom]; apply gapmap_uniq (l ≫[l] tauto f') this
  have : l.hom = v := by apply PullbackCone.IsLimit.hom_ext pb₁;
                         · simp [cone_fst]; rw [hl]; symm; exact pb₁.fac pbc₁ WalkingCospan.left
                         · simp [cone_snd]; rw [this]; symm; exact pb₁.fac pbc₁ WalkingCospan.right
  ext; assumption
-/

end CartMor

section CartLift

variable {P : E ⥤ C} {c d : C}

/-- Given a morphism `f` in the base category `C`, the type
`CartLifts P f src tgt` consists of the based-lifts of `f` with
the source `src` and the target `tgt` which are cartesian with respect to `P`. -/
class CartBasedLifts (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) extends BasedLift P f src tgt where
is_cart : CartesianBasedLift (P:= P) toBasedLift

instance instCoeHomOfCartBasedLift {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) : CoeOut (CartBasedLifts P f src tgt) (src.1 ⟶ tgt.1) where
  coe := fun l ↦ l.1.hom

/-- The type of cartesian lifts of a morphism `f` with fixed target. -/
class CartLift (f : c ⟶ d) (y : P⁻¹ d) extends Lift P f y where
is_cart : CartesianBasedLift (P:= P) lift

def CartLift.homOf {f : c ⟶ d} {y : P⁻¹ d} (g : CartLift f y) : (g.src : E) ⟶ y := g.based_lift.hom

instance instCoeLiftOfCartLift {c d : C} {f : c ⟶ d} {y : P⁻¹ d} : Coe (CartLift (P:= P) f y) (Lift P f y) where
  coe := fun l ↦ l.toLift

class CoCartLift (f : c ⟶ d) (x : P⁻¹ c) extends CoLift P f x where
is_cart : CoCartesianBasedLift (P:= P) colift

/--Mere existence of a cartesian lift with fixed target. -/
def HasCartLift (f : c ⟶ d) (y : P⁻¹ d) := Nonempty (CartLift (P:= P) f y)

def HasCoCartLift (f : c ⟶ d) (x : P⁻¹ c) := Nonempty (CoCartLift (P:= P) f x)

end CartLift



abbrev Cart ( _ : E ⥤ C) := E

/-- The subcategory of cartesian morphisms. -/
instance instCategoryCart {P : E ⥤ C} : Category (Cart P) where
  Hom x y := { f : x ⟶ y |  CartMor (P:= P) f }
  id x := ⟨𝟙 x, cart_id x⟩
  comp := @fun x y z f g => ⟨ f.1 ≫ g.1, sorry⟩  --cart_comp f.1 g.1 f.2 g.2⟩

namespace Cart

/-- The forgetful functor from the category of cartesian morphisms to the domain category. -/
def forget {P : E ⥤ C} : Cart P ⥤ E where
obj := fun x => x
map := @fun x y f => f

end Cart

end CategoryTheory
