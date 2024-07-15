/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Grothendieck
import GroupoidModel.FibrationForMathlib.Displayed.Fiber
import GroupoidModel.FibrationForMathlib.Displayed.Basic
import GroupoidModel.FibrationForMathlib.Displayed.Cartesian

/-!
# Fibrations for displayed categories

Given a displayed category structure on a type family `F : C → Type*`, the structure `ClovenFibration F`
provides the structure of a cleavage for `F`. Specialized to the display category structure of a functor,
`ClovenFibration (P⁻¹ .)` provides the structure of a cleavage for a functor `P : E ⥤ C`.

## Main declarations

- `Display.ClovenFibration.lift` is the lift function of a cleavage of a displayed category.
- `Functor.ClovenFibration.lift` is the lift function of a cleavage of a functor.

- `Display.ClovenFibration.transport` is the transport function of a cleavage of a displayed category.
- `Functor.transport` is the transport function of a functor with a cleavage.

-/


--set_option autoImplicit true
-- set_option pp.explicit false
-- set_option pp.notation true
-- set_option trace.simps.verbose true
-- set_option trace.Meta.synthInstance.instances true
-- set_option trace.Meta.synthInstance true
-- set_option pp.coercions true
--set_option pp.proofs.threshold 20

namespace CategoryTheory

open Category Opposite BasedLift Fiber Display

namespace Display

variable {C : Type*} [Category C] (F : C → Type*) [Display F]

/-- A Cloven fibration structure provides for every morphism `f` and every
object in the fiber of the codomain of `f` a specified cartesian lift of `f`. -/
class ClovenFibration where
  /-- A lift function which assigns to a morphism `f` and an
  object in the fiber of the codomain of `f` a cartesian lift of `f`. -/
  lift {I J : C} (f : I ⟶ J) (Y : F J) : CartLift f Y

/-- A fibration structure provides for every morphism `f` and every
object in the fiber of the codomain of `f` some cartesian lift of `f`. -/
class Fibration where
  /-- A lift function which provides for a morphism `f` and an object in the fiber of the
  codomain of `f` the existene of a cartesian lift of `f`. -/
  lift {I J : C} (f : I ⟶ J) (Y : F J) : HasCartLift f Y

class Transport where
  transport {I J : C} (f : I ⟶ J) (Y : F J) : F I

--notation f " ⋆ " y  : 10 => Transport.transport f y
scoped infixr:80 " ⋆ "  => Transport.transport -- NtS: infix right ensures that `f ⋆ y ⋆ z` is parsed as `f ⋆ (y ⋆ z)`

end Display

variable {C E : Type*} [Category C] [Category E]
namespace Functor

/-- A functor `P : E ⥤ C` is a cloven fibration if the associated displayed structure of `P` is a
cloven fibration. -/
abbrev ClovenFibration (P : E ⥤ C) := Display.ClovenFibration (P⁻¹ .)

/-- A functor `P : E ⥤ C` is a fibration if the associated displayed structure of `P` is a
fibration. -/
abbrev Fibration (P : E ⥤ C) := Display.Fibration (P⁻¹ .)

abbrev StreetFibration (P : E ⥤ C) := Display.Fibration (P⁻¹ᵉ .)

/-- A transport structure for a functor `P : E ⥤ C` consists of a transport function for the
associated displayed structure of `P`. -/
abbrev Transport (P : E ⥤ C) := Display.Transport (P⁻¹ .)

abbrev transport {P : E ⥤ C} [P.Transport] {I J : C} (f : I ⟶ J) (Y : P⁻¹ J) :=
  Display.Transport.transport f Y

lemma transport_over_eq {I J : C} {P : E ⥤ C} [Functor.Transport P] (f : I ⟶ J) (Y : P⁻¹ J) :
    P.obj (f ⋆ Y) = I := by
  simp only [Fiber.over]

end Functor

namespace Display

open Total

variable {C : Type*} [Category C] (F : C → Type*)
variable [Display F] [ClovenFibration F]

@[simps!]
instance transport : Transport F where
  transport f X := (ClovenFibration.lift f X).src

example {I J K : C} (f : I ⟶ J) (g : J ⟶ K) (Z : F K) : f ⋆ g ⋆ Z = f ⋆ (g ⋆ Z) := rfl

@[simp]
def tp {I J : C}  (f : I ⟶ J) : (F J) → (F I) := fun Y ↦ f ⋆ Y

attribute [instance] Display.Total.category

@[simp]
def totalLift {I J : C} (f : I ⟶ J) (Y : F J) :
  (Total.mk (f ⋆ Y) : ∫ F) ⟶ (Total.mk Y : ∫ F) :=
⟨f, (ClovenFibration.lift f Y).homOver⟩

end Display

open Display

namespace Functor.ClovenFibration

open Cartesian

variable {P : E ⥤ C} [P.ClovenFibration]

variable {F}
/-- A cloven fibration has transports along morphisms of the base. -/
@[simps!]
instance transport : P.Transport where
  transport f X := (ClovenFibration.lift f X).src

theorem transport_trans {I J K : C} (f : I ⟶ J) (g : J ⟶ K) (Z : P⁻¹ K) : f ⋆ g ⋆ Z = f ⋆ (g ⋆ Z) := rfl

@[simp]
def tp {I J : C}  (f : I ⟶ J) : (P⁻¹ J) → (P⁻¹ I) := fun Y ↦ f ⋆ Y

/-- The lift of a morphism `f`, ending at `Y`. -/
 def basedLift {I J : C} (f : I ⟶ J) (Y : P⁻¹ J) : (f ⋆ Y) ⟶[f] Y :=
  (ClovenFibration.lift f Y).homOver

/-- The lift `(f ⋆ Y) ⟶[f] Y` is cartesian. -/
 instance instCartesianBasedLift {I J : C} {f : I ⟶ J} {Y : P⁻¹ J} : Cartesian (basedLift f Y) :=
   (ClovenFibration.lift f Y).is_cart

@[simp]
def basedLiftHom {I J : C} (f : I ⟶ J) (Y : P⁻¹ J) : (f ⋆ Y : E) ⟶ (Y : E) :=
(ClovenFibration.lift f Y).homOver.hom

@[simp]
lemma basedLiftHom_over {I J : C} (f : I ⟶ J) (Y : P⁻¹ J) :
    P.map (basedLiftHom f Y) =
    (eqToHom (transport_over_eq (P:= P) f Y)) ≫ f ≫ eqToHom ((Fiber.over Y).symm) := by
  simp only [transport_transport, basedLiftHom, over_eq']

instance cartLiftOf {I J : C} (f : I ⟶ J) (Y : P⁻¹ J) : CartLift f Y := ClovenFibration.lift f Y

section Vertical

-- fiberHomOfBasedLiftHom
@[simp]
def vertOfBasedLift {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} (g : X ⟶[f] Y) : X ⟶[𝟙 I] f ⋆ Y :=
   (Cartesian.gap (basedLift f Y) (u:= 𝟙 I) (g.cast (id_comp f).symm))

--basedLiftOfFiberHom'
/-- Making a morphism in the fiber category `P⁻¹ I` into a vertical lift over `𝟙 I` -/
@[simp]
def vertOfFiberHom {I : C} {X Y : P⁻¹ I} (g : X ⟶ Y) : X ⟶[𝟙 I] Y :=
  ⟨g.1, by simp [g.2]⟩

notation:75 (name := Base_lift_stx) g "ᵛ" => vertOfFiberHom g

/-- Making a vertical lift over `𝟙 I` into a morphism in the fiber category `P⁻¹ I` -/
@[simp]
def fibreHomOfVert {I : C} {X Y : P⁻¹ I} (f : X ⟶[𝟙 I] Y) : X ⟶ Y :=
  ⟨f.hom, by simp⟩

notation:85 (name := Fibre_lift_stx) f "ᶠ" => fibreHomOfVert f

lemma vert_fiberHom_id {I : C} {X Y : P⁻¹ I} (g : X ⟶ Y) : (g ᵛ)ᶠ = g := rfl

lemma fiberHom_vert_id {I : C} {X Y : P⁻¹ I} (g : X ⟶[𝟙 I] Y) : (g ᶠ)ᵛ = g := rfl

lemma fiber_lift_comp {I : C} {X Y Z : P⁻¹ I} (f : X ⟶[𝟙 I] Y) (g : Y ⟶[𝟙 I] Z) :
     fᶠ ≫ gᶠ = (BasedLift.cast (comp_id (𝟙 I)) (f ≫ₒ g))ᶠ := by
   simp [fibreHomOfVert]
   sorry

lemma fiberLift_congr {I : C} {X Y: P⁻¹ I} (f g: X ⟶[𝟙 I] Y) :
     fᶠ = gᶠ ↔ f = g := by
   apply Iff.intro
   · intro eq
     ext
     simp [fibreHomOfVert] at eq
     injection eq
   · intro eq
     aesop_cat

/-- The equivalence of lifts `X ⟶[𝟙 I ≫ f] Y` and `X ⟶[𝟙 I] f ⋆ Y`.  -/
def equivBasedLiftVertAux {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
     (X ⟶[𝟙 I ≫ f] Y) ≃ (X ⟶[𝟙 I] f ⋆ Y) where
   toFun g := Cartesian.gap (basedLift f Y) (u:= 𝟙 I) g
   invFun h := h ≫ₒ basedLift f Y
   left_inv := by
     intro g
     simp only [transport_transport, Cartesian.gap_prop]
   right_inv := by
     intro h
     symm
     exact Cartesian.gaplift_uniq (basedLift f Y) (h ≫ₒ basedLift f Y) h (by rfl)

@[simps!]
def equivBasedLiftVert {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
    (X ⟶[f] Y) ≃ (X ⟶[𝟙 I] f ⋆ Y) :=
  Equiv.trans (Display.castEquiv (id_comp f).symm) equivBasedLiftVertAux

-- equivFiberCatHomBasedLift
/-- The equivalence of lifts `X ⟶[f] Y` and morphisms `X ⟶  f ⋆ Y` in the fiber category `P⁻¹ I`. -/
@[simps!]
def equivVertFiberHom {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
     (X ⟶[𝟙 I] f ⋆ Y) ≃ (X ⟶ f ⋆ Y) where
   toFun g := ⟨g.hom, by simp⟩
   invFun h := ⟨h.1, by simp⟩
   left_inv := by intro _; rfl
   right_inv := by intro _; rfl

@[simps!]
def equivBasedLiftFiberHom {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
     (X ⟶[f] Y) ≃ (X ⟶ f ⋆ Y) :=
   Equiv.trans equivBasedLiftVert equivVertFiberHom

end Vertical

lemma inv_comp {I: C} {X X' : P⁻¹ I} (g : X ⟶ X') [Cartesian (gᵛ)] :
    (gap (gᵛ) ((comp_id (𝟙 I)).symm ▸ (𝟙ₒ X')))ᶠ ≫ g = (𝟙ₒ X')ᶠ := by
  simp [gap]
  sorry

def map {I J : C} (f : I ⟶ J) : (P⁻¹ J) ⥤ (P⁻¹ I) where
  obj := Transport.transport f
  map {X Y} g :=  by
    let g₁ : (f ⋆ X) ⟶[f ≫ (𝟙 J)] Y := (basedLift f X) ≫ₒ (gᵛ)
    let g₂ : (f ⋆ X) ⟶[(𝟙 I) ≫ f] Y := ((basedLift f X) ≫ₒ (gᵛ)).cast <| by simp
    let g₃ : (f ⋆ X) ⟶[f] Y := g₁.cast (comp_id f)
    let g₄ : (f ⋆ Y) ⟶[f] Y := basedLift f Y
    refine ⟨?_, ?_⟩
    · exact (gap g₄ g₂).hom
    · simp only [Display.transport_transport, over_eq', id_comp, eqToHom_trans]
  map_id := by
    intro X
    simp
    symm
    congr 1
    sorry
    -- refine gaplift_uniq (basedLift f X) ((𝟙ₒ X) ≫ₒ (basedLift f X)) (basedLift.Id (f ⋆ Y)) ?_
    -- intro x; simp; symm; refine gap_uniq (BasedLift f x) (BasedLift.Comp (BasedLift f x) (BasedLift.Id x)  ) (BasedLift.Id (CoTransport (P:= P) f x)) ?_ -- apply Classical.choose_spec-- uniqueness of UP of lift
  --apply ((colift f x).is_cart.uniq_colift (𝟙 d) _).uniq ⟨(BasedLift.Id (CoTransport (P:= P) f x)), sorry⟩  -- apply Classical.choose_spec-- uniqueness of UP of lift
  map_comp := sorry -- uniquess of UP of lift

variable (P)

def straightening : Cᵒᵖ  ⥤ Cat where
  obj I := Cat.of (P⁻¹ (unop I))
  map {I J} f := Functor.ClovenFibration.map (unop f)
  map_id := by sorry
  map_comp := by sorry

#check Functor.leftOp

-- def unstraightening (G : Cᵒᵖ  ⥤ Cat) : (Grothendieck G)ᵒᵖ ⥤ C :=
-- (Grothendieck.forget G.rightOp)


end Functor.ClovenFibration

end CategoryTheory
