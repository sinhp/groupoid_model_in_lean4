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
import GroupoidModel.FibrationForMathlib.Displayed.Fibre
import GroupoidModel.FibrationForMathlib.Displayed.Basic
import GroupoidModel.FibrationForMathlib.Displayed.Cartesian



set_option autoImplicit true
-- set_option pp.explicit false
--set_option pp.notation true
-- set_option trace.simps.verbose true
--set_option trace.Meta.synthInstance.instances true
--set_option trace.Meta.synthInstance true
-- set_option pp.coercions true

namespace CategoryTheory

open Category Opposite BasedLift Fibre Display

/-
namespace Display

variable {C : Type*} [Category C] (F : C → Type*) [Display F]

#check CartLift

/-- A Cloven fibration structure provides for every morphism `f` and every
object in the fiber of the codomain of `f` a specified cartesian lift of `f`. -/
class ClovenFibration where
/-- A lift function which assigns to a morphism `f` and an
object in the fiber of the codomain of `f` a cartesian lift of `f`. -/
lift {I J : C} (f : I ⟶ J) (Y : F J) : CartLift f Y

/-- A fibration structure provides for every morphism `f` and every
object in the fiber of the codomain of `f` some cartesian lift of `f`. -/
class Fibration  where
/-- A lift function which provides for a morphism `f` and an object in the fiber of the
codomain of `f` the existene of a cartesian lift of `f`. -/
lift {I J : C} (f : I ⟶ J) (Y : F J) : HasCartLift f Y

class Transport where
  transport {I J : C} (f : I ⟶ J) (Y : F J) : F I

--notation f " ⋆ " y  : 10 => Transport.transport f y
scoped infixr:80 " ⋆ "  => Transport.transport -- NtS: infix right ensures that `f ⋆ y ⋆ z` is parsed as `f ⋆ (y ⋆ z)`

end Display

variable {C E : Type*} [Category C] [Category E]


/-- A functor `P : E ⥤ C` is a cloven fibration if the associated displayed structure of `P` is a
cloven fibration. -/
abbrev ClovenFibration (P : E ⥤ C) := Display.ClovenFibration (P⁻¹ .)

/-- A functor `P : E ⥤ C` is a fibration if the associated displayed structure of `P` is a
fibration. -/
abbrev Fibration (P : E ⥤ C) := Display.Fibration (P⁻¹ .)

/-- A transport function for a functor `P : E ⥤ C` is a transport function for the
associated displayed structure of `P`. -/
abbrev Functor.Transport (P : E ⥤ C) := Display.Transport (P⁻¹ .)

section
variable {C E : Type*} [Category C] [Category E] (P : E ⥤ C) [ClovenFibration P]
{c d : C} (f : c ⟶ d) (y : P⁻¹ d) (g : CartLift f y)
#check Fibration.lift
#check ClovenFibration.lift
#check g.1
#check g.1.homOver
#check g.homOver.hom
end

open Display

lemma transport_over' {c d : C} {P : E ⥤ C} [Functor.Transport P] (f : c ⟶ d) (y : P⁻¹ d) :
    P.obj (f ⋆ y) = c := by
  simp only [Fibre.over]

namespace Display.ClovenFibration


variable (F : C → Type*) [Display F] [Display.ClovenFibration F]

@[simps!]
instance transport : Transport F where
  transport f X := (ClovenFibration.lift f X).src

example (f : c ⟶ d) (g : d ⟶ e) (y : P⁻¹ e) : f ⋆ g ⋆ y = f ⋆ (g ⋆ y) := rfl

@[simp]
def Transport (f : c ⟶ d) : (P⁻¹ d) → (P⁻¹ c) := fun y ↦ f ⋆ y

/-- The lift of a morphism `f` ending at `y`. -/
def basedLift (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y) ⟶[f] y := (ClovenFibration.lift f y).homOver

/-- The lift `(f ⋆ y) ⟶[f] y` is cartesian. -/
instance instCartesianBasedLift {f : c ⟶ d} {y : P⁻¹ d} : Cartesian (basedLift f y) :=
(ClovenFibration.lift f y).is_cart

@[simp]
def basedLiftHom (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y : E) ⟶ (y : E) := (ClovenFibration.lift f y).homOver.hom

@[simp]
lemma basedLiftHom_over (f : c ⟶ d) (y : P⁻¹ d) :
P.map (basedLiftHom f y) =
(eqToHom (transport_over (P:= P) f y)) ≫ f ≫ eqToHom ((Fiber.over y).symm) := by
  simp only [Fiber.mk_coe, basedLiftHom, BasedLift.over_base]

instance CartLiftOf (f : c ⟶ d) (y : P⁻¹ d) : CartLift f y := lift f y

@[simp]
def fiberHomOfBasedLiftHom {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) : x ⟶ f ⋆ y where
  val := gaplift (basedLift f y) (𝟙 c) (g.cast (id_comp f).symm)
  property := by simp_all only [basedLift, over_base, id_comp, eqToHom_trans]

def basedLiftOfFiberHom' {c : C} {x y : P⁻¹ c} (f : x ⟶ y) : x ⟶[𝟙 c] y :=
⟨f.1, by simp [f.2]⟩

@[simps!]
def equivFiberCatHomBasedLift {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} :
(x ⟶[f] y) ≃ (x ⟶ f ⋆ y) where
  toFun g := fiberHomOfBasedLiftHom g
  invFun g := (basedLiftOfFiberHom g ≫[l] basedLift f y).cast (id_comp f)
  left_inv := by
    intro g; ext; dsimp; simp [basedLiftOfFiberHom, gaplift_hom_property]
  right_inv := by
    intro g; simp only [basedLiftOfFiberHom]; cases g; sorry -- use the uniqueness of the gap lift


#check CategoryTheory.Epi.left_cancellation

-- def equivTransportId {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x) ≅ x where
--   hom := gaplift' (BasedLift.id x) (𝟙 c) (basedLiftOf (𝟙 c) x) (by simp only [comp_id])
--   inv := equivFiberCatHomBasedLift (id x)
--   hom_inv_id := by ext;
--   inv_hom_id := _

/-- Transporting along the identity morphism creates an isomorphic copy
of the transported object. -/
def equivTransportId {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x) ≅ x := by
haveI : Cartesian (basedLiftOfFiberHom (basedLift (𝟙 c) x : (𝟙 c) ⋆ x ⟶ x)) := by sorry --simp only [equivFiberHomBasedLift.right_inv]; infer_instance
apply vertCartIso (g:= (basedLift (𝟙 c) x : (𝟙 c) ⋆ x ⟶ x))

lemma is_iso_gaplift_id_transport {c : C} (x : P⁻¹ c) : IsIso (gaplift' (BasedLift.id x) (𝟙 c) (basedLift (𝟙 c) x) (comp_id (𝟙 c)).symm ).hom := by
  have H : (gaplift' (BasedLift.id x) (𝟙 c) (basedLift (𝟙 c) x) (comp_id (𝟙 c)).symm ).hom = (basedLift (𝟙 c) x).hom := by
    simp [gaplift']; rfl
  haveI : Cartesian (basedLiftOfFiberHom (basedLift (𝟙 c) x : (𝟙 c) ⋆ x ⟶ x)) := by
    simp
    --infer_instance
    sorry
  haveI: IsIso (vertCartIso (g:= (basedLift (𝟙 c) x : (𝟙 c) ⋆ x ⟶ x))).hom := by infer_instance
  simp only [vertCartIso] at this
  rw [H]
  sorry


--set_option trace.Meta.synthInstance true in
-- @[simp]
-- lemma transport_id {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x) ≅ x where
--   hom := gaplift' (BasedLift.id x) (𝟙 c) (basedLiftOf (𝟙 c) x) (by simp only [comp_id])
--   inv := gaplift' (basedLiftOf (𝟙 c) x) (𝟙 c) (BasedLift.id x) (by simp only [id_comp])
--   hom_inv_id := by
--     simp [FiberCat.comp_coe]; simp only [← BasedLift.id_hom]
--     apply hom_comp_cast (h₁ := (id_comp (𝟙 c)).symm).mpr ; rw [gaplift_comp];
--     --change
--     --rw [← cast_hom (h:= (id_comp (𝟙 x)).symm)];  --apply comp_hom_aux.mp;
--   inv_hom_id := sorry

-- @[simp]
-- lemma transport_comp {c d₁ d₂ : C} {f₁ : c ⟶ d₁} {f₂ : d₁ ⟶ d₂} {y : P⁻¹ d₂} : ((f₁ ≫ f₂) ⋆ y) ≅ f₁ ⋆ (f₂ ⋆ y) := by
--   apply vertCartIso (g:= (basedLift (f₁ ≫ f₂) y : (f₁ ≫ f₂) ⋆ y ⟶ y))

-- @[simp]
-- lemma transport_comp {c d₁ d₂ : C} {f₁ : c ⟶ d₁} {f₂ : d₁ ⟶ d₂} {y : P⁻¹ d₂} : ((f₁ ≫ f₂) ⋆ y) ≅ f₁ ⋆ (f₂ ⋆ y) where
--   hom := gaplift (basedLift f₁ (f₂ ⋆ y)) (𝟙 c) (castIdComp.invFun  (gaplift (basedLift f₂ y) f₁ (basedLift (f₁ ≫ f₂) y)))
--   inv := gaplift (basedLift (f₁ ≫ f₂) y) (𝟙 c) (castIdComp.invFun ((basedLift f₁ (f₂ ⋆ y)) ≫[l] (basedLift f₂ y)))
--   hom_inv_id := by simp; rw [← comp_hom _ _, ← id_hom]; congr; simp; sorry --aesop--apply gaplift_uniq' (BasedLiftOf f₁ (f₂ ⋆ y)) _
--   inv_hom_id := sorry

variable {F : Type*} [Category F]

/-- The composition of two cloven fibrations is a cloven fibration. -/
instance instComp (P : E ⥤ C) [ClovenFibration P] (Q : F ⥤ E) [ClovenFibration Q] : ClovenFibration (Q ⋙ P) where
  lift := @fun c d f z => by
    have : P.obj (Q.obj z) = d := by simp only [← Functor.comp_obj, z.over]
    let y : P ⁻¹ d := ⟨Q.obj z, this⟩
    let g := ClovenFibration.lift f y
    haveI : Cartesian g.homOver := by exact g.is_cart
    let z' : Q⁻¹ (y.1) := Fiber.tauto (P:= Q.obj) z.1
    let k := ClovenFibration.lift g.homOver.hom z'
    exact {
      src := sorry
      homOver := sorry
      is_cart := sorry
    }

end ClovenFibration

open ClovenFibration

class SplitFibration (P : E ⥤ C) extends ClovenFibration P where
transport_id_obj {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x).1 = x.1
transport_id_hom {c : C} (x : P⁻¹ c) : basedLiftHom (𝟙 c) x = eqToHom (transport_id_obj x) ≫ 𝟙 (x.1)
transport_comp_obj {c d₁ d₂ : C} (f₁ : c ⟶ d₁) (f₂ : d₁ ⟶ d₂) (x : P⁻¹ d₂) : ((f₁ ≫ f₂) ⋆ x).1 = (f₁ ⋆ (f₂ ⋆ x)).1
lift_comp_hom {c d e : C} (f₁ : c ⟶ d) (f₂ : d ⟶ d') (x : P⁻¹ d') :
basedLiftHom (f₁ ≫ f₂) x = eqToHom (transport_comp_obj f₁ f₂ x) ≫ basedLiftHom f₁ (f₂ ⋆ x) ≫ (basedLiftHom f₂ x)
-/
