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


-- set_option pp.explicit false
-- set_option trace.simps.verbose true
--set_option trace.Meta.synthInstance.instances true
--set_option trace.Meta.synthInstance true
set_option pp.proofs.threshold 20

namespace CategoryTheory

open Category Opposite BasedLift Fibre Display

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

/-- A functor `P : E ⥤ C` is a cloven fibration if the associated displayed structure of `P` is a
cloven fibration. -/
abbrev Functor.ClovenFibration (P : E ⥤ C) := Display.ClovenFibration (P⁻¹ .)

/-- A functor `P : E ⥤ C` is a fibration if the associated displayed structure of `P` is a
fibration. -/
abbrev Functor.Fibration (P : E ⥤ C) := Display.Fibration (P⁻¹ .)

/-- A transport function for a functor `P : E ⥤ C` is a transport function for the
associated displayed structure of `P`. -/
abbrev Functor.Transport (P : E ⥤ C) := Display.Transport (P⁻¹ .)

open Display

lemma transport_over' {I J : C} {P : E ⥤ C} [Functor.Transport P] (f : I ⟶ J) (Y : P⁻¹ J) :
    P.obj (f ⋆ Y) = I := by
  simp only [Fibre.over]

namespace Display.ClovenFibration

variable {I J : C} {P : E ⥤ C} [P.ClovenFibration]

@[simps!]
instance transport (F : C → Type*) [Display F] [Display.ClovenFibration F] : Transport F where
  transport f X := (ClovenFibration.lift f X).src

instance {P : E ⥤ C} [P.ClovenFibration] : P.Transport where
  transport f X := (ClovenFibration.lift f X).src

@[simp]
def Transport (f : I ⟶ J) : (P⁻¹ J) → (P⁻¹ I) := fun Y ↦ f ⋆ Y

/-- The lift of a morphism `f` ending at `Y`. -/
def basedLift (f : I ⟶ J) (Y : P⁻¹ J) : (f ⋆ Y) ⟶[f] Y := (ClovenFibration.lift f Y).homOver

/-- The lift `(f ⋆ Y) ⟶[f] Y` is cartesian. -/
instance instCartesianBasedLift {f : I ⟶ J} {Y : P⁻¹ J} : Cartesian (basedLift f Y) :=
  (ClovenFibration.lift f Y).is_cart

@[simp]
def basedLiftHom (f : I ⟶ J) (Y : P⁻¹ J) : (f ⋆ Y : E) ⟶ (Y : E) := (ClovenFibration.lift f Y).homOver.hom

/-- JT: TODO there is a shadowing problem with `eqToHom` here, since we want to use the `CategoryTheory`
one, but it's shadowed by the `Fibre` one -/
@[simp]
lemma basedLiftHom_over (f : I ⟶ J) (Y : P⁻¹ J) :
    P.map (basedLiftHom f Y) =
    (CategoryTheory.eqToHom (transport_over' f Y)) ≫ f ≫ CategoryTheory.eqToHom ((Fibre.over Y).symm) := by
  simp only [Fibre.mk_coe, basedLiftHom, BasedLift.over_base]

instance CartLiftOf (f : I ⟶ J) (Y : P⁻¹ J) : CartLift f Y := lift f Y

def gapTransfer {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} (g : X ⟶[f] Y) : X ⟶[𝟙 I] f ⋆ Y :=
  (Cartesian.gap (basedLift f Y) (𝟙 I) (g.cast (id_comp f).symm))

def fibreHomOfHomOver {I : C} {X Y : P⁻¹ I} (f : X ⟶[𝟙 I] Y) : X ⟶ Y :=
  ⟨f.hom, by simp⟩

notation:85 (name := Fibre_lift_stx) f "ᶠ" => fibreHomOfHomOver f

lemma fiber_lift_comp {I : C} {X Y Z : P⁻¹ I} (f : X ⟶[𝟙 I] Y) (g : Y ⟶[𝟙 I] Z) :
    fᶠ ≫ gᶠ = (cast (comp_id (𝟙 I)) (f ≫ₗ g))ᶠ := by
  simp [fibreHomOfHomOver]
  sorry

def homOverOfFiberHom {I : C} {X Y : P⁻¹ I} (f : X ⟶ Y) : X ⟶[𝟙 I] Y :=
  ⟨f.1, by simp [f.2]⟩

notation:75 (name := Base_lift_stx) f "ᵒ" => homOverOfFiberHom f

@[simp]
lemma fiberHom_basedLift {I : C} {X Y : P⁻¹ I} (f : X ⟶ Y) : (f ᵒ)ᶠ = f := by
  rfl

@[simp]
lemma basedLift_fiberHom {I : C} {X Y : P⁻¹ I} (f : X ⟶[𝟙 I] Y) : (f ᶠ)ᵒ = f := by
  rfl

lemma fiberLift_congr {I : C} {X Y Z : P⁻¹ I} (f g: X ⟶[𝟙 I] Y) :
    fᶠ = gᶠ ↔ f = g := by
  apply Iff.intro
  · intro eq
    ext
    simp [fibreHomOfHomOver] at eq
    sorry
  · intro eq
    aesop_cat


def equivBasedLiftAux {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
    (X ⟶[𝟙 I ≫ f] Y) ≃ (X ⟶[𝟙 I] f ⋆ Y) where
  toFun g := Cartesian.gap (basedLift f Y) (𝟙 I) g
  invFun h := h ≫ₗ basedLift f Y
  left_inv := by
    intro g
    simp only [transport_transport, Cartesian.gap_prop]
  right_inv := by
    intro h
    symm
    exact Cartesian.gaplift_uniq (basedLift f Y) (h ≫ₗ basedLift f Y) h (by rfl)

@[simps!]
def equivBasedLift {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
    (X ⟶[f] Y) ≃ (X ⟶[𝟙 I] f ⋆ Y) :=
  Equiv.trans (Display.castEquiv (id_comp f).symm) equivBasedLiftAux

def equivFiberCatHomBasedLiftAux {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
    (X ⟶[𝟙 I] f ⋆ Y) ≃ (X ⟶ f ⋆ Y) where
  toFun g := ⟨g.hom, by simp⟩
  invFun h := ⟨h.1, by simp⟩
  left_inv := by intro _; rfl
  right_inv := by intro _; rfl

@[simps!]
def equivFiberCatHomBasedLift {I J : C} {f : I ⟶ J} {X : P⁻¹ I} {Y : P⁻¹ J} :
    (X ⟶[f] Y) ≃ (X ⟶ f ⋆ Y) :=
  Equiv.trans equivBasedLift equivFiberCatHomBasedLiftAux


-- open Cartesian in
-- lemma inv_comp {I: C} {X X' : P⁻¹ I} (g : X ⟶ X') [Cartesian (homOverOfFiberHom g)] :
--     (gap (g ᵒ) (𝟙 I) (cast (comp_id (𝟙 I)).symm (𝟙ₗ X')))ᶠ ≫ g = (𝟙ₗ X')ᶠ := by
--   simp

-- open Cartesian in
-- /-- Vertical cartesian morphisms are isomorphism. -/
-- @[simps!]
-- def vertCartIso {I: C} {X X' : P⁻¹ I} (g : X ⟶ X')
--   [Cartesian (homOverOfFiberHom g)] : X ≅ X' where
--   hom := g
--   inv := (gap (g ᵒ) (𝟙 I) (cast (comp_id (𝟙 I)).symm (𝟙ₗ X')))ᶠ
--   hom_inv_id := by
--     conv =>
--       lhs
--       rhs
--     sorry

--   inv_hom_id := by
--     dsimp
--     conv =>
--       lhs

-- /-- Transporting along the identity morphism creates an isomorphic copy
-- of the transported object. -/
-- def equivTransportId {I : C} (X : P⁻¹ I) : ((𝟙 I) ⋆ X) ≅ X := by
--   haveI : Cartesian (homOverOfFiberHom (basedLift (𝟙 I) X : (𝟙 I) ⋆ X ⟶ X)) := by sorry --simp only [equivFiberHomBasedLift.right_inv]; infer_instance
--   apply vertCartIso (g:= (basedLift (𝟙 c) x : (𝟙 c) ⋆ x ⟶ x))

-- lemma is_iso_gaplift_id_transport {c : C} (x : P⁻¹ c) : IsIso (gaplift' (BasedLift.id x) (𝟙 c) (basedLift (𝟙 c) x) (comp_id (𝟙 c)).symm ).hom := by
--   have H : (gaplift' (BasedLift.id x) (𝟙 c) (basedLift (𝟙 c) x) (comp_id (𝟙 c)).symm ).hom = (basedLift (𝟙 c) x).hom := by
--     simp [gaplift']; rfl
--   haveI : Cartesian (homOverOfFiberHom (basedLift (𝟙 c) x : (𝟙 c) ⋆ x ⟶ x)) := by
--     simp
--     --infer_instance
--     sorry
--   haveI: IsIso (vertCartIso (g:= (basedLift (𝟙 c) x : (𝟙 c) ⋆ x ⟶ x))).hom := by infer_instance
--   simp only [vertCartIso] at this
--   rw [H]
--   sorry


-- --set_option trace.Meta.synthInstance true in
-- -- @[simp]
-- -- lemma transport_id {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x) ≅ x where
-- --   hom := gaplift' (BasedLift.id x) (𝟙 c) (basedLiftOf (𝟙 c) x) (by simp only [comp_id])
-- --   inv := gaplift' (basedLiftOf (𝟙 c) x) (𝟙 c) (BasedLift.id x) (by simp only [id_comp])
-- --   hom_inv_id := by
-- --     simp [FiberCat.comp_coe]; simp only [← BasedLift.id_hom]
-- --     apply hom_comp_cast (h₁ := (id_comp (𝟙 c)).symm).mpr ; rw [gaplift_comp];
-- --     --change
-- --     --rw [← cast_hom (h:= (id_comp (𝟙 x)).symm)];  --apply comp_hom_aux.mp;
-- --   inv_hom_id := sorry

-- -- @[simp]
-- -- lemma transport_comp {c d₁ d₂ : C} {f₁ : c ⟶ d₁} {f₂ : d₁ ⟶ d₂} {y : P⁻¹ d₂} : ((f₁ ≫ f₂) ⋆ y) ≅ f₁ ⋆ (f₂ ⋆ y) := by
-- --   apply vertCartIso (g:= (basedLift (f₁ ≫ f₂) y : (f₁ ≫ f₂) ⋆ y ⟶ y))

-- -- @[simp]
-- -- lemma transport_comp {c d₁ d₂ : C} {f₁ : c ⟶ d₁} {f₂ : d₁ ⟶ d₂} {y : P⁻¹ d₂} : ((f₁ ≫ f₂) ⋆ y) ≅ f₁ ⋆ (f₂ ⋆ y) where
-- --   hom := gaplift (basedLift f₁ (f₂ ⋆ y)) (𝟙 c) (castIdComp.invFun  (gaplift (basedLift f₂ y) f₁ (basedLift (f₁ ≫ f₂) y)))
-- --   inv := gaplift (basedLift (f₁ ≫ f₂) y) (𝟙 c) (castIdComp.invFun ((basedLift f₁ (f₂ ⋆ y)) ≫[l] (basedLift f₂ y)))
-- --   hom_inv_id := by simp; rw [← comp_hom _ _, ← id_hom]; congr; simp; sorry --aesop--apply gaplift_uniq' (BasedLiftOf f₁ (f₂ ⋆ y)) _
-- --   inv_hom_id := sorry

-- variable {F : Type*} [Category F]

-- /-- The composition of two cloven fibrations is a cloven fibration. -/
-- instance instComp (P : E ⥤ C) [ClovenFibration P] (Q : F ⥤ E) [ClovenFibration Q] : ClovenFibration (Q ⋙ P) where
--   lift := @fun c d f z => by
--     have : P.obj (Q.obj z) = d := by simp only [← Functor.comp_obj, z.over]
--     let y : P ⁻¹ d := ⟨Q.obj z, this⟩
--     let g := ClovenFibration.lift f y
--     haveI : Cartesian g.homOver := by exact g.is_cart
--     let z' : Q⁻¹ (y.1) := Fiber.tauto (P:= Q.obj) z.1
--     let k := ClovenFibration.lift g.homOver.hom z'
--     exact {
--       src := sorry
--       homOver := sorry
--       is_cart := sorry
--     }

-- end ClovenFibration

-- open ClovenFibration

-- class SplitFibration (P : E ⥤ C) extends ClovenFibration P where
-- transport_id_obj {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x).1 = x.1
-- transport_id_hom {c : C} (x : P⁻¹ c) : basedLiftHom (𝟙 c) x = eqToHom (transport_id_obj x) ≫ 𝟙 (x.1)
-- transport_comp_obj {c d₁ d₂ : C} (f₁ : c ⟶ d₁) (f₂ : d₁ ⟶ d₂) (x : P⁻¹ d₂) : ((f₁ ≫ f₂) ⋆ x).1 = (f₁ ⋆ (f₂ ⋆ x)).1
-- lift_comp_hom {c d e : C} (f₁ : c ⟶ d) (f₂ : d ⟶ d') (x : P⁻¹ d') :
-- basedLiftHom (f₁ ≫ f₂) x = eqToHom (transport_comp_obj f₁ f₂ x) ≫ basedLiftHom f₁ (f₂ ⋆ x) ≫ (basedLiftHom f₂ x)
