import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Logic.Function.ULift
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.Data.Part
import Mathlib.CategoryTheory.ChosenFiniteProducts

/-! This file contains declarations missing from mathlib,
to be upstreamed. -/

namespace CategoryTheory

attribute [reassoc (attr := simp)] Limits.terminal.comp_from

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

namespace CategoryTheory.ULift

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/- Composing with downFunctor is injective.
   This requires an explicit universe variable in its fifth universe argument `u`. -/
theorem comp_downFunctor_inj (F G : C ⥤ ULift.{u} D) : F ⋙ downFunctor = G ⋙ downFunctor ↔ F = G := by
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
    (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem eqToHom_hom {C1 C2 : Cat.{v,u}} {x y: C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).map f = (cast (Cat.eqToHom_hom_aux x y eq) f) := by
  cases eq
  simp[CategoryStruct.id]

/-- This turns the object part of eqToHom functors into casts -/
theorem eqToHom_obj {C1 C2 : Cat.{v,u}} (x : C1) (eq : C1 = C2) :
    (eqToHom eq).obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp[CategoryStruct.id]

abbrev homOf {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := F

@[simps] def ULift_lte_iso_self {C : Type (max u u₁)} [Category.{v} C] :
    Cat.of (ULift.{u} C) ≅ Cat.of C where
  hom := ULift.downFunctor
  inv := ULift.upFunctor

@[simp] def ULift_succ_iso_self {C : Type (u + 1)} [Category.{v} C] :
    of (ULift.{u, u + 1} C) ≅ of C := ULift_lte_iso_self.{v,u,u+1}

@[simp] def ULift_iso_self {C : Type u} [Category.{v} C] :
    of (ULift.{u, u} C) ≅ of C := ULift_lte_iso_self

def ofULift (C : Type u) [Category.{v} C] : Cat.{v, max u w} :=
  of $ ULift.{w} C

def uLiftFunctor : Cat.{v,u} ⥤ Cat.{v, max u w} where
  obj X := Cat.ofULift.{w} X
  map F := Cat.homOf $ ULift.downFunctor ⋙ F ⋙ ULift.upFunctor

end CategoryTheory.Cat

namespace CategoryTheory.Grpd

abbrev homOf {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D] (F : C ⥤ D) :
    Grpd.of C ⟶ Grpd.of D := F

end CategoryTheory.Grpd

/-
  CategoryTheory.Grothedieck

-/

namespace CategoryTheory

namespace Grothendieck

variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Cat.{v₁,u₁}} {x y : Grothendieck A}

theorem obj_ext_hEq
    (hbase : x.base = y.base) (hfiber : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨xbase, xfiber⟩
  subst hbase
  subst hfiber
  rfl

/-- This proves that base of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem eqToHom_base (eq : x = y) :
    (eqToHom eq).base = (eqToHom (congrArg (Grothendieck.forget A).obj eq)) := by
  cases eq
  simp

/-- This is the proof of equality used in the eqToHom in `Grothendieck.eqToHom_fiber` -/
theorem eqToHom_fiber_aux {Γ : Cat.{v,u}} {A : Γ ⥤ Cat.{v₁,u₁}} {g1 g2 : Grothendieck A}
    (eq : g1 = g2) : (A.map (eqToHom eq).base).obj g1.fiber = g2.fiber := by
  cases eq
  simp

/-- This proves that fiber of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem eqToHom_fiber {Γ : Cat.{v,u}} {A : Γ ⥤ Cat.{v₁,u₁}} {g1 g2 : Grothendieck A}
    (eq : g1 = g2) : (eqToHom eq).fiber = eqToHom (Grothendieck.eqToHom_fiber_aux eq) := by
  cases eq
  simp

theorem obj_ext_cast
    (hbase : x.base = y.base)
    (hfiber : cast (congrArg (λ x ↦ (A.obj x).α) hbase) x.fiber = y.fiber)
    : x = y := obj_ext_hEq hbase (heq_of_cast_eq (by simp[hbase]) (by simp[hfiber]))

theorem map_eqToHom_base_pf {G1 G2 : Grothendieck A} (eq : G1 = G2) :
    A.obj G1.base = A.obj G2.base := by subst eq; rfl

theorem map_eqToHom_base {G1 G2 : Grothendieck A} (eq : G1 = G2)
    : A.map (eqToHom eq).base = eqToHom (map_eqToHom_base_pf eq) := by
  simp [eqToHom_base, eqToHom_map]
  
open Iso

variable {C : Type u₁} [Category.{v₁,u₁} C] {G : C ⥤ Cat.{v₂,u₂}}

/-- A morphism in the Grothendieck construction is an isomorphism if
- the morphism in the base is an isomorphism; and
- the fiber morphism is an isomorphism. -/
def mkIso {X Y : Grothendieck G}
    (s : X.base ≅ Y.base) (t : (G |>.map s.hom).obj X.fiber ≅ Y.fiber) :
    X ≅ Y where
  hom := { base := s.hom, fiber := t.hom }
  inv.base := s.inv
  inv.fiber := (G.map (s.inv)).map (t.inv) ≫
    eqToHom (by simpa only [Functor.map_comp, Functor.map_id] using
      congr((G.map $(s.hom_inv_id)).obj X.fiber))
  hom_inv_id := by
    apply ext
    erw [comp_fiber]
    simp only [Cat.comp_obj, id_eq, map_hom_inv_id_assoc,
      eqToHom_trans, id_fiber] at *
    erw [comp_base, id_base]
    dsimp
    rw [s.hom_inv_id]
  inv_hom_id := by
    suffices ∀ {Z g} (_ : g ≫ s.hom = Z) (_ : Z = 𝟙 _)
        {g'} (eq : g' ≫ (G.map g).map t.hom = 𝟙 _)
        (W) (eqW : G.map g ≫ G.map s.hom = W)
        (eq2 : ∃ w1 w2, W.map t.hom = eqToHom w1 ≫ t.hom ≫ eqToHom w2) h1 h2,
        { base := Z, fiber := eqToHom h1 ≫ (G.map s.hom).map (g' ≫ eqToHom h2) ≫ t.hom } =
        ({..} : Grothendieck.Hom ..) from
      this rfl s.inv_hom_id (by simp)
        (W := 𝟙 _) (eqW := by simp) (eq2 := ⟨rfl, rfl, by simp⟩) ..
    rintro _ g - rfl g' eq _ rfl ⟨w1, w2, eq2 : (G.map s.hom).map _ = _⟩ h1 h2; congr
    replace eq := congr((G.map s.hom).map $eq)
    simp only [Functor.map_comp, eq2, eqToHom_map, Category.assoc] at eq ⊢
    conv at eq => lhs; slice 1 3
    rw [(comp_eqToHom_iff ..).1 eq]; simp

end Grothendieck

namespace IsPullback

variable {C : Type u₁} [Category.{v₁} C]

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

def of_iso_isPullback (h : IsPullback fst snd f g) {Q} (i : Q ≅ P) :
      IsPullback (i.hom ≫ fst) (i.hom ≫ snd) f g := by
  have : Limits.HasPullback f g := ⟨ h.cone , h.isLimit ⟩
  refine IsPullback.of_iso_pullback (by simp [h.w]) (i ≪≫ h.isoPullback) (by simp) (by simp)

end IsPullback
end CategoryTheory

namespace CategoryTheory

namespace Grpd

open Limits

/-- The chosen terminal object in `Grpd`. -/
abbrev chosenTerminal : Grpd.{u,u} := Grpd.of (Discrete.{u} PUnit)

/-- The chosen terminal object in `Grpd` is terminal. -/
def chosenTerminalIsTerminal : IsTerminal chosenTerminal :=
  IsTerminal.ofUniqueHom (fun _ ↦ (Functor.const _).obj ⟨⟨⟩⟩) fun _ _ ↦ rfl

/-- The chosen product of categories `C × D` yields a product cone in `Grpd`. -/
def prodCone (C D : Grpd.{u,u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

/-- The product cone in `Grpd` is indeed a product. -/
def isLimitProdCone (X Y : Grpd) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => S.fst.prod' S.snd) (fun _ => rfl) (fun _ => rfl) (fun A B h1 h2 =>
    Functor.hext
      (fun x ↦ Prod.ext (by dsimp; rw [← h1]; rfl)
      (by dsimp; rw [← h2]; rfl))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))

instance : ChosenFiniteProducts Grpd where
  product (X Y : Grpd) := { isLimit := isLimitProdCone X Y }
  terminal  := { isLimit := chosenTerminalIsTerminal }

/-- The identity in the category of groupoids equals the identity functor.-/
theorem id_eq_id (X : Grpd) : 𝟙 X = 𝟭 X := rfl

/-- Composition in the category of groupoids equals functor composition.-/
theorem comp_eq_comp {X Y Z : Grpd} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

end Grpd

namespace AsSmall

def up_map_comp_down_map
    {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) :
  AsSmall.down.map (AsSmall.up.map f) = f := rfl

end AsSmall

end CategoryTheory
