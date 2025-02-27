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
import Mathlib.CategoryTheory.Core

/-! This file contains declarations missing from mathlib,
to be upstreamed. -/


/-

This comment space is for notes about mathlib definitions/theorems that should be fixed, refactored,
or redesigned.

- AsSmall.down and AsSmall.up should have their universe level order changed so that the third value comes first.
- currently I often write AsSmall.{_,_,w} because the first two can be inferred but not the max universe.

-/

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
  simp [← Functor.assoc, h]

theorem comp_down_inj {C : Type u} [Category.{v} C]
  {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ AsSmall.{w} D}
    (h : F ⋙ AsSmall.down = G ⋙ AsSmall.down)
    : F = G := by
  convert_to F ⋙ AsSmall.down
    ⋙ AsSmall.up
    = G ⋙ AsSmall.down ⋙ AsSmall.up
  simp [← Functor.assoc, h]

def up_comp_down
    {C : Type u₁} [Category.{v₁, u₁} C] :
  AsSmall.up ⋙ AsSmall.down = Functor.id C := rfl

def down_comp_up
    {C : Type u₁} [Category.{v₁, u₁} C] :
  AsSmall.down ⋙ AsSmall.up = Functor.id (AsSmall C) := rfl

instance {C : Type u} [Category.{v} C] :
    Functor.IsEquivalence (AsSmall.up : C ⥤ AsSmall C) :=
  AsSmall.equiv.isEquivalence_functor

end AsSmall

namespace Groupoid

instance asSmallGroupoid (Γ : Type w) [Groupoid.{v} Γ] :
    Groupoid (AsSmall.{max w u v} Γ) where
  inv f := AsSmall.up.map (inv (AsSmall.down.map f))

end Groupoid

namespace Grpd

abbrev homOf {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D] (F : C ⥤ D) :
    Grpd.of C ⟶ Grpd.of D := F

def asSmallFunctor : Grpd.{v, u} ⥤ Grpd.{max w v u, max w v u} where
  obj Γ := Grpd.of $ AsSmall.{max w v u} Γ
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

end Grpd

namespace Core

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

@[simp]
theorem id_inv (X : C) :
    Iso.inv (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl
  @[simp]
theorem comp_inv {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).inv = g.inv ≫ f.inv :=
  rfl

def functor' (F : C ⥤ D) : Core C ⥤ Core D where
  obj := F.obj
  map f := {
    hom := F.map f.hom
    inv := F.map f.inv}
  map_id x := by
    simp only [Grpd.coe_of, id_hom, Functor.map_id, id_inv]
    congr 1
  map_comp f g := by
    simp only [Grpd.coe_of, comp_hom, Functor.map_comp, comp_inv]
    congr 1

lemma functor'_comp_inclusion (F : C ⥤ D) :
    functor' F ⋙ inclusion D = inclusion C ⋙ F :=
  rfl

def functor : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := Grpd.homOf (functor' F)

variable {Γ : Type u} [Groupoid.{v} Γ]

/-  A functor from a groupoid into a category is equivalent
    to a functor from the groupoid into the core -/
def functorToCoreEquiv : Γ ⥤ D ≃ Γ ⥤ Core D where
  toFun := functorToCore
  invFun := forgetFunctorToCore.obj
  left_inv _ := rfl
  right_inv _ := by
    simp [functorToCore, forgetFunctorToCore]
    apply Functor.ext
    · intro x y f
      simp only [inclusion, id_eq, Functor.comp_obj, Functor.comp_map,
        IsIso.Iso.inv_hom, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      congr
    · intro
      rfl

section Adjunction

variable {C : Type u₁} [Category.{v₁} C]
variable {G : Type u₂} [Groupoid.{v₂} G]
variable {G' : Type u₃} [Groupoid.{v₃} G']
variable {C' : Type u₃} [Category.{v₃} C']

theorem functorToCore_naturality_left
    (H : G ⥤ C) (F : G' ⥤ G) :
    functorToCore (F ⋙ H) = F ⋙ functorToCore H := by
  apply Functor.ext
  · simp [functorToCore]
  · intro
    rfl

theorem functorToCore_naturality_right
    (H : G ⥤ C) (F : C ⥤ C') :
    functorToCore (H ⋙ F)
    = functorToCore H ⋙ (Core.functor' F) := by
  apply Functor.ext
  · intro x y f
    simp [functorToCore]
    congr 1
    simp
  · intro
    rfl

def adjunction : Grpd.forgetToCat ⊣ Core.functor where
  unit := {
    app G := Grpd.homOf (Core.functorToCore (Functor.id _))
    naturality _ _ F := by
      simp [Core.functor, Grpd.comp_eq_comp,
        ← functorToCore_naturality_left,
        ← functorToCore_naturality_right,
        Functor.id_comp, Functor.comp_id, Grpd.forgetToCat]}
  counit := {app C := Cat.homOf (Core.inclusion C)}

/-- Mildly evil. -/
theorem inclusion_comp_functorToCore : inclusion G ⋙ functorToCore (𝟭 G) = Functor.id (Core G) := by
    apply Functor.ext
    · intro x y f
      simp only [Core.inclusion, Grpd.homOf, Core.functorToCore, Functor.id_map,
        Grpd.comp_eq_comp, Functor.comp_map, Groupoid.inv_eq_inv, IsIso.Iso.inv_hom,
        Grpd.id_eq_id, eqToHom_refl, Category.comp_id, Category.id_comp]
      rfl
    · intro
      rfl

/-- Mildly evil. -/
instance : IsIso (Grpd.homOf (Core.inclusion G)) where
  out := ⟨ Grpd.homOf (Core.functorToCore (Functor.id G)),
    inclusion_comp_functorToCore, rfl ⟩

/-- Mildly evil. -/
instance {G : Type u} [Groupoid.{v} G] :
  IsIso (Grpd.homOf (Core.functorToCore (Functor.id G))) where
  out := ⟨ Grpd.homOf (Core.inclusion G), rfl,
    inclusion_comp_functorToCore ⟩

end Adjunction

open Functor

instance : IsLeftAdjoint Grpd.forgetToCat :=
  IsLeftAdjoint.mk ⟨ Core.functor , ⟨ adjunction ⟩ ⟩

instance : IsRightAdjoint Core.functor :=
  IsRightAdjoint.mk ⟨ Grpd.forgetToCat , ⟨ adjunction ⟩ ⟩

/- This whole section is evil. -/
namespace IsPullback

noncomputable section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D)

lemma w' : Cat.homOf (inclusion C) ≫ Cat.homOf F
    = Cat.homOf (Core.functor' F) ⋙ Cat.homOf (inclusion D) := rfl

variable {F} [F.ReflectsIsomorphisms]

open Limits

def lift (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    s.pt ⥤ Core C := {
  obj := s.fst.obj
  map {x y} f := @asIso _ _ _ _ (s.fst.map f) $ by
    let f' : F.obj (s.fst.obj x) ≅ F.obj (s.fst.obj y) :=
      (eqToIso s.condition).app x ≪≫ s.snd.map f ≪≫ (eqToIso s.condition.symm).app y
    have hnat : F.map (s.fst.map f) ≫ _
      = _ ≫ (inclusion D).map (s.snd.map f)
      := (eqToHom s.condition).naturality f
    have h : F.map (s.fst.map f) = f'.hom := by
      simp only [Cat.eqToHom_app, comp_eqToHom_iff] at hnat
      simp only [hnat, f', Core.inclusion]
      simp
    have : IsIso (F.map (s.fst.map f)) := by rw [h]; exact Iso.isIso_hom f'
    exact Functor.ReflectsIsomorphisms.reflects F (s.fst.map f)
  map_id x := by
    simp only [asIso, Functor.map_id, IsIso.inv_id]
    congr 1
  map_comp f g := by
    simp only [asIso, Functor.map_comp, IsIso.inv_comp]
    congr 1
    simp
}

def fac_left (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    lift s ≫ Cat.homOf (inclusion C) = s.fst := rfl

theorem Core.eqToIso_hom {a b : Core C} (h1 : a = b)
  (h2 : (inclusion C).obj a = (inclusion C).obj b) :
    (eqToHom h1).hom = eqToHom h2 := by
  cases h1
  rfl

def fac_right (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    lift s ≫ Cat.homOf (functor' F) = s.snd := by
  apply Functor.ext
  · intro x y f
    apply Functor.map_injective (inclusion D)
    have h := Functor.congr_hom s.condition f
    unfold Cat.homOf at *
    unfold inclusion at *
    simp only [Cat.of_α, Cat.comp_obj, lift, functor', comp_hom] at *
    convert h
    · apply Core.eqToIso_hom
    · apply Core.eqToIso_hom
  · intro x
    exact Functor.congr_obj s.condition x

def uniq (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D)))
  (m : s.pt ⟶ Cat.of (Core C))
  (fl : m ≫ Cat.homOf (inclusion C) = s.fst) :
    m = lift s := by
  apply Functor.ext
  · intro x y f
    apply Functor.map_injective (inclusion C)
    have h := Functor.congr_hom fl f
    unfold Cat.homOf at *
    unfold inclusion at *
    simp only [Cat.of_α, Cat.comp_map, lift, comp_hom, asIso_hom] at *
    rw [h, Core.eqToIso_hom, Core.eqToIso_hom]
  · intro x
    exact Functor.congr_obj fl x

end
end IsPullback

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) [F.ReflectsIsomorphisms]

open IsPullback

/--
  In the category of categories,
  if functor `F : C ⥤ D` reflects isomorphisms
  then taking the `Core` is pullback stable along `F`

  Core C ---- inclusion -----> C
    |                          |
    |                          |
    |                          |
 Core.functor' F               F
    |                          |
    |                          |
    V                          V
  Core D ---- inclusion -----> D
-/
theorem isPullback_functor'_self :
    IsPullback
      (Cat.homOf $ inclusion C)
      (Cat.homOf $ functor' F)
      (Cat.homOf F)
      (Cat.homOf $ inclusion D) :=
  IsPullback.of_isLimit $
    Limits.PullbackCone.IsLimit.mk
      (w' F) lift fac_left fac_right
      (λ s m fl _ ↦ uniq s m fl)
end Core

end CategoryTheory
