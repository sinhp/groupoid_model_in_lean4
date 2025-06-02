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
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Grothendieck
import SEq.Tactic.DepRewrite

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

theorem cast_eq {F G : Γ ⥤ Cat.{v₁,u₁}}
    (h : F = G) (p : Grothendieck F) :
    (cast (by subst h; rfl) p : Grothendieck G)
    = ⟨ p.base , cast (by subst h; rfl) p.fiber ⟩ := by
  subst h
  rfl

theorem obj_ext_hEq
    (hbase : x.base = y.base) (hfiber : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨xbase, xfiber⟩
  subst hbase
  subst hfiber
  rfl

/-- This proves that base of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem eqToHom_base (eq : x = y) :
    (eqToHom eq).base = eqToHom (by simp [eq]) := by
  cases eq
  simp

/-- This is the proof of equality used in the eqToHom in `Grothendieck.eqToHom_fiber` -/
theorem eqToHom_fiber_aux {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Cat.{v₁,u₁}} {g1 g2 : Grothendieck A}
    (eq : g1 = g2) : (A.map (eqToHom eq).base).obj g1.fiber = g2.fiber := by
  cases eq
  simp

/-- This proves that fiber of an eqToHom morphism in the category Grothendieck A is an eqToHom morphism -/
theorem eqToHom_fiber {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Cat.{v₁,u₁}} {g1 g2 : Grothendieck A}
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

theorem of_iso_isPullback (h : IsPullback fst snd f g) {Q} (i : Q ≅ P) :
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
@[simp] theorem id_eq_id (X : Grpd) : 𝟙 X = 𝟭 X := rfl

-- NOTE this is currently called `Grpd.hom_to_functor` in mathlib,
-- but this naming is inconsistent with that of `Cat`
/-- Composition in the category of groupoids equals functor composition.-/
@[simp] theorem comp_eq_comp {X Y Z : Grpd} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

theorem eqToHom_obj
  {C1 C2 : Grpd.{v,u}} (x : C1) (eq : C1 = C2) :
    (eqToHom eq).obj x = cast (congrArg Bundled.α eq) x := by
  cases eq
  simp[CategoryStruct.id]

section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}

@[simp] theorem map_id_obj {x : Γ} {a : A.obj x} :
    (A.map (𝟙 x)).obj a = a := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_obj this a

@[simp] theorem map_id_map
    {x : Γ} {a b : A.obj x} {f : a ⟶ b} :
    (A.map (𝟙 x)).map f = eqToHom Grpd.map_id_obj
      ≫ f ≫ eqToHom Grpd.map_id_obj.symm := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_hom this f

@[simp] theorem map_comp_obj
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a : A.obj x} :
    (A.map (f ≫ g)).obj a = (A.map g).obj ((A.map f).obj a) := by
  have : A.map (f ≫ g) = A.map f ⋙ A.map g := by
    simp [Grpd.comp_eq_comp]
  have h := Functor.congr_obj this a
  simp only [Functor.comp_obj] at h
  exact h

@[simp] theorem map_comp_map
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a b : A.obj x} {φ : a ⟶ b} :
    (A.map (f ≫ g)).map φ
    = eqToHom Grpd.map_comp_obj ≫ (A.map g).map ((A.map f).map φ)
    ≫ eqToHom Grpd.map_comp_obj.symm := by
  have : A.map (f ≫ g) = A.map f ≫ A.map g := by simp
  exact Functor.congr_hom this φ

theorem map_comp_map'
    {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z} {a b : A.obj x} {φ : a ⟶ b} :
    (A.map g).map ((A.map f).map φ)
    = eqToHom Grpd.map_comp_obj.symm ≫ (A.map (f ≫ g)).map φ ≫ eqToHom Grpd.map_comp_obj
    := by
  simp [Grpd.map_comp_map]
end

@[simp] theorem id_obj {C : Grpd} (X : C) :
    (𝟙 C : C ⥤ C).obj X = X :=
  rfl

@[simp] theorem comp_obj {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E)
    (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

variable {Γ : Type u} [Category.{v} Γ] (F : Γ ⥤ Grpd.{v₁,u₁})

@[simp] theorem map_eqToHom_obj {x y : Γ} (h : x = y) (t) :
    (F.map (eqToHom h)).obj t = cast (by rw [h]) t := by
  subst h
  simp

/-- This is the proof of equality used in the eqToHom in `Cat.eqToHom_hom` -/
theorem eqToHom_hom_aux {C1 C2 : Grpd.{v,u}} (x y: C1) (eq : C1 = C2) :
    (x ⟶ y) = ((eqToHom eq).obj x ⟶ (eqToHom eq).obj y) := by
  cases eq
  simp[CategoryStruct.id]

/-- This is the turns the hom part of eqToHom functors into a cast-/
theorem eqToHom_hom {C1 C2 : Grpd.{v,u}} {x y: C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).map f = (cast (Grpd.eqToHom_hom_aux x y eq) f) := by
  cases eq
  simp only [eqToHom_refl, id_eq_id, Functor.id_map, cast_eq]

@[simp] theorem map_eqToHom_map {x y : Γ} (h : x = y) {t s} (f : t ⟶ s) :
    (F.map (eqToHom h)).map f =
    eqToHom (Functor.congr_obj (eqToHom_map _ _) t)
    ≫ cast (Grpd.eqToHom_hom_aux t s (by rw [h])) f
    ≫ eqToHom (Eq.symm (Functor.congr_obj (eqToHom_map _ _) s)) := by
  have h1 : F.map (eqToHom h) = eqToHom (by rw [h]) := eqToHom_map _ _
  rw [Functor.congr_hom h1, Grpd.eqToHom_hom]
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

@[simp] theorem comp_inv {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).inv = g.inv ≫ f.inv :=
  rfl

def map' (F : C ⥤ D) : Core C ⥤ Core D where
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

lemma map'_comp_inclusion (F : C ⥤ D) :
    map' F ⋙ inclusion D = inclusion C ⋙ F :=
  rfl

def map : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := Grpd.homOf (map' F)

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

theorem eqToIso_hom {a b : Core C} (h1 : a = b)
  (h2 : (inclusion C).obj a = (inclusion C).obj b) :
    (eqToHom h1).hom = eqToHom h2 := by
  cases h1
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
    = functorToCore H ⋙ (Core.map' F) := by
  apply Functor.ext
  · intro x y f
    simp [functorToCore]
    congr 1
    simp
  · intro
    rfl

def adjunction : Grpd.forgetToCat ⊣ Core.map where
  unit := {
    app G := Grpd.homOf (Core.functorToCore (Functor.id _))
    naturality _ _ F := by
      simp [Core.map, Grpd.comp_eq_comp,
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

theorem functorToCore_inclusion_apply {C : Type u} [Category.{v} C] :
    Core.functorToCore (Core.inclusion C) = Functor.id (Core C) :=
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
  IsLeftAdjoint.mk ⟨ Core.map , ⟨ adjunction ⟩ ⟩

instance : IsRightAdjoint Core.map :=
  IsRightAdjoint.mk ⟨ Grpd.forgetToCat , ⟨ adjunction ⟩ ⟩

/- This whole section is evil. -/
namespace IsPullback

noncomputable section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D)

lemma w' : Cat.homOf (inclusion C) ≫ Cat.homOf F
    = Cat.homOf (Core.map' F) ⋙ Cat.homOf (inclusion D) := rfl

open Limits

variable {F} [F.ReflectsIsomorphisms]
  (s : PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D)))

def lift :
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

@[simp] theorem fac_left :
    lift s ≫ Cat.homOf (inclusion C) = s.fst := rfl

@[simp] theorem fac_right :
    lift s ≫ Cat.homOf (map' F) = s.snd := by
  apply Functor.ext
  · intro x y f
    apply Functor.map_injective (inclusion D)
    have h := Functor.congr_hom s.condition f
    unfold Cat.homOf at *
    unfold inclusion at *
    simp only [Cat.of_α, Cat.comp_obj, lift, map', comp_hom] at *
    convert h
    · apply Core.eqToIso_hom
    · apply Core.eqToIso_hom
  · intro x
    exact Functor.congr_obj s.condition x

def lift_uniq (m : s.pt ⟶ Cat.of (Core C))
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
 Core.map' F               F
    |                          |
    |                          |
    V                          V
  Core D ---- inclusion -----> D
-/
theorem isPullback_map'_self :
    IsPullback
      (Cat.homOf $ inclusion C)
      (Cat.homOf $ map' F)
      (Cat.homOf F)
      (Cat.homOf $ inclusion D) :=
  IsPullback.of_isLimit $
    Limits.PullbackCone.IsLimit.mk
      (w' F) lift fac_left fac_right
      (λ s m fl _ ↦ lift_uniq s m fl)

end Core

namespace Equivalence
noncomputable section
open Limits ChosenFiniteProducts

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [ChosenFiniteProducts C]
  (e : Equivalence C D)

/-- The chosen terminal object in `D`. -/
abbrev chosenTerminal : D :=
  e.functor.obj MonoidalCategory.tensorUnit

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
  isLimitChosenFiniteProductsOfPreservesLimits e.functor
    (e.inverse.obj X) (e.inverse.obj Y))))
  (BinaryFan.ext (eqToIso rfl) (by aesop_cat) (by aesop_cat))

def chosenFiniteProducts [ChosenFiniteProducts C] :
  ChosenFiniteProducts D where
  product X Y := { isLimit := e.isLimitProdCone X Y }
  terminal := { isLimit := e.chosenTerminalIsTerminal }

end
end Equivalence

namespace ULift
namespace Core

variable {C : Type u} [Category.{v} C]

-- FIXME could be generalized?
def isoCoreULift :
    Cat.of (ULift.{w} (Core C)) ≅
      Cat.of (Core (ULift.{w} C)) where
  hom := Cat.homOf (downFunctor ⋙ Core.map' upFunctor)
  inv := Cat.homOf (Core.map' downFunctor ⋙ upFunctor)

end Core
end ULift

section equivalence

def functorToAsSmallEquiv {D : Type u₁} [Category.{v₁} D] {C : Type u} [Category.{v} C]
    : D ⥤ AsSmall.{w} C ≃ D ⥤ C where
  toFun A := A ⋙ AsSmall.down
  invFun A := A ⋙ AsSmall.up
  left_inv _ := rfl
  right_inv _ := rfl

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
    (A.map (𝟙 x)).obj a = a := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_obj this a

theorem Cat.map_id_map {A : Γ ⥤ Cat.{v₁,u₁}}
    {x : Γ} {a b : A.obj x} {f : a ⟶ b} :
    (A.map (𝟙 x)).map f = eqToHom Cat.map_id_obj
      ≫ f ≫ eqToHom Cat.map_id_obj.symm := by
  have : A.map (𝟙 x) = 𝟙 (A.obj x) := by simp
  exact Functor.congr_hom this f

end

namespace Grothendieck

variable {C : Type u} [Category.{v} C]
variable {F : C ⥤ Cat.{v₂, u₂}}

theorem ιNatTrans_id_app {X : C} {a : F.obj X} :
    (@ιNatTrans _ _ F _ _ (𝟙 X)).app a =
    eqToHom (by simp) := by
  apply ext
  · simp
  · simp [eqToHom_base]

theorem ιNatTrans_comp_app {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {a} :
    (@ιNatTrans _ _ F _ _ (f ≫ g)).app a =
    (@ιNatTrans _ _ F _ _ f).app a ≫
    (@ιNatTrans _ _ F _ _ g).app ((F.map f).obj a) ≫ eqToHom (by simp) := by
  apply Grothendieck.ext
  · simp
  · simp

variable {Γ : Type u₂} [Category.{v₂} Γ] {Δ : Type u₃} [Category.{v₃} Δ]
    (σ : Δ ⥤ Γ)

@[simp] theorem ιCompPre (A : Γ ⥤ Cat.{v₁,u₁}) (x : Δ)
    : ι (σ ⋙ A) x ⋙ Grothendieck.pre A σ = ι A (σ.obj x) := by
  apply CategoryTheory.Functor.ext
  · intro x y f
    apply Grothendieck.ext
    · simp [eqToHom_map, Cat.map_id_map]
    · simp
  · intro x
    rfl

section
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ Cat.{v₂,u₂})

theorem preNatIso_congr {G H : D ⥤ C} {α β : G ≅ H} (h : α = β) :
    preNatIso F α = preNatIso F β ≪≫ eqToIso (by subst h; simp) := by
  subst h
  simp

@[simp] theorem preNatIso_eqToIso {G H : D ⥤ C} {h : G = H} :
    preNatIso F (eqToIso h) = eqToIso (by
      subst h
      simp [Grothendieck.map_id_eq, Cat.id_eq_id, Functor.id_comp]) := by
  subst h
  ext
  apply Grothendieck.ext
  · simp only [eqToIso_refl, Iso.refl_hom, eqToIso.hom, Category.comp_id,
      pre_obj_fiber, preNatIso, transportIso, transport_base,
      isoMk, transport_fiber, Iso.refl_inv, Iso.symm_mk, NatIso.ofComponents_hom_app]
    rw! [eqToHom_app, eqToHom_fiber]
  · simp [preNatIso]

theorem preNatIso_comp {G1 G2 G3 : D ⥤ C} (α : G1 ≅ G2) (β : G2 ≅ G3) :
    preNatIso F (α ≪≫ β) = preNatIso F α ≪≫ isoWhiskerLeft _ (preNatIso F β) ≪≫
    eqToIso (by simp [map_comp_eq, Functor.assoc]) := by
  ext p
  apply Grothendieck.ext
  · simp only [Iso.trans_hom, Functor.comp_obj, pre_obj_base, map_obj_base, preNatIso,
      Iso.app_hom, isoWhiskerLeft_hom, eqToIso.hom, NatTrans.comp_app,
      NatIso.ofComponents_hom_app, Iso.symm_hom, whiskerLeft_app,
      map_obj_fiber, transportIso_inv_base, pre_obj_fiber,
      transportIso_inv_fiber, Category.comp_id, comp_fiber, Functor.map_id,
      Category.id_comp, eqToHom_app, base_eqToHom,
      eqToHom_refl, Cat.id_obj, eqToHom_naturality_assoc, eqToHom_trans_assoc]
    rw! [eqToHom_app, eqToHom_fiber, eqToHom_trans]
  · simp [preNatIso]

end

end Grothendieck

-- NOTE this was added to mathlib very recently
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]
@[simp]
theorem isoWhiskerLeft_trans (F : C ⥤ D) {G H K : D ⥤ E} (α : G ≅ H) (β : H ≅ K) :
    isoWhiskerLeft F (α ≪≫ β) = isoWhiskerLeft F α ≪≫ isoWhiskerLeft F β :=
  rfl

section
variable {B : Type u} [Category.{v} B]

@[simp]
theorem isoWhiskerLeft_eqToIso (F : C ⥤ D) {G H : D ⥤ E} (η : G = H) :
    isoWhiskerLeft F (eqToIso η) = eqToIso (by subst η; rfl) := by
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

-- TODO: delete this when bumping mathlib, it's in newer versions.
namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {X Y Z : C}
variable (hF : F.FullyFaithful)

@[simp]
lemma preimage_id {X : C} :
    hF.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  hF.map_injective (by simp)

@[simp, reassoc]
lemma preimage_comp {X Y Z : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    hF.preimage (f ≫ g) = hF.preimage f ≫ hF.preimage g :=
  hF.map_injective (by simp)

end CategoryTheory.Functor.FullyFaithful

namespace CategoryTheory

variable {C : Type u₁} [SmallCategory C] {F G : Cᵒᵖ ⥤ Type u₁}
  (app : ∀ {X : C}, (yoneda.obj X ⟶ F) → (yoneda.obj X ⟶ G))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y) (α : yoneda.obj Y ⟶ F),
    app (yoneda.map f ≫ α) = yoneda.map f ≫ app α)

variable (F) in
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

end CategoryTheory
