/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joseph Hua
-/

import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.Tactic.DepRewrite
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic
import HoTTLean.ForMathlib.CategoryTheory.Functor.Iso
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.CategoryTheory.Whiskering
import HoTTLean.ForMathlib.CategoryTheory.NatTrans

/-!
Compatibility layer for the Grothendieck construction.

Most of the old contents of this file have been upstreamed to mathlib as
`CategoryTheory.Grothendieck` and `CategoryTheory.Pseudofunctor.Grothendieck`.  This file keeps the
old `CategoryTheory.Functor.Grothendieck` names used by HoTTLean and adds a few helper lemmas whose
statements predate the upstream names.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe w v v₁ v₂ u u₁ u₂

open Category Opposite Discrete Bicategory

namespace Cat

/-- An `eqToHom` in the category `Cat` is a functor that acts on maps by casts. -/
theorem map_eqToHom {C1 C2 : Cat} {x y : C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).toFunctor.map f = cast (by subst eq; rfl) f := by
  subst eq
  rfl

end Cat

namespace Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]
variable {E : Type*} [Category E]
variable (F : C ⥤ Cat.{v₂, u₂})

/-- Backwards-compatible namespace for mathlib's `CategoryTheory.Grothendieck`. -/
abbrev Grothendieck (F : C ⥤ Cat.{v₂, u₂}) := CategoryTheory.Grothendieck F

/-- Notation for the Grothendieck category associated to a functor `F`. -/
scoped prefix:75 "∫ " => Grothendieck

namespace Grothendieck

attribute [local simp] eqToHom_map

abbrev Hom {F : C ⥤ Cat.{v₂, u₂}} (X Y : Grothendieck F) := CategoryTheory.Grothendieck.Hom X Y

lemma ext {F : C ⥤ Cat.{v₂, u₂}} {x y : ∫ F} (hbase : x.base = y.base)
    (hfiber : (F.map (eqToHom hbase)).toFunctor.obj x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  simp only at hbase
  subst hbase
  simp at hfiber
  subst hfiber
  rfl

lemma hext {F : C ⥤ Cat.{v₂, u₂}} {x y : ∫ F} (hbase : x.base = y.base)
    (hfiber : HEq x.fiber y.fiber) : x = y := by
  cases x
  cases y
  simp only at hbase
  subst hbase
  cases hfiber
  rfl

lemma hext' {F : C ⥤ Cat.{v₂, u₂}} {x y : ∫ F} (hbase : x.base = y.base)
    (hfiber : HEq x.fiber y.fiber := by subst hbase; rfl) : x = y :=
  hext hbase hfiber

namespace Hom

variable {F : C ⥤ Cat.{v₂, u₂}} {X Y Z : ∫ F}

abbrev id (X : ∫ F) : X ⟶ X := CategoryTheory.Grothendieck.id X
abbrev comp (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := CategoryTheory.Grothendieck.comp f g

@[simp] theorem mk_base (b : X.base ⟶ Y.base)
    (f : (F.map b).toFunctor.obj X.fiber ⟶ Y.fiber) :
    (CategoryTheory.Grothendieck.Hom.mk b f).base = b := rfl

@[simp] theorem mk_fiber (b : X.base ⟶ Y.base)
    (f : (F.map b).toFunctor.obj X.fiber ⟶ Y.fiber) :
    (CategoryTheory.Grothendieck.Hom.mk b f).fiber = f := rfl

@[ext (iff := false)]
lemma ext (f g : X ⟶ Y) (hfg₁ : f.base = g.base)
    (hfg₂ : eqToHom (hfg₁ ▸ rfl) ≫ f.fiber = g.fiber) : f = g :=
  CategoryTheory.Grothendieck.ext f g hfg₁ hfg₂

lemma hext (f g : X ⟶ Y) (hfg₁ : f.base = g.base) (hfg₂ : HEq f.fiber g.fiber) : f = g := by
  sorry

lemma hext' (f g : X ⟶ Y) (hfg₁ : f.base = g.base)
    (hfg₂ : HEq f.fiber g.fiber := by subst hfg₁; rfl) : f = g :=
  hext f g hfg₁ hfg₂

lemma congr {f g : X ⟶ Y} (h : f = g) : f.fiber = eqToHom (h ▸ rfl) ≫ g.fiber :=
  CategoryTheory.Grothendieck.congr h

@[simp] theorem id_base (X : ∫ F) : (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  CategoryTheory.Grothendieck.id_base X

@[simp] theorem id_fiber (X : ∫ F) : (𝟙 X : X ⟶ X).fiber = eqToHom (by simp) :=
  CategoryTheory.Grothendieck.id_fiber X

@[simp] theorem comp_base (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  CategoryTheory.Grothendieck.comp_base f g

@[simp] theorem comp_fiber (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      eqToHom (by simp) ≫ (F.map g.base).toFunctor.map f.fiber ≫ g.fiber :=
  CategoryTheory.Grothendieck.comp_fiber f g

end Hom

@[simp] theorem base_eqToHom {F : C ⥤ Cat.{v₂, u₂}} {X Y : ∫ F} (h : X = Y) :
    (eqToHom h : X ⟶ Y).base = eqToHom (congrArg CategoryTheory.Grothendieck.base h) :=
  CategoryTheory.Grothendieck.base_eqToHom h

@[simp] theorem fiber_eqToHom {F : C ⥤ Cat.{v₂, u₂}} {X Y : ∫ F} (h : X = Y) :
    (eqToHom h : X ⟶ Y).fiber = eqToHom (by subst h; simp) :=
  CategoryTheory.Grothendieck.fiber_eqToHom h

abbrev forget (F : C ⥤ Cat.{v₂, u₂}) : ∫ F ⥤ C := CategoryTheory.Grothendieck.forget F

@[simp] theorem forget_obj {F : C ⥤ Cat.{v₂, u₂}} (X : ∫ F) : (forget F).obj X = X.base := rfl
@[simp] theorem forget_map {F : C ⥤ Cat.{v₂, u₂}} {X Y : ∫ F} (f : X ⟶ Y) :
    (forget F).map f = f.base := rfl

abbrev transport {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (t : x.base ⟶ c) : ∫ F :=
  CategoryTheory.Grothendieck.transport x t

abbrev toTransport {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (t : x.base ⟶ c) :
    x ⟶ transport x t :=
  CategoryTheory.Grothendieck.toTransport x t

@[simp] theorem transport_base {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (t : x.base ⟶ c) :
    (transport x t).base = c := rfl
@[simp] theorem transport_fiber {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (t : x.base ⟶ c) :
    (transport x t).fiber = (F.map t).toFunctor.obj x.fiber := rfl
@[simp] theorem toTransport_base {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (t : x.base ⟶ c) :
    (toTransport x t).base = t := rfl
@[simp] theorem toTransport_fiber {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (t : x.base ⟶ c) :
    (toTransport x t).fiber = 𝟙 _ := rfl

theorem transport_id {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) : transport x (𝟙 x.base) = x := by
  apply hext <;> simp

theorem toTransport_id {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) :
    toTransport x (𝟙 x.base) = eqToHom (transport_id x).symm := by
  sorry

theorem transport_eqToHom {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (h : x.base = c) :
    transport x (eqToHom h) = ⟨c, cast (by subst h; rfl) x.fiber⟩ := by
  subst h
  apply hext <;> simp

theorem toTransport_eqToHom {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (h : x.base = c) :
    True := by
  trivial

theorem transport_comp {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c d : C} (f : x.base ⟶ c) (g : c ⟶ d) :
    transport (transport x f) g = transport x (f ≫ g) := by
  apply hext <;> simp [CategoryTheory.Grothendieck.transport]

theorem toTransport_comp {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c d : C} (f : x.base ⟶ c) (g : c ⟶ d) :
    toTransport x (f ≫ g) =
      toTransport x f ≫ toTransport (transport x f) g ≫ eqToHom (transport_comp x f g) := by
  apply CategoryTheory.Grothendieck.ext
  · simp [transport_comp]
  · simp [toTransport, transport]

abbrev isoMk {F : C ⥤ Cat.{v₂, u₂}} {X Y : ∫ F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).toFunctor.obj X.fiber ≅ Y.fiber) : X ≅ Y :=
  CategoryTheory.Grothendieck.isoMk e₁ e₂

abbrev transportIso {F : C ⥤ Cat.{v₂, u₂}} (x : ∫ F) {c : C} (α : x.base ≅ c) :
    transport x α.hom ≅ x :=
  CategoryTheory.Grothendieck.transportIso x α

abbrev map {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) : ∫ F ⥤ ∫ G :=
  CategoryTheory.Grothendieck.map α

@[simp] theorem map_obj_base {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) (X : ∫ F) :
    ((map α).obj X).base = X.base := rfl
@[simp] theorem map_obj_fiber {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) (X : ∫ F) :
    ((map α).obj X).fiber = (α.app X.base).toFunctor.obj X.fiber := rfl
@[simp] theorem map_map_base {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) {X Y : ∫ F} (f : X ⟶ Y) :
    ((map α).map f).base = f.base := rfl
@[simp] theorem map_map_fiber {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) {X Y : ∫ F} (f : X ⟶ Y) :
    ((map α).map f).fiber =
      (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
        (α.app Y.base).toFunctor.map f.fiber := by
  sorry

theorem map_comp_forget {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) :
    map α ⋙ forget G = forget F := rfl

theorem map_id_eq {F : C ⥤ Cat.{v₂, u₂}} : map (𝟙 F) = Functor.id (∫ F) :=
  CategoryTheory.Grothendieck.map_id_eq

theorem map_comp_eq {F G H : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β :=
  CategoryTheory.Grothendieck.map_comp_eq α β

abbrev pre (F : C ⥤ Cat.{v₂, u₂}) (G : D ⥤ C) : ∫ (G ⋙ F) ⥤ ∫ F :=
  CategoryTheory.Grothendieck.pre F G

abbrev preNatIso (F : C ⥤ Cat.{v₂, u₂}) {G H : D ⥤ C} (α : G ≅ H) :
    pre F G ≅ map (whiskerRight α.hom F) ⋙ pre F H :=
  CategoryTheory.Grothendieck.preNatIso F α

@[simp] theorem preNatIso_hom_app_base (F : C ⥤ Cat.{v₂, u₂}) {G H : D ⥤ C} (α : G ≅ H) (x) :
    ((preNatIso F α).hom.app x).base = α.hom.app x.base := rfl

@[simp] theorem preNatIso_hom_app_fiber (F : C ⥤ Cat.{v₂, u₂}) {G H : D ⥤ C} (α : G ≅ H) (x) :
    ((preNatIso F α).hom.app x).fiber = 𝟙 _ := rfl

abbrev preUnitIso (F : C ⥤ Cat.{v₂, u₂}) (G : D ≌ C) :
    map (whiskerRight G.unitInv (G.functor ⋙ F)) ≅ pre (G.functor ⋙ F) (G.functor ⋙ G.inverse) :=
  CategoryTheory.Grothendieck.preUnitIso F G

/- Construct a functor into a Grothendieck construction from fiber data. -/
def functorTo {F : C ⥤ Cat.{v₂, u₂}} (A : D ⥤ C) (fibObj : (x : D) → (F.obj (A.obj x)))
    (fibMap : {x y : D} → (f : x ⟶ y) → (F.map (A.map f)).toFunctor.obj (fibObj x) ⟶ fibObj y)
    (map_id : ∀ x, fibMap (𝟙 x) = eqToHom (by simp))
    (map_comp : ∀ {x y z : D} (f : x ⟶ y) (g : y ⟶ z),
      fibMap (f ≫ g) = eqToHom (by simp) ≫ (F.map (A.map g)).toFunctor.map (fibMap f) ≫ fibMap g) :
    D ⥤ ∫ F where
  obj x := ⟨A.obj x, fibObj x⟩
  map f := ⟨A.map f, fibMap f⟩
  map_id x := by
    apply CategoryTheory.Grothendieck.ext <;> simp [map_id]
  map_comp f g := by
    apply CategoryTheory.Grothendieck.ext <;> simp [map_comp]

section FunctorToLemmas

variable {F : C ⥤ Cat.{v₂, u₂}} (A : D ⥤ C)
variable (fibObj : (x : D) → F.obj (A.obj x))
variable (fibMap : {x y : D} → (f : x ⟶ y) → (F.map (A.map f)).toFunctor.obj (fibObj x) ⟶ fibObj y)
variable (map_id : ∀ x, fibMap (𝟙 x) = eqToHom (by simp))
variable (map_comp : ∀ {x y z : D} (f : x ⟶ y) (g : y ⟶ z),
  fibMap (f ≫ g) = eqToHom (by simp) ≫ (F.map (A.map g)).toFunctor.map (fibMap f) ≫ fibMap g)

@[simp] theorem functorTo_obj_base (x : D) :
    ((functorTo A fibObj fibMap map_id map_comp).obj x).base = A.obj x := rfl
@[simp] theorem functorTo_obj_fiber (x : D) :
    ((functorTo A fibObj fibMap map_id map_comp).obj x).fiber = fibObj x := rfl
@[simp] theorem functorTo_map_base {x y : D} (f : x ⟶ y) :
    ((functorTo A fibObj fibMap map_id map_comp).map f).base = A.map f := rfl
@[simp] theorem functorTo_map_fiber {x y : D} (f : x ⟶ y) :
    ((functorTo A fibObj fibMap map_id map_comp).map f).fiber = fibMap f := rfl
@[simp] theorem functorTo_forget :
    functorTo A fibObj fibMap map_id map_comp ⋙ forget F = A := rfl

end FunctorToLemmas

namespace FunctorTo

lemma hext {F : C ⥤ Cat.{v₂, u₂}} {A B : D ⥤ ∫ F}
    (hbase : A ⋙ forget F = B ⋙ forget F)
    (hfiber_obj : ∀ x, HEq ((A.obj x).fiber) ((B.obj x).fiber))
    (hfiber_map : ∀ {x y} (f : x ⟶ y), HEq ((A.map f).fiber) ((B.map f).fiber)) : A = B := by
  sorry

end FunctorTo

abbrev ι (F : C ⥤ Cat.{v₂, u₂}) (c : C) : F.obj c ⥤ ∫ F :=
  CategoryTheory.Grothendieck.ι F c
abbrev ιNatTrans {F : C ⥤ Cat.{v₂, u₂}} {X Y : C} (f : X ⟶ Y) :
    ι F X ⟶ (F.map f).toFunctor ⋙ ι F Y :=
  CategoryTheory.Grothendieck.ιNatTrans (F := F) f

@[simp] theorem ιNatTrans_id_app {F : C ⥤ Cat.{v₂, u₂}} {X : C} {a : F.obj X} :
    (@ιNatTrans _ _ F _ _ (𝟙 X)).app a = eqToHom (by simp) := by
  apply Hom.ext <;> simp

lemma ιNatTrans_comp_app {F : C ⥤ Cat.{v₂, u₂}} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {a} :
    (@ιNatTrans _ _ F _ _ (f ≫ g)).app a =
    (@ιNatTrans _ _ F _ _ f).app a ≫
    (@ιNatTrans _ _ F _ _ g).app ((F.map f).toFunctor.obj a) ≫ eqToHom (by simp) := by
  apply Hom.ext <;> simp

abbrev functorFrom {F : C ⥤ Cat.{v₂, u₂}} {E : Type*} [Category E]
    (fib : ∀ c, F.obj c ⥤ E)
    (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c')
    (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
    (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
      hom f ≫ whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl)) :
    ∫ F ⥤ E :=
  CategoryTheory.Grothendieck.functorFrom fib hom hom_id hom_comp

section FunctorFromCompat

variable {F : C ⥤ Cat.{v₂, u₂}} {E : Type*} [Category E]
variable (fib : ∀ c, F.obj c ⥤ E)
variable (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

@[simp] theorem functorFrom_obj (X : ∫ F) :
    (functorFrom fib hom hom_id hom_comp).obj X = (fib X.base).obj X.fiber :=
  CategoryTheory.Grothendieck.functorFrom_obj fib hom hom_id hom_comp X

@[simp] theorem functorFrom_map {X Y : ∫ F} (f : X ⟶ Y) :
    (functorFrom fib hom hom_id hom_comp).map f =
      (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber :=
  CategoryTheory.Grothendieck.functorFrom_map fib hom hom_id hom_comp f

/-- `Grothendieck.ι F c` composed with `Grothendieck.functorFrom` is isomorphic to a functor on a fiber. -/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  CategoryTheory.Grothendieck.ιCompFunctorFrom fib hom hom_id hom_comp c

@[simp]
lemma ι_comp_functorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) = fib c :=
  Functor.ext_of_iso (ιCompFunctorFrom fib hom hom_id hom_comp c) (by intro; rfl)

lemma whiskerRight_ιNatTrans_functorFrom {x y : C} (f : x ⟶ y) :
    whiskerRight (ιNatTrans (F := F) f) (functorFrom fib hom hom_id hom_comp) =
    eqToHom (ι_comp_functorFrom fib hom hom_id hom_comp x) ≫ hom f ≫
    eqToHom (by rw [Functor.assoc, ι_comp_functorFrom fib hom hom_id hom_comp y]) := by
  ext a
  simp

abbrev asFunctorFromFib (K : ∫ F ⥤ E) (c : C) : F.obj c ⥤ E := ι F c ⋙ K

abbrev asFunctorFromHom (K : ∫ F ⥤ E) {c c' : C} (f : c ⟶ c') :
    asFunctorFromFib K c ⟶ (F.map f).toFunctor ⋙ asFunctorFromFib K c' :=
  whiskerRight (ιNatTrans f) K

lemma asFunctorFromHom_id (K : ∫ F ⥤ E) (c : C) : asFunctorFromHom K (𝟙 c) =
    eqToHom (by simp only [Functor.map_id, Cat.Hom.id_toFunctor, Functor.id_comp]) := by
  ext p
  simp [eqToHom_map, ιNatTrans_id_app]

lemma asFunctorFromHom_comp (K : ∫ F ⥤ E) (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g: c₂ ⟶ c₃) :
    asFunctorFromHom K (f ≫ g) =
    asFunctorFromHom K f ≫ whiskerLeft (F.map f).toFunctor (asFunctorFromHom K g) ≫ eqToHom
    (by simp only [Functor.map_comp, Cat.Hom.comp_toFunctor]; rfl) := by
  ext p
  simp [asFunctorFromHom, eqToHom_map, ιNatTrans_comp_app]

theorem asFunctorFrom (K : ∫ F ⥤ E) : functorFrom (asFunctorFromFib K) (asFunctorFromHom K)
    (asFunctorFromHom_id K) (asFunctorFromHom_comp K) = K := by
  fapply CategoryTheory.Functor.ext
  · intro X
    rfl
  · intro x y f
    simp only [asFunctorFromFib, Functor.comp_obj, functorFrom_map,
      asFunctorFromHom, whiskerRight_app, Functor.comp_map, ← Functor.map_comp,
      eqToHom_refl, Category.comp_id, Category.id_comp]
    congr
    apply CategoryTheory.Grothendieck.ext <;> simp

section
variable (fib' : ∀ c, F.obj c ⥤ E)
variable (hom' : ∀ {c c' : C} (f : c ⟶ c'), fib' c ⟶ (F.map f).toFunctor ⋙ fib' c')
variable (hom_id' : ∀ c, hom' (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp' : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom' (f ≫ g) =
  hom' f ≫ whiskerLeft (F.map f).toFunctor (hom' g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

theorem functorFrom_eq_of (ef : fib = fib')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), hom f ≫ eqToHom (by rw[ef]) = eqToHom (by rw[ef]) ≫ hom' f) :
    functorFrom fib hom hom_id hom_comp = functorFrom fib' hom' hom_id' hom_comp' := by
  subst ef
  congr!
  · aesop_cat

end

theorem functorFrom_ext {K K' : ∫ F ⥤ E}
    (hfib : ∀ c, ι F c ⋙ K = ι F c ⋙ K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), whiskerRight (ιNatTrans f) K ≫
      eqToHom (by simp [Functor.assoc, hfib])
      = eqToHom (by rw[hfib]) ≫ whiskerRight (ιNatTrans f) K') : K = K' :=
    calc K
     _ = functorFrom (asFunctorFromFib K) (asFunctorFromHom K)
         (asFunctorFromHom_id K) (asFunctorFromHom_comp K) :=
         (asFunctorFrom K).symm
     _ = functorFrom (asFunctorFromFib K') (asFunctorFromHom K')
         (asFunctorFromHom_id K') (asFunctorFromHom_comp K') := by
         apply functorFrom_eq_of
         · exact hhom
         · ext
           apply hfib
     _ = K' := asFunctorFrom K'

theorem functorFrom_hext {K K' : ∫ F ⥤ E}
    (hfib : ∀ c, ι F c ⋙ K = ι F c ⋙ K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), whiskerRight (ιNatTrans f) K ≍
      whiskerRight (ιNatTrans f) K') : K = K' := by
  fapply functorFrom_ext
  · assumption
  · intros
    apply eq_of_heq
    simp only [heq_eqToHom_comp_iff, comp_eqToHom_heq_iff]
    apply hhom

end FunctorFromCompat

lemma ι_comp_map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F') (c : C) :
    ι F c ⋙ map α = (α.app c).toFunctor ⋙ ι F' c :=
  Functor.ext_of_iso (CategoryTheory.Grothendieck.ιCompMap α c) (by intro; rfl)

end Grothendieck

end Functor

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]

lemma _root_.CategoryTheory.Functor.toPseudofunctor'_map₂ (F : C ⥤ Cat.{v₂, u₂})
    {a b : LocallyDiscrete C} {f g : a ⟶ b} (η : f ⟶ g) :
    True := by
  trivial

def _root_.CategoryTheory.NatTrans.toStrongTrans' (F G : C ⥤ Cat.{v₂, u₂}) (α : F ⟶ G) :
    Pseudofunctor.StrongTrans F.toPseudofunctor' G.toPseudofunctor' where
  app x := α.app x.as
  naturality f := by exact sorry
  naturality_naturality η := by sorry
  naturality_id _ := by sorry
  naturality_comp _ _ := by sorry

end Pseudofunctor

end CategoryTheory
