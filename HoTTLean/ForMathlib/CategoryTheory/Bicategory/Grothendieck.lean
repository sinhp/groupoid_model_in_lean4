/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joseph Hua
-/

import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
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
# The Grothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮` to `Cat`, we associate to it a category
`∫ F`, equipped with a functor `∫ F ⥤ 𝒮`.

The category `∫ F` is defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : b ⟶ F(f)(a)`

The projection functor `∫ F ⥤ 𝒮` is then given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## Future work / TODO

1. Once the bicategory of pseudofunctors has been defined, show that this construction forms a
pseudofunctor from `Pseudofunctor (LocallyDiscrete 𝒮) Cat` to `Cat`.
2. One could probably deduce the results in `CategoryTheory.Grothendieck` as a specialization of the
results in this file.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

namespace CategoryTheory.Pseudofunctor

universe w v₁ v₂ v₃ u₁ u₂ u₃

open Category Opposite Discrete Bicategory StrongTrans

section

variable {B : Type u₁} [Bicategory B]
variable (F : Pseudofunctor B Cat) {a b : B}

@[simp] lemma _root_.CategoryTheory.LocallyDiscrete.Iso.hom_inv {C : Type u₁} [Category C]
    (X Y : LocallyDiscrete C) (e : X ≅ Y) : e.hom.toLoc ≫ e.inv.toLoc = 𝟙 _ :=
  LocallyDiscrete.eq_of_hom ⟨⟨by simp⟩⟩

end

lemma _root_.CategoryTheory.Functor.toPseudofunctor'_map₂ {C : Type u₁} [Category.{v₁} C] (F : C ⥤ Cat)
    {a b : LocallyDiscrete C} {f g : a ⟶ b} (η : f ⟶ g) :
    F.toPseudoFunctor'.map₂ η = eqToHom (by simp [eq_of_hom η]) := by
  simp [Functor.toPseudoFunctor', pseudofunctorOfIsLocallyDiscrete]

@[simps]
def _root_.CategoryTheory.NatTrans.toStrongTrans' {C : Type u₁} [Category.{v₁} C] (F G : C ⥤ Cat) (α : F ⟶ G) :
    F.toPseudoFunctor' ⟶ G.toPseudoFunctor' where
  app x := α.app x.as
  naturality _ := eqToIso (α.naturality _)
  naturality_naturality η := by simp [Functor.toPseudofunctor'_map₂]
  naturality_id _ := by ext; simp [Bicategory.leftUnitor, Bicategory.rightUnitor]
  naturality_comp _ _ := by ext; simp [Bicategory.associator]

/-- An `eqToHom` in the category `Cat` is a functor that acts on maps by casts. -/
theorem _root_.CategoryTheory.Cat.map_eqToHom {C1 C2 : Cat} {x y : C1} (f : x ⟶ y) (eq : C1 = C2) :
    (eqToHom eq).map f = (cast (by subst eq; rfl) f) := by
  cases eq
  simp [CategoryStruct.id]

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}

/-- The type of objects in the fibered category associated to a presheaf valued in types. -/
@[ext]
structure Grothendieck (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨base⟩

namespace Grothendieck

/-- Notation for the Grothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ " => Grothendieck

/-- A morphism in the Grothendieck construction `∫ F` between two points `X Y : ∫ F` consists of
a morphism in the base category `base : X.base ⟶ Y.base` and
a morphism in a fiber `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : ∫ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : (F.map base.toLoc).obj X.fiber ⟶ Y.fiber

@[simps! id_base id_fiber comp_base comp_fiber]
instance categoryStruct : CategoryStruct (∫ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨X.base⟩).hom.app X.fiber }
  comp {X _ _} f g := {
    base := f.base ≫ g.base
    fiber := (F.mapComp f.base.toLoc g.base.toLoc).hom.app X.fiber ≫
      (F.map g.base.toLoc).map f.fiber ≫ g.fiber }

instance (X : ∫ F) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

section

variable {a b : ∫ F}

@[ext (iff := false)]
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : eqToHom (hfg₁ ▸ rfl) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  dsimp at hfg₁ hfg₂
  rw! (castMode := .all) [← hfg₂, ← hfg₁]
  simp

lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ ∃ (hfg : f.base = g.base), eqToHom (hfg ▸ rfl) ≫ f.fiber = g.fiber where
  mp hfg := by subst hfg; simp
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

lemma Hom.congr {a b : ∫ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = eqToHom (h ▸ rfl) ≫ g.fiber := by
  subst h
  simp

end

/-- The category structure on `∫ F`. -/
instance category : Category (∫ F) where
  toCategoryStruct := Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_hom_app, PrelaxFunctor.map₂_eqToHom, Strict.leftUnitor_eqToIso,
        ← Functor.map_comp_assoc]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_hom_app, PrelaxFunctor.map₂_eqToHom, Strict.rightUnitor_eqToIso]
  assoc f g h := by
    ext
    · simp
    · simp [PrelaxFunctor.map₂_eqToHom, mapComp_assoc_right_hom_app_assoc,
        Strict.associator_eqToIso]

variable (F)

/-- The projection `∫ F ⥤ 𝒮` given by projecting both objects and homs to the first
factor. -/
@[simps]
def forget (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}) : ∫ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base

section

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

variable {F} {G : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}
  {H : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}

/-- The Grothendieck construction is functorial: a strong natural transformation `α : F ⟶ G`
induces a functor `Grothendieck.map : ∫ F ⥤ ∫ G`.
-/
@[simps!]
def map (α : F ⟶ G) : ∫ F ⥤ ∫ G where
  obj a := {
    base := a.base
    fiber := (α.app ⟨a.base⟩).obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.naturality f.1.toLoc).inv.app a.fiber ≫ (α.app ⟨b.base⟩).map f.2 }
  map_id a := by
    ext
    · dsimp
    · simp [StrongTrans.naturality_id_inv_app, ← Functor.map_comp]
  map_comp {a b c} f g := by
    ext
    · dsimp
    · simp only [categoryStruct_comp_base, Quiver.Hom.comp_toLoc,
        StrongTrans.naturality_comp_inv_app_assoc, ← Functor.map_comp]
      have := (α.naturality g.base.toLoc).inv.naturality_assoc
      simp only [Cat.comp_map] at this
      simp [this]

@[simp]
lemma map_id_map {x y : ∫ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f := by
  ext <;> simp

@[simp]
theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

section

variable (F)

/-- The natural isomorphism witnessing the pseudo-unity constraint of `Grothendieck.map`. -/
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ F) :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by aesop_cat))

lemma map_id_eq : map (𝟙 F) = 𝟭 (∫ F) :=
  Functor.ext_of_iso (mapIdIso F) (fun x ↦ by simp [map]) (fun x ↦ by simp [mapIdIso])

end

/-- The natural isomorphism witnessing the pseudo-functoriality of `Grothendieck.map`. -/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by aesop_cat)) (fun f ↦ by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

lemma map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β :=
  Functor.ext_of_iso (mapCompIso α β) (fun _ ↦ by simp [map]) (fun _ ↦ by simp [mapCompIso])

end

section Transport

variable {F} (x : ∫ F) {c : 𝒮}
/--
If `F : Pseudofunctor (LocallyDiscrete 𝒮) Cat` is a pseudofunctor and `t : c ⟶ d` is a morphism in
`C`, then `transport` maps each `c`-based element of `∫ F` to a `d`-based element.
-/
@[simps]
def transport (t : x.base ⟶ c) : ∫ F :=
  ⟨c, (F.map t.toLoc).obj x.fiber⟩

/--
If `F : Pseudofunctor (LocallyDiscrete 𝒮) Cat` is a pseudofunctor and `t : c ⟶ d` is a morphism in
`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identity on fibers.
-/
@[simps]
def toTransport (t : x.base ⟶ c) : x ⟶ x.transport t := ⟨t, (𝟙 _)⟩

end Transport

end Pseudofunctor.Grothendieck

end CategoryTheory

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

`Grothendieck.functor` makes the Grothendieck construction into a functor from the functor category
`C ⥤ Cat` to the over category `Over C` in the category of categories.

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

In `CategoryTheory.Bicategory.Grothendieck`,
`Cat` is treated as a strict 2-category and `F` is replaced with a pseudofunctor.
This file specializes this construction to 1-category theory.
The design of this file hides the 2-categorical definitions
so that the user only deals with the underlying 1-categories.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : f ⟶ (F.map (op β)).obj f'`.

## Notable constructions

- `Grothendieck F` is the Grothendieck construction.
- Elements of `Grothendieck F` whose base is `c : C` can be transported along `f : c ⟶ d` using
`transport`.
- A natural transformation `α : F ⟶ G` induces `map α : Grothendieck F ⥤ Grothendieck G`.
- The Grothendieck construction and `map` together form a functor (`functor`) from the functor
category `E ⥤ Cat` to the over category `Over E`.
- A functor `G : D ⥤ C` induces `pre F G : Grothendieck (G ⋙ F) ⥤ Grothendieck F`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/


universe w u v u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]
variable (F : C ⥤ Cat.{v₂, u₂})

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

/-- Notation for the Grothendieck category associated to a functor `F`. -/
scoped prefix:75 "∫ " => Grothendieck

namespace Grothendieck

attribute [local simp] eqToHom_map

variable {F}

lemma ext {x y : ∫ F} (hbase : x.base = y.base)
    (hfiber : (F.map (eqToHom hbase)).obj x.fiber = y.fiber) : x = y := by
  cases x; cases y
  congr
  · simp only [eqToHom_map] at hbase hfiber
    subst hbase
    simp [← hfiber]

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : ∫ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber

namespace Hom

variable {X Y : ∫ F} (f g : Hom X Y)

@[simp]
lemma mk_base (b : X.base ⟶ Y.base) (f : (F.map b).obj X.fiber ⟶ Y.fiber) : (mk b f).base = b :=
  rfl

@[simp]
lemma mk_fiber (b : X.base ⟶ Y.base) (f : (F.map b).obj X.fiber ⟶ Y.fiber) : (mk b f).fiber = f :=
  rfl

@[ext (iff := false)]
lemma ext (hfg₁ : f.base = g.base)
    (hfg₂ : eqToHom (hfg₁ ▸ rfl) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  dsimp at hfg₁ hfg₂
  rw! (castMode := .all) [← hfg₂, ← hfg₁]
  simp

lemma ext_iff : f = g ↔ ∃ (hfg : f.base = g.base), eqToHom (hfg ▸ rfl) ≫ f.fiber = g.fiber where
  mp hfg := by subst hfg; simp
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

lemma congr {f g : Hom X Y} (h : f = g) : f.fiber = eqToHom (h ▸ rfl) ≫ g.fiber := by
  subst h
  simp

/-- The identity morphism in the Grothendieck category.
-/
def id (X : ∫ F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by simp)

instance (X : ∫ F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
def comp {X Y Z : ∫ F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by simp) ≫ (F.map g.base).map f.fiber ≫ g.fiber

end Hom

attribute [local simp] eqToHom_map

instance : Category (∫ F) where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  comp_id {X Y} f := by
    ext
    · simp [Hom.comp, Hom.id]
    · dsimp [Hom.comp, Hom.id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_id Y.base)) f.fiber]
      simp
  id_comp f := by ext <;> simp [Hom.comp, Hom.id]
  assoc f g h := by
    ext
    · simp [Hom.comp]
    · dsimp [Hom.comp, Hom.id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) f.fiber]
      simp

namespace Hom

@[simp]
lemma id_base (X : ∫ F) :
    Hom.base (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
lemma id_fiber (X : ∫ F) :
    Hom.fiber (𝟙 X) = eqToHom (by simp) :=
  rfl

@[simp]
lemma comp_base {X Y Z : ∫ F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
lemma comp_fiber {X Y Z : ∫ F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) = eqToHom (by simp) ≫ (F.map g.base).map f.fiber ≫ g.fiber :=
  rfl

end Hom

@[simp]
lemma base_eqToHom {X Y : ∫ F} (h : X = Y) :
    (eqToHom h).base = eqToHom (by simp [h]) := by
  subst h; rfl

@[simp]
lemma fiber_eqToHom {X Y : ∫ F} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; simp) := by
  subst h; rfl

lemma eqToHom_eq_mk {X Y : ∫ F} (hF : X = Y) :
    eqToHom hF = Hom.mk (eqToHom (by subst hF; rfl)) (eqToHom (by subst hF; simp)) := by
  subst hF
  rfl

section

variable (F)

/-- The forgetful functor from `∫ F` to the source category. -/
@[simps!]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map f := f.1

end

section ext

theorem hext {x y : ∫ F} (hbase : x.base = y.base) (hfiber : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨xbase, xfiber⟩
  subst hbase
  subst hfiber
  rfl

theorem hext_iff {x y : ∫ F} : x.base = y.base ∧ HEq x.fiber y.fiber
    ↔ x = y := by
  constructor
  · intro ⟨ hα , hstr ⟩
    exact hext hα hstr
  · intro hCD
    subst hCD
    exact ⟨ rfl , HEq.rfl ⟩

theorem Hom.hext {X Y : ∫ F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : HEq f.fiber g.fiber) : f = g := by
  cases f; cases g
  congr

theorem Hom.hext_iff (x y : ∫ F) (f g : x ⟶ y) :
    f.base = g.base ∧ HEq f.fiber g.fiber ↔ f = g := by
  constructor
  · intro h
    exact Hom.hext _ _ h.1 h.2
  · aesop

variable {F' : C ⥤ Cat.{v₂, u₂}}

theorem hext' (h : F = F') {x : ∫ F} {y : ∫ F'}
    (hbase : HEq x.base y.base) (hfiber : HEq x.fiber y.fiber) : HEq x y := by
  rcases x; rcases y
  subst hbase
  congr

theorem Hom.hext' (h : F = F') {X Y : ∫ F} {X' Y' : ∫ F'} (hX : HEq X X') (hY : HEq Y Y')
    (f : Hom X Y) (g : Hom X' Y') (w_base : HEq f.base g.base) (w_fiber : HEq f.fiber g.fiber) :
    HEq f g := by
  cases f; cases g
  congr

theorem FunctorTo.hext (G H : D ⥤ ∫ F)
    (hbase : G ⋙ forget _ = H ⋙ forget _)
    (hfiber_obj : ∀ x : D, HEq (G.obj x).fiber (H.obj x).fiber)
    (hfiber_map : ∀ {x y : D} (f : x ⟶ y), HEq (G.map f).fiber (H.map f).fiber)
    : G = H := by
  fapply CategoryTheory.Functor.ext
  · intro x
    apply Grothendieck.hext
    · exact Functor.congr_obj hbase x
    · apply hfiber_obj
  · intro x y f
    fapply Grothendieck.Hom.hext
    · simp only [Hom.comp_base, base_eqToHom]
      exact Functor.congr_hom hbase f
    · simp only [Hom.comp_fiber, fiber_eqToHom, eqToHom_map, heq_eqToHom_comp_iff,
        heq_comp_eqToHom_iff]
      rw! [base_eqToHom, eqToHom_map, hfiber_map f, Cat.map_eqToHom]
      simp

end ext
section Transport

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element of `∫ F` to a `d`-based element.
-/
def transport (x : ∫ F) {c : C} (t : x.base ⟶ c) : ∫ F :=
  mk c ((F.map t).obj x.fiber)

@[simp]
def transport_base (x : ∫ F) {c : C} (t : x.base ⟶ c) : (transport x t).base = c :=
  rfl

@[simp]
def transport_fiber (x : ∫ F) {c : C} (t : x.base ⟶ c) :
    (transport x t).fiber = (F.map t).obj x.fiber :=
  rfl

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element `x` of `∫ F` to a `d`-based element `x.transport t`.

`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identity on fibers.
-/
def toTransport (x : ∫ F) {c : C} (t : x.base ⟶ c) : x ⟶ x.transport t :=
  Hom.mk t (𝟙 _)

@[simp]
def toTransport_base (x : ∫ F) {c : C} (t : x.base ⟶ c) : (toTransport x t).base = t :=
  rfl

@[simp]
def toTransport_fiber (x : ∫ F) {c : C} (t : x.base ⟶ c) :
    (toTransport x t).fiber = 𝟙 _ :=
  rfl

lemma transport_id {x : ∫ F} :
    transport x (𝟙 x.base) = x := by
  fapply Grothendieck.ext <;> simp [transport]

lemma transport_eqToHom {X: C} {X' : ∫ F} (hX': (forget F).obj X' = X):
    X'.transport (eqToHom hX') = X' := by
  subst hX'
  simp [transport_id]

lemma toTransport_id {X : ∫ F} :
    toTransport X (𝟙 X.base) = eqToHom transport_id.symm := by
  apply Grothendieck.Hom.ext <;> simp

lemma toTransport_eqToHom {X: C} {X' : ∫ F} (hX': (forget F).obj X' = X):
    toTransport X' (eqToHom hX') = eqToHom (by subst hX'; simp[transport_id]) := by
  subst hX'
  simp [toTransport_id]

lemma transport_comp (x : ∫ F) {c d: C} (t : x.base ⟶ c) (t': c ⟶ d):
      transport x (t ≫ t') = transport (c:= d) (transport x t) t' := by
  simp [transport]

lemma toTransport_comp (x : ∫ F) {c d: C} (t : x.base ⟶ c) (t': c ⟶ d):
    toTransport x (t ≫ t') =
    toTransport x t ≫ toTransport (transport x t) t' ≫ eqToHom (transport_comp x t t').symm := by
  simp only [← Category.assoc, ← heq_eq_eq, heq_comp_eqToHom_iff]
  simp only [toTransport, transport_base, transport_fiber]
  fapply Grothendieck.Hom.hext'
  · rfl
  · rfl
  · simp [transport_comp]
  · simp
  · simp only [transport_base, Hom.mk_base, transport_fiber, Hom.comp_base, Hom.comp_fiber, map_id,
      Category.comp_id]
    symm
    apply eqToHom_heq_id_dom

/--
Construct an isomorphism in a Grothendieck construction from isomorphisms in its base and fiber.
-/
def isoMk {X Y : ∫ F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).obj X.fiber ≅ Y.fiber) :
    X ≅ Y where
  hom := Hom.mk e₁.hom e₂.hom
  inv := Hom.mk e₁.inv ((F.map e₁.inv).map e₂.inv ≫
    eqToHom (Functor.congr_obj (F.mapIso e₁).hom_inv_id X.fiber))
  hom_inv_id := by apply Hom.ext; all_goals simp
  inv_hom_id := by
    apply Hom.ext
    · have := Functor.congr_hom (F.mapIso e₁).inv_hom_id e₂.inv
      simp only [mapIso_inv, mapIso_hom, Cat.comp_map] at this
      simp [this]
    · simp

@[simp]
lemma isoMk_hom_base {X Y : ∫ F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).obj X.fiber ≅ Y.fiber) :
    (isoMk e₁ e₂).hom.base = e₁.hom :=
  rfl

@[simp]
lemma isoMk_hom_fiber {X Y : ∫ F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).obj X.fiber ≅ Y.fiber) :
    (isoMk e₁ e₂).hom.fiber = e₂.hom :=
  rfl

@[simp]
lemma isoMk_inv_base {X Y : ∫ F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).obj X.fiber ≅ Y.fiber) :
    (isoMk e₁ e₂).inv.base = e₁.inv :=
  rfl

@[simp]
lemma isoMk_inv_fiber {X Y : ∫ F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).obj X.fiber ≅ Y.fiber) :
    (isoMk e₁ e₂).inv.fiber = (F.map e₁.inv).map e₂.inv ≫ eqToHom (by
      simp [← Functor.comp_obj, ← Cat.comp_eq_comp, ← Functor.map_comp]) :=
  rfl

/--
If `F : C ⥤ Cat` and `x : ∫ F`, then every `C`-isomorphism `α : x.base ≅ c` induces
an isomorphism between `x` and its transport along `α`
-/
def transportIso (x : ∫ F) {c : C} (α : x.base ≅ c) :
    x.transport α.hom ≅ x := (isoMk α (CategoryTheory.Iso.refl _)).symm

@[simp]
lemma transportIso_hom_base (x : ∫ F) {c : C} (α : x.base ≅ c) :
    (x.transportIso α).hom.base = α.inv :=
  rfl

@[simp]
lemma transportIso_hom_fiber (x : ∫ F) {c : C} (α : x.base ≅ c) :
    (x.transportIso α).hom.fiber =
    eqToHom (by simp [transportIso, ← Functor.comp_obj, ← Cat.comp_eq_comp]) := by
  simp only [transportIso, CategoryTheory.Iso.symm_hom, isoMk_inv_fiber, CategoryTheory.Iso.refl_inv]
  erw [Functor.map_id]
  simp

@[simp]
lemma transportIso_inv_base (x : ∫ F) {c : C} (α : x.base ≅ c) :
    (x.transportIso α).inv.base = α.hom :=
  rfl

@[simp]
lemma transportIso_inv_fiber (x : ∫ F) {c : C} (α : x.base ≅ c) :
    (x.transportIso α).inv.fiber = 𝟙 ((F.map α.hom).obj x.fiber) :=
  rfl

end Transport

section functorTo
variable (A : D ⥤ C) (fibObj : (x : D) → (A ⋙ F).obj x)
    (fibMap : {x y : D} → (f : x ⟶ y) → ((A ⋙ F).map f).obj (fibObj x) ⟶ fibObj y)

theorem functorTo_map_id_aux (x : D) : ((A ⋙ F).map (𝟙 x)).obj (fibObj x) = fibObj x := by
  simp

theorem functorTo_map_comp_aux {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    ((A ⋙ F).map (f ≫ g)).obj (fibObj x)
    = (F.map (A.map g)).obj (((A ⋙ F).map f).obj (fibObj x)) := by
  simp

section
variable
    (map_id : (x : D) → fibMap (CategoryStruct.id x)
      = eqToHom (functorTo_map_id_aux A fibObj x))
    (map_comp : {x y z : D} → (f : x ⟶ y) → (g : y ⟶ z) → fibMap (f ≫ g)
      = eqToHom (functorTo_map_comp_aux A fibObj f g)
      ≫ (F.map (A.map g)).map (fibMap f) ≫ fibMap g)

/--
Define a functor into `∫ F` by providing a functor into the base cateogry,
as well as the actions on fibers. -/
@[simps!]
def functorTo : D ⥤ ∫ F where
  obj x := mk (A.obj x) (fibObj x)
  map f := Hom.mk (A.map f) (fibMap f)
  map_id x := Hom.ext _ _ (by simp) (by simp [map_id])
  map_comp f g := Hom.ext _ _ (by simp) (by simp [map_comp])

variable {A} {fibObj} {fibMap} {map_id} {map_comp}
@[simp] theorem functorTo_forget :
    functorTo _ _ _ map_id @map_comp ⋙ Grothendieck.forget _ = A :=
  rfl

end

end functorTo

section

variable {G H : C ⥤ Cat.{v₂,u₂}}

/-- The Grothendieck construction is functorial: a natural transformation `α : F ⟶ G` induces
a functor `Grothendieck.map : Grothendieck F ⥤ Grothendieck G`.
-/
@[simps!]
def map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G :=
  functorTo (forget F)
  (fun X => (α.app X.base).obj X.fiber)
  (fun {X Y} f => (eqToHom (α.naturality f.base).symm).app X.fiber ≫ (α.app Y.base).map f.fiber)
  (by intro x; simp)
  (by
    intro x y z f g
    have := Functor.congr_hom (α.naturality g.base).symm f.fiber
    simp at this
    simp [this])

/-- The functor `Grothendieck.map α : ∫ F ⥤ ∫ G` lies over `C`. -/
@[simp]
theorem map_comp_forget {α : F ⟶ G} :
    Grothendieck.map α ⋙ Grothendieck.forget G = Grothendieck.forget F :=
  rfl

theorem map_id_eq : map (𝟙 F) = 𝟙 (Cat.of <| Grothendieck <| F) := by
  apply FunctorTo.hext
  all_goals simp [Cat.id_eq_id, Functor.id_comp]

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `mapIdIso` to `map_id_eq` whenever we can. -/
def mapIdIso : map (𝟙 F) ≅ 𝟙 (Cat.of <| Grothendieck <| F) := eqToIso map_id_eq

theorem map_comp_eq (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  apply FunctorTo.hext
  all_goals simp [Functor.assoc]

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `map_comp_iso` to `map_comp_eq` whenever we can. -/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

end

/-- The Grothendieck construction as a functor from the functor category `E ⥤ Cat` to the
over category `Over E`. -/
def functor {E : Cat.{v, u}} : (E ⥤ Cat.{v,u}) ⥤ Over (T := Cat.{v,u}) E where
  obj F := Over.mk (X := E) (Y := Cat.of (∫ F)) (Grothendieck.forget F)
  map {_ _} α := Over.homMk (X:= E) (Grothendieck.map α) Grothendieck.map_comp_forget
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp [Grothendieck.map_comp_eq α β]
    rfl

section Elements
variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatFunctor : ∫(G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
def grothendieckTypeToCatInverse : G.Elements ⥤ ∫(G ⋙ typeToCat) where
  obj X := mk X.1 ⟨X.2⟩
  map f := Hom.mk f.1 ⟨⟨f.2⟩⟩

@[simp]
lemma grothendieckTypeToCatInverse_obj_base (X : G.Elements) :
    ((grothendieckTypeToCatInverse G).obj X).base = X.1 :=
  rfl

@[simp]
lemma grothendieckTypeToCatInverse_obj_fiber_as (X : G.Elements) :
    ((grothendieckTypeToCatInverse G).obj X).fiber.as = X.2 :=
  rfl

@[simp]
lemma grothendieckTypeToCatInverse_map_base {X Y : G.Elements} (f : X ⟶ Y) :
    ((grothendieckTypeToCatInverse G).map f).base = f.1 :=
  rfl

/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps!]
def grothendieckTypeToCat : ∫(G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact CategoryTheory.Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact CategoryTheory.Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    simp
    rfl

end Elements

section Pseudofunctor

variable (F)

@[simps!]
def toPseudoFunctor'Iso.hom : ∫ F ⥤ F.toPseudoFunctor'.Grothendieck where
  obj x := ⟨ x.base, x.fiber ⟩
  map f := ⟨ f.base, f.fiber ⟩
  map_id x := by apply Pseudofunctor.Grothendieck.Hom.ext <;> simp
  map_comp f g := by apply Pseudofunctor.Grothendieck.Hom.ext <;> simp

@[simps!]
def toPseudoFunctor'Iso.inv : F.toPseudoFunctor'.Grothendieck ⥤ ∫ F where
  obj x := ⟨ x.base, x.fiber ⟩
  map f := ⟨ f.base, f.fiber ⟩
  map_id x := by apply Hom.ext <;> simp
  map_comp f g := by apply Hom.ext <;> simp

def toPseudoFunctor'Iso : ∫ F ≅≅ F.toPseudoFunctor'.Grothendieck where
  hom := toPseudoFunctor'Iso.hom F
  inv := toPseudoFunctor'Iso.inv F

def toPseudoFunctor'Equivalence : ∫ F ≌ F.toPseudoFunctor'.Grothendieck :=
  (toPseudoFunctor'Iso F).toEquivalence

lemma toPseudoFunctor'Iso.hom_comp_forget : toPseudoFunctor'Iso.hom F ⋙
    Pseudofunctor.Grothendieck.forget _ = forget _ :=
  rfl

lemma toPseudoFunctor'Iso.inv_comp_forget : toPseudoFunctor'Iso.inv F ⋙ forget _ =
    Pseudofunctor.Grothendieck.forget _ :=
  rfl

lemma map_eq_pseudofunctor_map {G} (α : F ⟶ G) : map α = (toPseudoFunctor'Iso F).hom ⋙
    Pseudofunctor.Grothendieck.map α.toStrongTrans' ⋙
    (toPseudoFunctor'Iso G).inv := by
  fapply Functor.ext
  · aesop
  · intro _
    aesop

end Pseudofunctor

section

variable {G : D ⥤ C}

/-- Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction induces a functor
`∫(G ⋙ F) ⥤ ∫ F`. -/
@[simps!]
def pre (F) (G : D ⥤ C) : ∫ (G ⋙ F) ⥤ ∫ F :=
  functorTo (forget _ ⋙ G) (fun x => x.fiber) (fun f => f.fiber)
  (Hom.id_fiber) (Hom.comp_fiber)

@[simp]
theorem pre_id : pre F (𝟭 C) = 𝟭 _ := rfl

end

variable (F)

section

variable {G H : D ⥤ C} (α : G ≅ H)
/--
An natural isomorphism between functors `G ≅ H` induces a natural isomorphism between the canonical
morphism `pre F G` and `pre F H`, up to composition with
`∫(G ⋙ F) ⥤ ∫(H ⋙ F)`.
-/
def preNatIso : pre F G ≅ map (whiskerRight α.hom F) ⋙ (pre F H) :=
  NatIso.ofComponents
    (fun X => (transportIso (mk (G.obj X.base) X.fiber) (α.app X.base)).symm)
    (fun {X Y} f => by
      fapply Hom.ext
      · simp
      · simp only [comp_obj, Iso.app_hom, comp_map, Hom.comp_base,
        Hom.comp_fiber, pre_map_fiber,
        eqToHom_trans_assoc, map_map_fiber, whiskerRight_app]
        erw [Category.comp_id, Functor.map_id,
          Functor.congr_hom (F.congr_map (transportIso_inv_base (mk (G.obj Y.base) Y.fiber)
          (α.app Y.base)))]
        simp)

@[simp] theorem preNatIso_hom_app_base (x) :
    ((preNatIso F α).hom.app x).base = α.hom.app x.base := by
  simp [preNatIso]

@[simp] theorem preNatIso_hom_app_fiber (x) :
    ((preNatIso F α).hom.app x).fiber = 𝟙 _ := by
  simp [preNatIso]

theorem preNatIso_congr {G H : D ⥤ C} {α β : G ≅ H} (h : α = β) :
    preNatIso F α = preNatIso F β ≪≫ eqToIso (by subst h; simp) := by
  subst h
  simp

@[simp] theorem preNatIso_eqToIso {G H : D ⥤ C} {h : G = H} :
    preNatIso F (eqToIso h) =
    eqToIso (by subst h; simp [map_id_eq, Cat.id_eq_id, Functor.id_comp]) := by
  subst h
  ext
  fapply Hom.ext
  · simp
  · simp only [eqToIso_refl, comp_obj, eqToIso.hom, preNatIso_hom_app_fiber,
      Category.comp_id]
    rw! [eqToHom_app, fiber_eqToHom]

theorem preNatIso_comp {G1 G2 G3 : D ⥤ C} (α : G1 ≅ G2) (β : G2 ≅ G3) :
    preNatIso F (α ≪≫ β) = preNatIso F α ≪≫ isoWhiskerLeft _ (preNatIso F β) ≪≫
    eqToIso (by simp [map_comp_eq, Functor.assoc]) := by
  ext
  fapply Hom.ext
  · simp
  · simp only [CategoryTheory.Iso.trans_hom, eqToIso.hom, NatTrans.comp_app]
    rw! [eqToHom_app]
    simp

end

/--
Given an equivalence of categories `G`, `preInv _ G` is the (weak) inverse of the `pre _ G.functor`.
-/
def preInv (G : D ≌ C) : ∫ F ⥤ ∫(G.functor ⋙ F) :=
  map (whiskerRight G.counitInv F) ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse

lemma pre_comp_map (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) :
    pre F G ⋙ map α = map (whiskerLeft G α) ⋙ pre H G := rfl

lemma pre_comp_forget (G : D ⥤ C) : pre F G ⋙ forget _ = forget _ ⋙ G :=
  rfl

variable {F} in
lemma pre_comp_map_assoc (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : Type*} [Category E]
    (K : ∫ H ⥤ E) : pre F G ⋙ map α ⋙ K= map (whiskerLeft G α) ⋙ pre H G ⋙ K := rfl

variable {E : Type*} [Category E] in
@[simp]
lemma pre_comp (G : D ⥤ C) (H : E ⥤ D) : pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G := rfl

/--
Let `G` be an equivalence of categories. The functor induced via `pre` by `G.functor ⋙ G.inverse`
is naturally isomorphic to the functor induced via `map` by a whiskered version of `G`'s inverse
unit.
-/
protected def preUnitIso (G : D ≌ C) :
    map (whiskerRight G.unitInv _) ≅ pre (G.functor ⋙ F) (G.functor ⋙ G.inverse) :=
  preNatIso _ G.unitIso.symm |>.symm

/--
Given a functor `F : C ⥤ Cat` and an equivalence of categories `G : D ≌ C`, the functor
`pre F G.functor` is an equivalence between `∫ (G.functor ⋙ F)` and `∫ F`.
-/
def preEquivalence (G : D ≌ C) : ∫ (G.functor ⋙ F) ≌ ∫ F where
  functor := pre F G.functor
  inverse := preInv F G
  unitIso := by
    refine (eqToIso ?_)
      ≪≫ (Grothendieck.preUnitIso F G |> isoWhiskerLeft (map _))
      ≪≫ (pre_comp_map_assoc G.functor _ _ |> Eq.symm |> eqToIso)
    calc
      _ = map (𝟙 _) := map_id_eq.symm
      _ = map _ := ?_
      _ = map _ ⋙ map _ := map_comp_eq _ _
    congr; ext X
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, Functor.id_obj,
      Functor.map_id, NatTrans.comp_app, NatTrans.id_app, whiskerLeft_app, whiskerRight_app,
      Equivalence.counitInv_functor_comp]
  counitIso := preNatIso F G.counitIso.symm |>.symm
  functor_unitIso_comp X := by
    simp only [preInv, Grothendieck.preUnitIso, pre_id, CategoryTheory.Iso.trans_hom,
      eqToIso.hom, eqToHom_app, eqToHom_refl, isoWhiskerLeft_hom, NatTrans.comp_app]
    fapply Hom.ext <;> simp [preNatIso, transportIso]

variable {F} in
/--
Let `F, F' : C ⥤ Cat` be functor, `G : D ≌ C` an equivalence and `α : F ⟶ F'` a natural

transformation.

Left-whiskering `α` by `G` and then taking the Grothendieck construction is, up to isomorphism,
the same as taking the Grothendieck construction of `α` and using the equivalences `pre F G`
and `pre F' G` to match the expected type:

```
∫(G.functor ⋙ F) ≌ ∫ F ⥤ ∫ F' ≌ ∫(G.functor ⋙ F')
```
-/
def mapWhiskerLeftIsoConjPreMap {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F') :
    map (whiskerLeft G.functor α) ≅
      (preEquivalence F G).functor ⋙ map α ⋙ (preEquivalence F' G).inverse :=
  (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (preEquivalence F' G).unitIso

section FunctorFrom

variable {E : Type*} [Category E] (c : C)

/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its Grothendieck
construction. -/
@[simps!]
def ι : F.obj c ⥤ ∫ F :=
  functorTo ((const (F.obj c)).obj c) id (fun f => eqToHom (by simp) ≫ f) (by simp)
  (by simp [Functor.congr_hom (F.map_id _)])

instance faithful_ι (c : C) : (ι F c).Faithful where
  map_injective f := by
    injection f with _ f
    rwa [cancel_epi] at f

theorem ι_comp_forget : ι F c ⋙ forget _ = (const (F.obj c)).obj c :=
  rfl

@[simp] theorem ι_comp_pre (G : D ⥤ C) (x : D)
    : ι (G ⋙ F) x ⋙ pre F G = ι F (G.obj x) := by
  apply Grothendieck.FunctorTo.hext
  · rw [ι_comp_forget, Functor.assoc, pre_comp_forget, ← Functor.assoc, ι_comp_forget]
    apply Functor.ext <;> simp
  · simp
  · simp

variable {F}

section ιNatTrans

variable {X Y : C} (f : X ⟶ Y)

/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
@[simps!]
def ιNatTrans : ι F X ⟶ F.map f ⋙ ι F Y where
  app _ := Hom.mk f (𝟙 _)
  naturality _ _ _ := Hom.ext _ _ (by simp) (by simp [eqToHom_map])

@[simp]
theorem ιNatTrans_id_app {X : C} {a : F.obj X} :
    (@ιNatTrans _ _ F _ _ (𝟙 X)).app a = eqToHom (by simp) :=
  Hom.ext _ _ (by simp) (by simp)

lemma ιNatTrans_comp_app {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {a} :
    (@ιNatTrans _ _ F _ _ (f ≫ g)).app a =
    (@ιNatTrans _ _ F _ _ f).app a ≫
    (@ιNatTrans _ _ F _ _ g).app ((F.map f).obj a) ≫ eqToHom (by simp) :=
  Hom.ext _ _ (by simp) (by simp)

end ιNatTrans

theorem cast_eq {F G : C ⥤ Cat}
    (h : F = G) (p : Grothendieck F) :
    (cast (by subst h; rfl) p : Grothendieck G)
    = ⟨ p.base , cast (by subst h; rfl) p.fiber ⟩ := by
  subst h
  rfl

section

variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ F.map f ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f) (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

/-- Construct a functor from `∫ F` to another category `E` by providing a family of
functors on the fibers of `∫ F`, a family of natural transformations on morphisms in the
base of `∫ F` and coherence data for this family of natural transformations. -/
@[simps]
def functorFrom : ∫ F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

theorem map_eqToHom_base_pf {G1 G2 : Grothendieck F} (eq : G1 = G2) :
    F.obj G1.base = F.obj G2.base := by subst eq; rfl

theorem map_eqToHom_base {G1 G2 : Grothendieck F} (eq : G1 = G2)
    : F.map (eqToHom eq).base = eqToHom (map_eqToHom_base_pf eq) := by
  simp [eqToHom_map]

theorem map_eqToHom_obj_base {F G : C ⥤ Cat.{v,u}} (h : F = G)
  (x) : ((Grothendieck.map (eqToHom h)).obj x).base = x.base := rfl

theorem map_forget {F G : C ⥤ Cat.{v,u}} (α : F ⟶ G) :
    Grothendieck.map α ⋙ Grothendieck.forget G =
    Grothendieck.forget F :=
  rfl

variable (K : Grothendieck F ⥤ E)

abbrev asFunctorFromFib (c : C) : (F.obj c) ⥤ E := ι F c ⋙ K

abbrev asFunctorFromHom {c c' : C} (f: c ⟶ c') :
    asFunctorFromFib K c ⟶ F.map f ⋙ asFunctorFromFib K c' :=
  Functor.whiskerRight (ιNatTrans f) K

lemma asFunctorFromHom_app {c c' : C} (f: c ⟶ c') (p : F.obj c) :
    (asFunctorFromHom K f).app p = K.map ((ιNatTrans f).app p) :=
  rfl

lemma asFunctorFromHom_id (c : C) : asFunctorFromHom K (𝟙 c) =
    eqToHom (by simp only [Functor.map_id,Cat.id_eq_id,Functor.id_comp]) := by
  ext p
  simp [eqToHom_map, ιNatTrans_id_app]

lemma asFunctorFromHom_comp (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g: c₂ ⟶ c₃) :
    asFunctorFromHom K (f ≫ g) =
    asFunctorFromHom K f ≫ Functor.whiskerLeft (F.map f) (asFunctorFromHom K g) ≫ eqToHom
    (by simp[← Functor.assoc]; congr) := by
  ext p
  simp [asFunctorFromHom, eqToHom_map, ιNatTrans_comp_app]

theorem asFunctorFrom : Grothendieck.functorFrom (asFunctorFromFib K) (asFunctorFromHom K)
    (asFunctorFromHom_id K) (asFunctorFromHom_comp K) = K := by
  fapply CategoryTheory.Functor.ext
  · intro X
    rfl
  · intro x y f
    simp only [functorFrom_obj, asFunctorFromFib, Functor.comp_obj, functorFrom_map,
      asFunctorFromHom, Functor.whiskerRight_app, Functor.comp_map, ← Functor.map_comp,
      eqToHom_refl, Category.comp_id, Category.id_comp]
    congr
    fapply Hom.ext
    · simp
    · simp

section

variable {D : Type*} [Category D] (G : E ⥤ D)

def functorFromCompFib (c : C) : F.obj c ⥤ D := fib c ⋙ G

def functorFromCompHom {c c' : C} (f : c ⟶ c') :
    functorFromCompFib fib G c ⟶ F.map f ⋙ functorFromCompFib fib G c' :=
  Functor.whiskerRight (hom f) G

include hom_id in
lemma functorFromCompHom_id (c : C) : functorFromCompHom fib hom G (𝟙 c)
    = eqToHom (by simp [Cat.id_eq_id, Functor.id_comp]) := by
  ext x
  simp [hom_id, functorFromCompHom]

include hom_comp in
lemma functorFromCompHom_comp (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃):
    functorFromCompHom fib hom G (f ≫ g)
    = functorFromCompHom fib hom G f ≫
    Functor.whiskerLeft (F.map f) (functorFromCompHom fib hom G g) ≫
    eqToHom (by simp[Cat.comp_eq_comp, Functor.map_comp, Functor.assoc]) := by
  ext
  simp [functorFromCompHom, hom_comp]

theorem functorFrom_comp : functorFrom fib hom hom_id hom_comp ⋙ G =
    functorFrom (functorFromCompFib fib G) (functorFromCompHom fib hom G)
  (functorFromCompHom_id fib hom hom_id G)
  (functorFromCompHom_comp fib hom hom_comp G) := by
  fapply CategoryTheory.Functor.ext
  · intro X
    simp [functorFromCompFib]
  · intro x y f
    simp [functorFromCompHom, functorFromCompFib]

end

section
variable (fib' : ∀ c, F.obj c ⥤ E) (hom' : ∀ {c c' : C} (f : c ⟶ c'), fib' c ⟶ F.map f ⋙ fib' c')
variable (hom_id' : ∀ c, hom' (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp' : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom' (f ≫ g) =
  hom' f ≫ Functor.whiskerLeft (F.map f) (hom' g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

theorem functorFrom_eq_of (ef : fib = fib')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), hom f ≫ eqToHom (by rw[ef]) = eqToHom (by rw[ef]) ≫ hom' f) :
    functorFrom fib hom hom_id hom_comp = functorFrom fib' hom' hom_id' hom_comp' := by
  subst ef
  congr!
  · aesop_cat

theorem functorFrom_ext {K K' : Grothendieck F ⥤ E}
    (hfib : ∀ c, ι F c ⋙ K = ι F c ⋙ K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), Functor.whiskerRight (ιNatTrans f) K ≫
      eqToHom (by simp [Functor.assoc, hfib])
      = eqToHom (by rw[hfib]) ≫ Functor.whiskerRight (ιNatTrans f) K') :
    K = K' :=
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

theorem functorFrom_hext {K K' : Grothendieck F ⥤ E}
    (hfib : ∀ c, ι F c ⋙ K = ι F c ⋙ K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), Functor.whiskerRight (ιNatTrans f) K ≍
      Functor.whiskerRight (ιNatTrans f) K')
    : K = K' := by
  fapply functorFrom_ext
  · assumption
  · intros
    apply eq_of_heq
    simp only [heq_eqToHom_comp_iff, comp_eqToHom_heq_iff]
    apply hhom

end

/-- `Grothendieck.ι F c` composed with `Grothendieck.functorFrom` is isomorphic a functor on a fiber
on `F` supplied as the first argument to `Grothendieck.functorFrom`. -/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  NatIso.ofComponents (fun _ => CategoryTheory.Iso.refl _) (fun f => by simp [hom_id])

@[simp]
lemma ι_comp_functorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) = fib c :=
  Functor.ext_of_iso (ιCompFunctorFrom fib hom hom_id hom_comp c) (by intro; rfl)

lemma whiskerRight_ιNatTrans_functorFrom {x y} (f : x ⟶ y) :
    Functor.whiskerRight (ιNatTrans f) (functorFrom fib hom hom_id hom_comp) =
    eqToHom (ι_comp_functorFrom ..) ≫ hom f ≫
    eqToHom (by rw [Functor.assoc, ι_comp_functorFrom]) := by
  ext; simp

section
variable (A : E ⥤ C) (fibObj : (x : E) → (A ⋙ F).obj x)
    (fibMap : {x y : E} → (f : x ⟶ y) → ((A ⋙ F).map f).obj (fibObj x) ⟶ fibObj y)
    (map_id : (x : E) → fibMap (CategoryStruct.id x)
      = eqToHom (functorTo_map_id_aux A fibObj x))
    (map_comp : {x y z : E} → (f : x ⟶ y) → (g : y ⟶ z) → fibMap (f ≫ g)
      = eqToHom (functorTo_map_comp_aux A fibObj f g)
      ≫ (F.map (A.map g)).map (fibMap f) ≫ fibMap g)

@[simps!]
def functorIsoFrom (fib_comp : ∀ c, fib c ⋙ A = ι F c ⋙ forget F)
    (fibObj_fib_obj : ∀ c x, fibObj ((fib c).obj x) ≍ x)
    (fibMap_fib_map : ∀ c {x y} (f : x ⟶ y), fibMap ((fib c).map f) ≍ f)
    (fib_obj_fibObj : ∀ x, (fib (A.obj x)).obj (fibObj x) = x)
    (hom_map_app_fibObj : ∀ {x y} (f : x ⟶ y), (hom (A.map f)).app (fibObj x) ≫
      (fib (A.obj y)).map (fibMap f) ≍ f)
    (obj_fib_obj : ∀ c x, A.obj ((fib c).obj x) = c)
    (map_hom_app : ∀ {c c'} (f : c ⟶ c') x, A.map ((hom f).app x) ≍ f)
    (fibMap_hom_app : ∀ {c c'} (f : c ⟶ c') x, fibMap ((hom f).app x) ≍ 𝟙 ((F.map f).obj x)) :
    ∫ F ≅≅ E where
  hom := functorFrom fib hom hom_id hom_comp
  inv := functorTo A fibObj fibMap map_id map_comp
  hom_inv_id := by
    fapply functorFrom_ext
    · intro c
      rw [← Functor.assoc, ι_comp_functorFrom]
      apply FunctorTo.hext
      · simp only [Functor.assoc, functorTo_forget, Functor.id_comp, fib_comp]
      · apply fibObj_fib_obj
      · intro x y f
        simp only [comp_obj, functorTo_obj_base, comp_map, functorTo_map_base, functorTo_obj_fiber,
          functorTo_map_fiber, id_obj, ι_obj_base, id_map, ι_map_base, ι_obj_fiber, ι_map_fiber]
        rw! [eqToHom_comp_heq, heq_cast_iff_heq]
        apply fibMap_fib_map
    · intro c c' f
      apply NatTrans.ext
      ext x
      simp only [comp_obj, functorFrom_obj, ι_obj_base, ι_obj_fiber, id_obj, comp_whiskerRight,
        whiskerRight_ιNatTrans_functorFrom, whiskerRight_comp, eqToHom_whiskerRight, Category.assoc,
        eqToHom_trans, NatTrans.comp_app, eqToHom_app, eqToHom_refl, whiskerRight_app,
        Category.id_comp, id_whiskerRight, ← heq_eq_eq, heq_eqToHom_comp_iff, comp_eqToHom_heq_iff]
      apply Grothendieck.Hom.hext' rfl
      any_goals apply Grothendieck.hext' rfl
      all_goals simp [obj_fib_obj, fibObj_fib_obj, fibMap_hom_app, map_hom_app]
  inv_hom_id := by
    fapply Functor.ext
    · intro x
      simp [fib_obj_fibObj]
    · intro x y f
      simp [← heq_eq_eq, hom_map_app_fibObj]

end
end

end FunctorFrom

/-- The fiber inclusion `ι F c` composed with `map α` is isomorphic to `α.app c ⋙ ι F' c`. -/
@[simps!]
def ιCompMap {F' : C ⥤ Cat} (α : F ⟶ F') (c : C) : ι F c ⋙ map α ≅ α.app c ⋙ ι F' c :=
  NatIso.ofComponents (fun X => CategoryTheory.Iso.refl _) (fun f => by
    simp only [CategoryTheory.Iso.refl_hom, Category.comp_id]
    apply Hom.ext <;> simp)

lemma ι_comp_map {F' : C ⥤ Cat} (α : F ⟶ F') (c : C) : ι F c ⋙ map α = α.app c ⋙ ι F' c :=
  Functor.ext_of_iso (ιCompMap ..) (by intro; rfl)

section AsSmall

attribute [-simp] AsSmall.down_obj AsSmall.down_map

/-- The inverse functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simp] def compAsSmallFunctorEquivalenceInverse :
    ∫ F ⥤ ∫(F ⋙ Cat.asSmallFunctor.{w}) :=
  functorTo (forget _) (fun X => (AsSmall.up.obj X.fiber)) (fun f => (AsSmall.up.map f.fiber))
  (by simp) (by intros; simp)

/-- The functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simp] def compAsSmallFunctorEquivalenceFunctor :
    ∫(F ⋙ Cat.asSmallFunctor.{w}) ⥤ ∫ F :=
  functorTo (forget _) (fun X => (AsSmall.down.obj X.fiber)) (fun f => (AsSmall.down.map f.fiber))
  (by intros; simp; apply eqToHom_map) -- FIXME: eqToHom_map does not fire under simp
  (by
    intros
    simp [Functor.map_comp])
  -- FIXME: these AsSmall goals are awful. Need to add some evil lemmas for AsSmall.up, AsSmall.down

/-- Taking the Grothendieck construction on `F ⋙ asSmallFunctor`, where
`asSmallFunctor : Cat ⥤ Cat` is the functor which turns each category into a small category of a
(potentiall) larger universe, is equivalent to the Grothendieck construction on `F` itself. -/
@[simps]
def compAsSmallFunctorEquivalence :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ≌ ∫ F where
  functor := compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := CategoryTheory.Iso.refl _
  unitIso := CategoryTheory.Iso.refl _

namespace AsSmall

@[simp] theorem up_map_down_map
    {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) :
  AsSmall.down.map (AsSmall.up.map f) = f := rfl

@[simp] theorem down_map_up_map
    {C : Type u₁} [Category.{v₁, u₁} C]
    {X Y : AsSmall C} (f : X ⟶ Y) :
  AsSmall.up.map (AsSmall.down.map f) = f := rfl

theorem comp_up_inj {C : Type u} [Category.{v} C]
  {D : Type u₁} [Category.{v₁} D] {F G : C ⥤ D}
    (h : F ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D) = G ⋙ AsSmall.up) : F = G := by
  convert_to F ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D)
    ⋙ AsSmall.down
    = G ⋙ (AsSmall.up : D ⥤ AsSmall.{w} D)
    ⋙ AsSmall.down
  rw [← Functor.assoc, h, Functor.assoc]

theorem comp_down_inj {C : Type u} [Category.{v} C]
  {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ AsSmall.{w} D}
    (h : F ⋙ AsSmall.down = G ⋙ AsSmall.down)
    : F = G := by
  convert_to F ⋙ AsSmall.down
    ⋙ AsSmall.up
    = G ⋙ AsSmall.down ⋙ AsSmall.up
  rw [← Functor.assoc, h, Functor.assoc]

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

variable {F G} in
/-- Mapping a Grothendieck construction along the whiskering of any natural transformation
`α : F ⟶ G` with the functor `asSmallFunctor : Cat ⥤ Cat` is naturally isomorphic to conjugating
`map α` with the equivalence between `Grothendieck (F ⋙ asSmallFunctor)` and `∫ F`. -/
def mapWhiskerRightAsSmallFunctor (α : F ⟶ G) :
    map (whiskerRight α Cat.asSmallFunctor.{w}) ≅
    (compAsSmallFunctorEquivalence F).functor ⋙ map α ⋙
      (compAsSmallFunctorEquivalence G).inverse :=
  NatIso.ofComponents
    (fun X => CategoryTheory.Iso.refl _)
    (fun f => by
      simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalenceFunctor,
        comp_obj, forget_obj, comp_map, forget_map, compAsSmallFunctorEquivalence_inverse,
        compAsSmallFunctorEquivalenceInverse, CategoryTheory.Iso.refl_hom, Category.comp_id,
        Category.id_comp]
      apply Hom.ext <;> simp
      )

end AsSmall

noncomputable section

variable {F} {x y : ∫ F} (f : x ⟶ y) [IsIso f]

instance : IsIso f.base := by
  refine ⟨ (CategoryTheory.inv f).base , ?_, ?_ ⟩
  · simp [← Grothendieck.Hom.comp_base]
  · simp [← Grothendieck.Hom.comp_base]

def invFiber : y.fiber ⟶ (F.map f.base).obj x.fiber :=
  eqToHom (by simp [← Functor.comp_obj, ← Cat.comp_eq_comp, ← Functor.map_comp,
      ← Grothendieck.Hom.comp_base]) ≫
    (F.map f.base).map (CategoryTheory.inv f).fiber

@[simp]
lemma fiber_comp_invFiber : f.fiber ≫ invFiber f = 𝟙 ((F.map f.base).obj x.fiber) := by
  have h := Functor.Grothendieck.Hom.comp_fiber f (CategoryTheory.inv f)
  rw! [IsIso.hom_inv_id] at h
  have h0 : F.map (CategoryTheory.inv f).base ⋙ F.map f.base = 𝟭 _ := by
    simp [← Cat.comp_eq_comp, ← Functor.map_comp, ← Grothendieck.Hom.comp_base, Cat.id_eq_id]
  have h1 := Functor.congr_map (F.map f.base) h
  simp [← heq_eq_eq, eqToHom_map, ← Functor.comp_map, Functor.congr_hom h0] at h1
  dsimp [invFiber]
  rw! [← h1]
  simp

@[simp]
lemma invFiber_comp_fiber : invFiber f ≫ f.fiber = 𝟙 _ := by
  have h := Functor.Grothendieck.Hom.comp_fiber (CategoryTheory.inv f) f
  rw! [IsIso.inv_hom_id] at h
  simp [invFiber]
  convert h.symm
  · simp
  · simp
  · simpa using (eqToHom_heq_id_cod _ _ _).symm

instance : IsIso f.fiber :=
  ⟨invFiber f , fiber_comp_invFiber f, invFiber_comp_fiber f⟩

lemma inv_base : CategoryTheory.inv f.base = Grothendieck.Hom.base (CategoryTheory.inv f) := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← Hom.comp_base]

lemma inv_fiber : CategoryTheory.inv f.fiber = invFiber f := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp

end

end Grothendieck

end Functor

end CategoryTheory
