/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import SEq.Tactic.DepRewrite

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

open Functor Category Opposite Discrete Bicategory StrongTrans

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

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
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

section

variable {a b : ∫ F}

@[ext (iff := false)]
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : f.fiber = eqToHom (hfg₁ ▸ rfl) ≫ g.fiber) : f = g := by
  cases f; cases g
  dsimp at hfg₁ hfg₂
  rw! [hfg₂, hfg₁]
  simp

lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ ∃ (hfg : f.base = g.base), f.fiber = eqToHom (hfg ▸ rfl) ≫ g.fiber where
  mp hfg := by subst hfg; simp
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

lemma Hom.congr {a b : ∫ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = eqToHom (h ▸ rfl) ≫ g.fiber := by
  subst h
  simp

end

section

variable {B : Type u₁} [Bicategory B]
variable (F : Pseudofunctor B Cat) {a b : B}

lemma mapComp_assoc_right_hom_app_assoc {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (X : ↑(F.obj a)) {Z : ↑(F.obj d)} (η : (F.map f ≫ F.map g ≫ F.map h).obj X ⟶ Z) :
    (F.mapComp f (g ≫ h)).hom.app X ≫ (F.mapComp g h).hom.app ((F.map f).obj X) ≫ η =
    (F.map₂ (α_ f g h).inv).app X ≫ (F.mapComp (f ≫ g) h).hom.app X ≫
    (F.map h).map ((F.mapComp f g).hom.app X) ≫ (α_ (F.map f) (F.map g) (F.map h)).hom.app X ≫ η :=
  sorry

end

/-- The category structure on `∫ F`. -/
instance category : Category (∫ F) where
  toCategoryStruct := Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_hom_app, Strict.rightUnitor_eqToIso]
  assoc f g h := by
    ext
    · simp
    · simp [mapComp_assoc_right_hom_app_assoc, Strict.associator_eqToIso]
      -- rw [F.mapComp_assoc_right_hom_app_assoc] after Mathlib change

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
    fiber := sorry
      -- (α.app ⟨a.base⟩).map f.2 ≫ (α.naturality f.1.toLoc).hom.app b.fiber
      }
  map_id a := by
    ext1
    · dsimp
    · sorry
      -- simp [StrongTrans.naturality_id_hom_app, ← Functor.map_comp_assoc]
  map_comp {a b c} f g := by
    ext
    · dsimp
    · dsimp
      sorry
      -- rw [StrongTrans.naturality_comp_hom_app]
      -- simp only [map_comp, Cat.comp_obj, Strict.associator_eqToIso,
      --   eqToIso_refl, Iso.refl_hom, Cat.id_app, Iso.refl_inv, id_comp, assoc, comp_id]
      -- slice_lhs 2 4 => simp only [← Functor.map_comp, Iso.inv_hom_id_app, Cat.comp_obj, comp_id]
      -- simp [← Functor.comp_map]

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

end Pseudofunctor.Grothendieck

end CategoryTheory

#exit

/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic

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
`Cat` is treated as a strict 2-category and `F` a pseudofunctor.
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
This is implemented as the Grothendieck construction on `F` viewed as a pseudofunctor.
-/
def Grothendieck := Pseudofunctor.Grothendieck
  (F.toPseudoFunctor' : Pseudofunctor (LocallyDiscrete (Cᵒᵖ)ᵒᵖ ) Cat)


end Functor

open Functor

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

namespace Grothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber

@[ext (iff := false)]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  aesop_cat

/-- The identity morphism in the Grothendieck category.
-/
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by simp)

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by simp) ≫ (F.map g.base).map f.fiber ≫ g.fiber

attribute [local simp] eqToHom_map

instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp f g := Grothendieck.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_id Y.base)) f.fiber]
      simp
  id_comp f := by ext <;> simp [comp, id]
  assoc f g h := by
    ext
    · simp [comp]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) f.fiber]
      simp

@[simp]
theorem id_base (X : Grothendieck F) :
    Hom.base (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
theorem id_fiber (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by simp) :=
  rfl

@[simp]
theorem comp_base {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_fiber {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) =
      eqToHom (by simp) ≫ (F.map g.base).map f.fiber ≫ g.fiber :=
  rfl

theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  simp

@[simp]
theorem base_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Grothendieck.base h) := by subst h; rfl

@[simp]
theorem fiber_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; simp) := by subst h; rfl

lemma eqToHom_eq {X Y : Grothendieck F} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) } := by
  subst hF
  rfl

section Transport

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element of `Grothendieck F` to a `d`-based element.
-/
@[simps]
def transport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : Grothendieck F :=
  ⟨c, (F.map t).obj x.fiber⟩

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element `x` of `Grothendieck F` to a `d`-based element `x.transport t`.

`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identity on fibers.
-/
@[simps]
def toTransport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : x ⟶ x.transport t :=
  ⟨t, 𝟙 _⟩

/--
Construct an isomorphism in a Grothendieck construction from isomorphisms in its base and fiber.
-/
@[simps]
def isoMk {X Y : Grothendieck F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).obj X.fiber ≅ Y.fiber) :
    X ≅ Y where
  hom := ⟨e₁.hom, e₂.hom⟩
  inv := ⟨e₁.inv, (F.map e₁.inv).map e₂.inv ≫
    eqToHom (Functor.congr_obj (F.mapIso e₁).hom_inv_id X.fiber)⟩
  hom_inv_id := Grothendieck.ext _ _ (by simp) (by simp)
  inv_hom_id := Grothendieck.ext _ _ (by simp) (by
    have := Functor.congr_hom (F.mapIso e₁).inv_hom_id e₂.inv
    dsimp at this
    simp [this])

/--
If `F : C ⥤ Cat` and `x : Grothendieck F`, then every `C`-isomorphism `α : x.base ≅ c` induces
an isomorphism between `x` and its transport along `α`
-/
@[simps!]
def transportIso (x : Grothendieck F) {c : C} (α : x.base ≅ c) :
    x.transport α.hom ≅ x := (isoMk α (Iso.refl _)).symm

end Transport
section

variable (F)

/-- The forgetful functor from `Grothendieck F` to the source category. -/
@[simps!]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map f := f.1

end

section

variable {G : C ⥤ Cat}

/-- The Grothendieck construction is functorial: a natural transformation `α : F ⟶ G` induces
a functor `Grothendieck.map : Grothendieck F ⥤ Grothendieck G`.
-/
@[simps!]
def map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where
  obj X :=
  { base := X.base
    fiber := (α.app X.base).obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).app X.fiber ≫ (α.app Y.base).map f.fiber }
  map_id X := by simp only [Cat.eqToHom_app, id_fiber, eqToHom_map, eqToHom_trans]; rfl
  map_comp {X Y Z} f g := by
    dsimp
    congr 1
    simp only [← Category.assoc, Functor.map_comp, eqToHom_map]
    congr 1
    simp only [Cat.eqToHom_app, Cat.comp_obj, eqToHom_trans, eqToHom_map, Category.assoc,
      ← Cat.comp_map]
    rw [Functor.congr_hom (α.naturality g.base).symm f.fiber]
    simp

theorem map_obj {α : F ⟶ G} (X : Grothendieck F) :
    (Grothendieck.map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl

theorem map_map {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y} :
    (Grothendieck.map α).map f =
    ⟨f.base, (eqToHom (α.naturality f.base).symm).app X.fiber ≫ (α.app Y.base).map f.fiber⟩ := rfl

/-- The functor `Grothendieck.map α : Grothendieck F ⥤ Grothendieck G` lies over `C`. -/
theorem functor_comp_forget {α : F ⟶ G} :
    Grothendieck.map α ⋙ Grothendieck.forget G = Grothendieck.forget F := rfl

theorem map_id_eq : map (𝟙 F) = 𝟙 (Cat.of <| Grothendieck <| F) := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `mapIdIso` to `map_id_eq` whenever we can. -/
def mapIdIso : map (𝟙 F) ≅ 𝟙 (Cat.of <| Grothendieck <| F) := eqToIso map_id_eq

variable {H : C ⥤ Cat}

theorem map_comp_eq (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, NatTrans.comp_app, Cat.comp_obj, Cat.comp_map,
      eqToHom_refl, Functor.comp_map, Functor.map_comp, Category.comp_id, Category.id_comp]
    fapply Grothendieck.ext
    · rfl
    · simp

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `map_comp_iso` to `map_comp_eq` whenever we can. -/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

variable (F)

/-- The inverse functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
def compAsSmallFunctorEquivalenceInverse :
    Grothendieck F ⥤ Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) where
  obj X := ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩

/-- The functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
def compAsSmallFunctorEquivalenceFunctor :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ⥤ Grothendieck F where
  obj X := ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id _ := by apply Grothendieck.ext <;> simp
  map_comp _ _ := by apply Grothendieck.ext <;> simp [down_comp]

/-- Taking the Grothendieck construction on `F ⋙ asSmallFunctor`, where
`asSmallFunctor : Cat ⥤ Cat` is the functor which turns each category into a small category of a
(potentiall) larger universe, is equivalent to the Grothendieck construction on `F` itself. -/
@[simps]
def compAsSmallFunctorEquivalence :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ≌ Grothendieck F where
  functor := compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := Iso.refl _
  unitIso := Iso.refl _

variable {F} in
/-- Mapping a Grothendieck construction along the whiskering of any natural transformation
`α : F ⟶ G` with the functor `asSmallFunctor : Cat ⥤ Cat` is naturally isomorphic to conjugating
`map α` with the equivalence between `Grothendieck (F ⋙ asSmallFunctor)` and `Grothendieck F`. -/
def mapWhiskerRightAsSmallFunctor (α : F ⟶ G) :
    map (whiskerRight α Cat.asSmallFunctor.{w}) ≅
    (compAsSmallFunctorEquivalence F).functor ⋙ map α ⋙
      (compAsSmallFunctorEquivalence G).inverse :=
  NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun f => by
      fapply Grothendieck.ext
      · simp [compAsSmallFunctorEquivalenceInverse]
      · simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse,
          Functor.comp_obj, compAsSmallFunctorEquivalenceInverse_obj_base, map_obj_base,
          compAsSmallFunctorEquivalenceFunctor_obj_base, Cat.asSmallFunctor_obj, Cat.of_α,
          Iso.refl_hom, Functor.comp_map, comp_base, id_base,
          compAsSmallFunctorEquivalenceInverse_map_base, map_map_base,
          compAsSmallFunctorEquivalenceFunctor_map_base, Cat.asSmallFunctor_map, map_obj_fiber,
          whiskerRight_app, AsSmall.down_obj, AsSmall.up_obj_down,
          compAsSmallFunctorEquivalenceInverse_obj_fiber,
          compAsSmallFunctorEquivalenceFunctor_obj_fiber, comp_fiber, map_map_fiber,
          AsSmall.down_map, down_comp, eqToHom_down, AsSmall.up_map_down, Functor.map_comp,
          eqToHom_map, id_fiber, Category.assoc, eqToHom_trans_assoc,
          compAsSmallFunctorEquivalenceInverse_map_fiber,
          compAsSmallFunctorEquivalenceFunctor_map_fiber, eqToHom_comp_iff, comp_eqToHom_iff]
        simp only [conj_eqToHom_iff_heq']
        rw [G.map_id]
        simp )

end

/-- The Grothendieck construction as a functor from the functor category `E ⥤ Cat` to the
over category `Over E`. -/
def functor {E : Cat.{v, u}} : (E ⥤ Cat.{v,u}) ⥤ Over (T := Cat.{v,u}) E where
  obj F := Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F)
  map {_ _} α := Over.homMk (X:= E) (Grothendieck.map α) Grothendieck.functor_comp_forget
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp [Grothendieck.map_comp_eq α β]
    rfl

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩

/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps!]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    simp
    rfl

section Pre

variable (F)

/-- Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction induces a functor
`Grothendieck (G ⋙ F) ⥤ Grothendieck F`. -/
@[simps]
def pre (G : D ⥤ C) : Grothendieck (G ⋙ F) ⥤ Grothendieck F where
  obj X := ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

@[simp]
theorem pre_id : pre F (𝟭 C) = 𝟭 _ := rfl

/--
An natural isomorphism between functors `G ≅ H` induces a natural isomorphism between the canonical
morphism `pre F G` and `pre F H`, up to composition with
`Grothendieck (G ⋙ F) ⥤ Grothendieck (H ⋙ F)`.
-/
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F G ≅ map (whiskerRight α.hom F) ⋙ (pre F H) :=
  NatIso.ofComponents
    (fun X => (transportIso ⟨G.obj X.base, X.fiber⟩ (α.app X.base)).symm)
    (fun f => by fapply Grothendieck.ext <;> simp)

/--
Given an equivalence of categories `G`, `preInv _ G` is the (weak) inverse of the `pre _ G.functor`.
-/
def preInv (G : D ≌ C) : Grothendieck F ⥤ Grothendieck (G.functor ⋙ F) :=
  map (whiskerRight G.counitInv F) ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse

variable {F} in
lemma pre_comp_map (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) :
    pre F G ⋙ map α = map (whiskerLeft G α) ⋙ pre H G := rfl

variable {F} in
lemma pre_comp_map_assoc (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : Type*} [Category E]
    (K : Grothendieck H ⥤ E) : pre F G ⋙ map α ⋙ K= map (whiskerLeft G α) ⋙ pre H G ⋙ K := rfl

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
`pre F G.functor` is an equivalence between `Grothendieck (G.functor ⋙ F)` and `Grothendieck F`.
-/
def preEquivalence (G : D ≌ C) : Grothendieck (G.functor ⋙ F) ≌ Grothendieck F where
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
  functor_unitIso_comp := by
    intro X
    simp only [preInv, Grothendieck.preUnitIso, pre_id,
      Iso.trans_hom, eqToIso.hom, eqToHom_app, eqToHom_refl, isoWhiskerLeft_hom, NatTrans.comp_app]
    fapply Grothendieck.ext <;> simp [preNatIso, transportIso]

variable {F} in
/--
Let `F, F' : C ⥤ Cat` be functor, `G : D ≌ C` an equivalence and `α : F ⟶ F'` a natural
transformation.

Left-whiskering `α` by `G` and then taking the Grothendieck construction is, up to isomorphism,
the same as taking the Grothendieck construction of `α` and using the equivalences `pre F G`
and `pre F' G` to match the expected type:

```
Grothendieck (G.functor ⋙ F) ≌ Grothendieck F ⥤ Grothendieck F' ≌ Grothendieck (G.functor ⋙ F')
```
-/
def mapWhiskerLeftIsoConjPreMap {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F') :
    map (whiskerLeft G.functor α) ≅
      (preEquivalence F G).functor ⋙ map α ⋙ (preEquivalence F' G).inverse :=
  (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (preEquivalence F' G).unitIso

end Pre

section FunctorFrom

variable {E : Type*} [Category E]

variable (F) in
/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its Grothendieck
construction. -/
@[simps obj map]
def ι (c : C) : F.obj c ⥤ Grothendieck F where
  obj d := ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
    simp only [eqToHom_comp_iff, Category.assoc, eqToHom_trans_assoc]
    apply Functor.congr_hom (F.map_id _).symm

instance faithful_ι (c : C) : (ι F c).Faithful where
  map_injective f := by
    injection f with _ f
    rwa [cancel_epi] at f

/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
@[simps]
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ F.map f ⋙ ι F Y where
  app d := ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ F.map f ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f) (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

/-- Construct a functor from `Grothendieck F` to another category `E` by providing a family of
functors on the fibers of `Grothendieck F`, a family of natural transformations on morphisms in the
base of `Grothendieck F` and coherence data for this family of natural transformations. -/
@[simps]
def functorFrom : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

/-- `Grothendieck.ι F c` composed with `Grothendieck.functorFrom` is isomorphic a functor on a fiber
on `F` supplied as the first argument to `Grothendieck.functorFrom`. -/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

end FunctorFrom

/-- The fiber inclusion `ι F c` composed with `map α` is isomorphic to `α.app c ⋙ ι F' c`. -/
@[simps!]
def ιCompMap {F' : C ⥤ Cat} (α : F ⟶ F') (c : C) : ι F c ⋙ map α ≅ α.app c ⋙ ι F' c :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by simp [map])

end Grothendieck

end CategoryTheory
