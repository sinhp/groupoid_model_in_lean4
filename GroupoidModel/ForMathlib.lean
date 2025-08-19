import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Logic.Function.ULift
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.Data.Part
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Adjunction.Limits
import SEq.Tactic.DepRewrite
import GroupoidModel.ForMathlib.CategoryTheory.Bicategory.Grothendieck

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
theorem comp_downFunctor_inj (F G : C ⥤ ULift.{u} D) :
    F ⋙ downFunctor = G ⋙ downFunctor ↔ F = G := by
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

section

variable (C : Type*) [Category C] (D : Type*) [Category D]

@[simp] lemma prod.eqToHom_fst (x y : C × D) (h : x = y) :
    (eqToHom h).1 = eqToHom (by aesop) := by
  subst h
  rfl

@[simp] lemma prod.eqToHom_snd (x y : C × D) (h : x = y) :
    (eqToHom h).2 = eqToHom (by aesop) := by
  subst h
  rfl

end

namespace IsPullback

variable {C : Type u₁} [Category.{v₁} C]

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem of_iso_isPullback (h : IsPullback fst snd f g) {Q} (i : Q ≅ P) :
      IsPullback (i.hom ≫ fst) (i.hom ≫ snd) f g := by
  have : Limits.HasPullback f g := ⟨ h.cone , h.isLimit ⟩
  refine IsPullback.of_iso_pullback (by simp [h.w]) (i ≪≫ h.isoPullback) (by simp) (by simp)

@[simp] theorem isoPullback_refl [Limits.HasPullback f g] :
    isoPullback (.of_hasPullback f g) = Iso.refl _ := by ext <;> simp

end IsPullback
end CategoryTheory

namespace CategoryTheory

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
  simp only [← Functor.assoc, h]

theorem comp_down_inj {C : Type u} [Category.{v} C]
  {D : Type u₁} [Category.{v₁} D]
    {F G : C ⥤ AsSmall.{w} D}
    (h : F ⋙ AsSmall.down = G ⋙ AsSmall.down)
    : F = G := by
  convert_to F ⋙ AsSmall.down
    ⋙ AsSmall.up
    = G ⋙ AsSmall.down ⋙ AsSmall.up
  simp only [← Functor.assoc, h]

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

lemma homOf_id {A : Type u} [Groupoid.{v} A] : Grpd.homOf (𝟭 A) = 𝟙 _ :=
  rfl

lemma homOf_comp {A B C : Type u} [Groupoid.{v} A] [Groupoid.{v} B] [Groupoid.{v} C]
    (F : A ⥤ B) (G : B ⥤ C) : Grpd.homOf (F ⋙ G) = Grpd.homOf F ≫ Grpd.homOf G :=
  rfl

def asSmallFunctor : Grpd.{v, u} ⥤ Grpd.{max w v u, max w v u} where
  obj Γ := Grpd.of $ AsSmall.{max w v u} Γ
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

end Grpd

namespace Equivalence
noncomputable section
open Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [CartesianMonoidalCategory C]
  (e : Equivalence C D)

/-- The chosen terminal object in `D`. -/
abbrev chosenTerminal : D :=
  e.functor.obj (𝟙_ C)

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
  isLimitCartesianMonoidalCategoryOfPreservesLimits e.functor
    (e.inverse.obj X) (e.inverse.obj Y))))
  (BinaryFan.ext (eqToIso rfl) (by aesop_cat) (by aesop_cat))

def chosenFiniteProducts [CartesianMonoidalCategory C] : CartesianMonoidalCategory D :=
  .ofChosenFiniteProducts
    { cone := asEmptyCone e.chosenTerminal
      isLimit := e.chosenTerminalIsTerminal }
    (fun X Y => {
      cone := e.prodCone X Y
      isLimit := e.isLimitProdCone X Y })

end
end Equivalence

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

namespace Functor.Grothendieck

variable {Γ : Type*} [Category Γ] {A : Γ ⥤ Cat}
  {x y : Grothendieck A}

theorem cast_eq {F G : Γ ⥤ Cat}
    (h : F = G) (p : Grothendieck F) :
    (cast (by subst h; rfl) p : Grothendieck G)
    = ⟨ p.base , cast (by subst h; rfl) p.fiber ⟩ := by
  subst h
  rfl

theorem map_eqToHom_base_pf {G1 G2 : Grothendieck A} (eq : G1 = G2) :
    A.obj G1.base = A.obj G2.base := by subst eq; rfl

theorem map_eqToHom_base {G1 G2 : Grothendieck A} (eq : G1 = G2)
    : A.map (eqToHom eq).base = eqToHom (map_eqToHom_base_pf eq) := by
  simp [eqToHom_map]

theorem map_eqToHom_obj_base {F G : Γ ⥤ Cat.{v,u}} (h : F = G)
  (x) : ((Grothendieck.map (eqToHom h)).obj x).base = x.base := rfl

theorem map_forget {F G : Γ ⥤ Cat.{v,u}} (α : F ⟶ G) :
    Grothendieck.map α ⋙ Grothendieck.forget G =
    Grothendieck.forget F :=
  rfl

variable {C : Type u} [Category.{v} C]
    {F : C ⥤ Cat.{v₁,u₁}}

variable {E : Type*} [Category E]
variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ F.map f ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ Functor.whiskerLeft (F.map f) (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

variable (K : Grothendieck F ⥤ E)

def asFunctorFrom_fib (c : C) : (F.obj c) ⥤ E := ι F c ⋙ K

def asFunctorFrom_hom {c c' : C} (f: c ⟶ c') :
    asFunctorFrom_fib K c ⟶ F.map f ⋙ asFunctorFrom_fib K c' :=
  Functor.whiskerRight (ιNatTrans f) K

lemma asFunctorFrom_hom_app {c c' : C} (f: c ⟶ c') (p : F.obj c) :
    (asFunctorFrom_hom K f).app p = K.map ((ιNatTrans f).app p) :=
  rfl

lemma asFunctorFrom_hom_id (c : C) : asFunctorFrom_hom K (𝟙 c) =
    eqToHom (by simp only[Functor.map_id,Cat.id_eq_id,Functor.id_comp]) := by
  ext p
  simp [asFunctorFrom_hom_app, eqToHom_map, ιNatTrans_id_app]

lemma asFunctorFrom_hom_comp (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g: c₂ ⟶ c₃) :
    asFunctorFrom_hom K (f ≫ g) =
    asFunctorFrom_hom K f ≫ Functor.whiskerLeft (F.map f) (asFunctorFrom_hom K g) ≫ eqToHom
    (by simp[← Functor.assoc]; congr) := by
  ext p
  simp [asFunctorFrom_hom, eqToHom_map, ιNatTrans_comp_app]

theorem asFunctorFrom : Grothendieck.functorFrom (asFunctorFrom_fib K) (asFunctorFrom_hom K)
    (asFunctorFrom_hom_id K) (asFunctorFrom_hom_comp K) = K := by
  fapply CategoryTheory.Functor.ext
  · intro X
    rfl
  · intro x y f
    simp only [functorFrom_obj, asFunctorFrom_fib, Functor.comp_obj, functorFrom_map,
      asFunctorFrom_hom, Functor.whiskerRight_app, Functor.comp_map, ← Functor.map_comp,
      eqToHom_refl, Category.comp_id, Category.id_comp]
    congr
    fapply Hom.ext
    · simp
    · simp

variable {D : Type*} [Category D] (G : E ⥤ D)

def functorFrom_comp_fib (c : C) : F.obj c ⥤ D := fib c ⋙ G

def functorFrom_comp_hom {c c' : C} (f : c ⟶ c') :
    functorFrom_comp_fib fib G c ⟶ F.map f ⋙ functorFrom_comp_fib fib G c' :=
  Functor.whiskerRight (hom f) G

include hom_id in
lemma functorFrom_comp_hom_id (c : C) : functorFrom_comp_hom fib hom G (𝟙 c)
    = eqToHom (by simp [Cat.id_eq_id, Functor.id_comp]) := by
  ext x
  simp [hom_id, eqToHom_map, functorFrom_comp_hom]

include hom_comp in
lemma functorFrom_comp_hom_comp (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃):
    functorFrom_comp_hom fib (fun {c c'} ↦ hom) G (f ≫ g)
    = functorFrom_comp_hom fib (fun {c c'} ↦ hom) G f ≫
    Functor.whiskerLeft (F.map f) (functorFrom_comp_hom fib hom G g) ≫
    eqToHom (by simp[Cat.comp_eq_comp, Functor.map_comp, Functor.assoc]) := by
  ext
  simp [functorFrom_comp_hom, hom_comp, eqToHom_map]

theorem functorFrom_comp : functorFrom fib hom hom_id hom_comp ⋙ G =
    functorFrom (functorFrom_comp_fib fib G) (functorFrom_comp_hom fib hom G)
  (functorFrom_comp_hom_id fib hom hom_id G)
  (functorFrom_comp_hom_comp fib hom hom_comp G) := by
  fapply CategoryTheory.Functor.ext
  · intro X
    simp [functorFrom_comp_fib]
  · intro x y f
    simp [functorFrom_comp_hom, functorFrom_comp_fib]

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
    (hfib : asFunctorFrom_fib K = asFunctorFrom_fib K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), asFunctorFrom_hom K f ≫ eqToHom (by rw [hfib])
      = eqToHom (by rw[hfib]) ≫ asFunctorFrom_hom K' f)
    : K = K' :=
    calc K
     _ = functorFrom (asFunctorFrom_fib K) (asFunctorFrom_hom K)
         (asFunctorFrom_hom_id K) (asFunctorFrom_hom_comp K) :=
         (asFunctorFrom K).symm
     _ = functorFrom (asFunctorFrom_fib K') (asFunctorFrom_hom K')
         (asFunctorFrom_hom_id K') (asFunctorFrom_hom_comp K') := by
         apply functorFrom_eq_of
         · exact hhom
         · exact hfib
     _ = K' := asFunctorFrom K'

theorem functorFrom_hext {K K' : Grothendieck F ⥤ E}
    (hfib : asFunctorFrom_fib K = asFunctorFrom_fib K')
    (hhom : ∀ {c c' : C} (f : c ⟶ c'), asFunctorFrom_hom K f ≍ asFunctorFrom_hom K' f)
    : K = K' := by
  fapply functorFrom_ext
  · assumption
  · intros
    apply eq_of_heq
    simp only [heq_eqToHom_comp_iff, comp_eqToHom_heq_iff]
    apply hhom

end Functor.Grothendieck

section
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {B : Type u} [Category.{v} B]

@[simp]
theorem isoWhiskerLeft_eqToIso (F : C ⥤ D) {G H : D ⥤ E} (η : G = H) :
    Functor.isoWhiskerLeft F (eqToIso η) = eqToIso (by subst η; rfl) := by
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

namespace CategoryTheory

variable {C : Type u₁} [SmallCategory C] {F G : Cᵒᵖ ⥤ Type u₁}
  (app : ∀ {X : C}, (yoneda.obj X ⟶ F) → (yoneda.obj X ⟶ G))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y) (α : yoneda.obj Y ⟶ F),
    app (yoneda.map f ≫ α) = yoneda.map f ≫ app α)

variable (F) in
/--
  A presheaf `F` on a small category `C` is isomorphic to
  the hom-presheaf `Hom(y(•),F)`.
-/
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

namespace Functor

theorem precomp_heq_of_heq_id {A B : Type u} {C : Type*} [Category.{v} A] [Category.{v} B] [Category C]
    (hAB : A = B) (h0 : HEq (inferInstance : Category A) (inferInstance : Category B)) {F : A ⥤ B}
    (h : HEq F (𝟭 B)) (G : B ⥤ C) : HEq (F ⋙ G) G := by
  subst hAB
  subst h0
  subst h
  rfl

theorem comp_heq_of_heq_id {A B : Type u} {C : Type*} [Category.{v} A] [Category.{v} B] [Category C]
    (hAB : A = B) (h0 : HEq (inferInstance : Category A) (inferInstance : Category B))
    {F : B ⥤ A}
    (h : HEq F (𝟭 B)) (G : C ⥤ B) : HEq (G ⋙ F) G := by
  subst hAB
  subst h0
  subst h
  rfl

end Functor

end CategoryTheory
