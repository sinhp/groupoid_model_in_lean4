import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.ForMathlib.CategoryTheory.Whiskering
import GroupoidModel.ForMathlib.CategoryTheory.NatTrans

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
namespace CategoryTheory

namespace ObjectProperty

-- JH: after the golfs, we don't acuse this lemma anymore,
-- but it is still probably useful?
lemma ι_mono {T C : Type u} [Category.{v} C] [Category.{v} T]
    {Z : C → Prop} (f g : T ⥤ FullSubcategory Z)
    (e: f ⋙ ι Z = g ⋙ ι Z) : f = g := by
  apply CategoryTheory.Functor.ext_of_iso _ _ _
  · exact Functor.fullyFaithfulCancelRight (ι Z) (eqToIso e)
  · intro X
    ext
    exact Functor.congr_obj e X
  · intro X
    simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.preimage, ι_obj, ι_map,
      eqToIso.hom, eqToHom_app, Functor.comp_obj, Classical.choose_eq]
    rfl

end ObjectProperty

end CategoryTheory

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck.Groupoidal  Groupoid

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp Functor.comp_id


-- @yiming can we remove this?
/-
   Uncomment this to see the the flow of organizing Conjugation into the Conjugating functor.
   def Conjugating0 {Γ : Grpd.{v,u}} (A B : Γ ⥤ Grpd.{u₁,u₁})
    {x y: Γ } (f: x ⟶ y) : (A.obj x⥤ B.obj x) ⥤ (A.obj y⥤ B.obj y) :=
     let wr : B.obj x ⥤ B.obj y := B.map f
     let wl : A.obj y ⥤ A.obj x := A.map (Groupoid.inv f)
     let f1_ty : (A.obj y ⥤ A.obj x) ⥤ ((A.obj x) ⥤ (B.obj x)) ⥤ (A.obj y) ⥤  (B.obj x) :=
       whiskeringLeft (A.obj y) (A.obj x) (B.obj x)
     let f1 : ((A.obj x) ⥤ (B.obj x)) ⥤ (A.obj y) ⥤  (B.obj x) :=
       (whiskeringLeft (A.obj y) (A.obj x) (B.obj x)).obj (A.map (Groupoid.inv f))
     let f2_ty :  ((B.obj x) ⥤ (B.obj y)) ⥤ (A.obj y ⥤ B.obj x) ⥤ (A.obj y) ⥤  (B.obj y) :=
       whiskeringRight (A.obj y) (B.obj x) (B.obj y)
     let f2 : (A.obj y ⥤ B.obj x) ⥤ (A.obj y) ⥤  (B.obj y) :=
       (whiskeringRight (A.obj y) (B.obj x) (B.obj y)).obj (B.map f)
     let f3 := f1 ⋙ f2
     f3
-/

namespace FunctorOperation
section

open CategoryTheory.Functor

variable {Γ : Type u} [Groupoid.{v} Γ] (A B : Γ ⥤ Grpd)

/--
The functor that, on objects `G : A.obj x ⥤ B.obj x` acts by
creating the map on the right,
by taking the inverse of `f : x ⟶ y` in the groupoid
         A f
  A x --------> A y
   |             .
   |             |
   |             .
G  |             | conjugating A B f G
   |             .
   V             V
  B x --------> B y
         B f
-/
def conjugating {x y : Γ} (f : x ⟶ y) : (A.obj x ⥤ B.obj x) ⥤ (A.obj y ⥤ B.obj y) :=
  whiskeringLeftObjWhiskeringRightObj (A.map (CategoryTheory.inv f)) (B.map f)

@[simp] lemma conjugating_obj {x y : Γ} (f : x ⟶ y) (s : A.obj x ⥤ B.obj x) :
    (conjugating A B f).obj s = CategoryTheory.inv (A.map f) ⋙ s ⋙ B.map f := by
  simp [conjugating]

@[simp] lemma conjugating_map {x y : Γ} (f : x ⟶ y) {s1 s2 : A.obj x ⥤ B.obj x} (h : s1 ⟶ s2) :
    (conjugating A B f).map h
    = whiskerRight (whiskerLeft (A.map (CategoryTheory.inv f)) h) (B.map f) := by
  simp [conjugating]

@[simp] lemma conjugating_id (x : Γ) : conjugating A B (𝟙 x) = 𝟭 _ := by
  simp [conjugating]

@[simp] lemma conjugating_comp (x y z : Γ) (f : x ⟶ y) (g : y ⟶ z) :
    conjugating A B (f ≫ g) = conjugating A B f ⋙ conjugating A B g := by
  simp [conjugating]

end

section
variable {A B : Type*} [Category A] [Category B] (F : B ⥤ A)

-- NOTE to follow mathlib convention can use camelCase for definitions, and capitalised first letter when that definition is a Prop or Type
def IsSection (s : A ⥤ B) := s ⋙ F = Functor.id A

abbrev Section := ObjectProperty.FullSubcategory (IsSection F)

instance Section.category : Category (Section F) :=
  ObjectProperty.FullSubcategory.category (IsSection F)

abbrev Section.ι : Section F ⥤ (A ⥤ B) :=
  ObjectProperty.ι (IsSection F)

instance Section.groupoid {B : Type*} [Groupoid B] (F : B ⥤ A) :
    Groupoid (Section F) :=
  InducedCategory.groupoid (A ⥤ B) (fun (f: Section F) ↦ f.obj)

end

section

variable {Γ : Type*} [Category Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
  (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ)

abbrev sigma.fstAuxObj : sigmaObj B x ⥤ A.obj x := forget

open sigma

def piObj : Type _ := Section (fstAuxObj B x)

instance piObj.groupoid : Groupoid (piObj B x) :=
  inferInstanceAs (Groupoid (Section (fstAuxObj B x)))

end

section
variable {Γ : Type*} [Groupoid Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (B : ∫(A) ⥤ Grpd.{u₁,u₁})
variable {x y: Γ} (f: x ⟶ y)

open sigma

/--
If `s : piObj B x` then the underlying functor is of the form `s : A x ⥤ sigma A B x`
and it is a section of the forgetful functor `sigma A B x ⥤ A x`.
This theorem states that conjugating `A f⁻¹ ⋙ s ⋙ sigma A B f⁻¹ : A y ⥤ sigma A B y`
using some `f : x ⟶ y` produces a section of the forgetful functor `sigma A B y ⥤ A y`.
-/
theorem isSection_conjugating_isSection (s : piObj B x) : IsSection (fstAuxObj B y)
    ((Section.ι (fstAuxObj B x) ⋙ conjugating A (sigma A B) f).obj s) := by
  simp only [IsSection, Functor.comp_obj, ObjectProperty.ι_obj,
    conjugating_obj, Functor.assoc]
  convert_to CategoryTheory.inv (A.map f) ⋙ (s.obj ⋙ fstAuxObj B x) ⋙ A.map f = _
  rw [s.property]
  simp only [Functor.id_comp, ← Grpd.comp_eq_comp, IsIso.inv_hom_id, Grpd.id_eq_id]

/-- The functorial action of `pi` on a morphism `f : x ⟶ y` in `Γ`
is given by "conjugation".
Since `piObj B x` is a full subcategory of `sigma A B x ⥤ A x`,
we obtain the action `piMap : piObj B x ⥤ piObj B y`
as the induced map in the following diagram
          the inclusion
           Section.ι
   piObj B x   ⥤   (A x ⥤ sigma A B x)
     ⋮                     ||
     ⋮                     || conjugating A (sigma A B) f
     VV                     VV
   piObj B y   ⥤   (A y ⥤ sigma A B y)
-/
def piMap : piObj B x ⥤ piObj B y :=
  ObjectProperty.lift (IsSection (fstAuxObj B y))
  ((Section.ι (fstAuxObj B x) ⋙ conjugating A (sigma A B) f))
  (isSection_conjugating_isSection A B f)

lemma piMap_obj_obj (s: piObj B x) : ((piMap A B f).obj s).obj =
    (conjugating A (sigma A B) f).obj s.obj := rfl

lemma piMap_map (s1 s2: piObj B x) (η: s1 ⟶ s2) :
    (piMap A B f).map η = (conjugating A (sigma A B) f).map η :=
  rfl

/--
The square commutes

   piObj B x   ⥤   (A x ⥤ sigma A B x)
     ⋮                     ||
piMap⋮                     || conjugating A (sigma A B) f
     VV                     VV
   piObj B y   ⥤   (A y ⥤ sigma A B y)
-/
lemma piMap_ι : piMap A B f ⋙ Section.ι (fstAuxObj B y)
    = Section.ι (fstAuxObj B x) ⋙ conjugating A (sigma A B) f :=
  rfl

@[simp] lemma piMap_id (x : Γ) : piMap A B (𝟙 x) = 𝟭 (piObj B x) := by
  simp only [piMap, conjugating_id]
  rfl

lemma piMap_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    piMap A B (f ≫ g) = (piMap A B f) ⋙ (piMap A B g) := by
  simp only [piMap, conjugating_comp]
  rfl

/-- The formation rule for Π-types for the natural model `smallU`
  as operations between functors -/
@[simps] def pi : Γ ⥤ Grpd.{u₁,u₁} where
  obj x := Grpd.of $ piObj B x
  map := piMap A B
  map_id := piMap_id A B
  map_comp := piMap_comp A B

end

namespace pi

variable {Γ : Type*} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫(A) ⥤ Grpd)
  (f : Γ ⥤ PGrpd) (hf : f ⋙ PGrpd.forgetToGrpd = pi A B)

-- NOTE: it seems like we need a 2-categorical version of Grothendieck.map
-- so the following should be replaced with something like
-- `secAux : CategoryTheory.Oplax.OplaxTrans A (sigma A B)`
-- def secAux : A ⟶ sigma A B where
--   app x := (PGrpd.objFiber' hf x).obj
--   naturality x y g := by
--     have h : (((pi A B).map g).obj (PGrpd.objFiber' hf x)).obj ⟶ (PGrpd.objFiber' hf y).obj :=
--       PGrpd.mapFiber' hf g
--     simp [piMap_obj_obj] at h
--     simp

--     sorry

-- def secFib (x) : A.obj x ⥤ ∫(sigma A B) := (PGrpd.objFiber' hf x).obj ⋙ ι (sigma A B) x

-- def secHom {x y} (g : x ⟶ y) : secFib B f hf x ⟶ A.map g ⋙ secFib B f hf y := by
--   have h : (((pi A B).map g).obj (PGrpd.objFiber' hf x)).obj ⟶ (PGrpd.objFiber' hf y).obj :=
--       PGrpd.mapFiber' hf g
--   simp [piMap_obj_obj] at h
--   simp [secFib]
--   sorry

-- NOTE: this should be defined as something like `Grothendieck.Groupoidal.mapOplax secAux`
def sec : ∫(A) ⥤ ∫(sigma A B) :=
  sorry
  -- have h (x) := (PGrpd.objFiber' hf x).obj
  -- exact functorTo forget (fun x => (h x.base).obj x.fiber) sorry sorry sorry
  -- exact functorFrom (secFib B f hf) (fun {x y} g => sorry) sorry sorry

/--  Let `Γ` be a category.
For any pair of functors `A : Γ ⥤ Grpd` and `B : ∫(A) ⥤ Grpd`,
and any "term of pi", meaning a functor `f : Γ ⥤ PGrpd`
satisfying `f ⋙ forgetToGrpd = pi A B : Γ ⥤ Grpd`,
there is a "term of `B`" `sec' : Γ ⥤ PGrpd` such that `sec' ⋙ forgetToGrpd = B`.
-/
def sec' : ∫(A) ⥤ PGrpd := sorry ⋙ sigma.assoc B ⋙ toPGrpd B

def sec_forgetToGrpd : sec' B ⋙ PGrpd.forgetToGrpd = B := sorry

end pi

section

variable {Γ : Type*} [Groupoid Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (β : ∫(A) ⥤ PGrpd.{u₁,u₁})

section
variable (x : Γ)

def lamFibObjObj :=
  sec (ι A x ⋙ β ⋙ PGrpd.forgetToGrpd) (ι A x ⋙ β) rfl

@[simp] lemma lamFibObjObj_obj_base (a) : ((lamFibObjObj A β x).obj a).base = a := by
  simp [lamFibObjObj]

@[simp] lemma lamFibObjObj_obj_fiber (a) : ((lamFibObjObj A β x).obj a).fiber
    = PGrpd.objFiber (ι A x ⋙ β) a := by
  simp [lamFibObjObj]

@[simp] lemma lamFibObjObj_map_base {a a'} (h: a ⟶ a'):
    ((lamFibObjObj A β x).map h).base = h := by
  simp [lamFibObjObj]

@[simp] lemma lamFibObjObj_map_fiber {a a'} (h: a ⟶ a'):
    ((lamFibObjObj A β x).map h).fiber = PGrpd.mapFiber (ι A x ⋙ β) h := by
  simp [lamFibObjObj]

def lamFibObj : piObj (β ⋙ PGrpd.forgetToGrpd) x :=
  ⟨lamFibObjObj A β x , rfl⟩

@[simp] lemma lamFibObj_obj : (lamFibObj A β x).obj = lamFibObjObj A β x :=
  rfl

@[simp] lemma lamFibObj_obj_obj : (lamFibObj A β x).obj = lamFibObjObj A β x :=
  rfl

end

section
variable {x y : Γ} (f : x ⟶ y)

open CategoryTheory.Functor
def lamFibObjObjCompSigmaMap.app (a : A.obj x) :
    (lamFibObjObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f).obj a ⟶
    (A.map f ⋙ lamFibObjObj A β y).obj a :=
  homMk (𝟙 _) (eqToHom (by simp; rfl) ≫ (β.map ((ιNatTrans f).app a)).fiber)

@[simp] lemma lamFibObjObjCompSigmaMap.app_base (a : A.obj x) : (app A β f a).base = 𝟙 _ := by
  simp [app]

lemma lamFibObjObjCompSigmaMap.app_fiber_eq (a : A.obj x) : (app A β f a).fiber =
    eqToHom (by simp; rfl) ≫ (β.map ((ιNatTrans f).app a)).fiber := by
  simp [app]

lemma lamFibObjObjCompSigmaMap.app_fiber_heq (a : A.obj x) : (app A β f a).fiber ≍
    (β.map ((ιNatTrans f).app a)).fiber := by
  simp [app]

lemma lamFibObjObjCompSigmaMap.naturality {x y : Γ} (f : x ⟶ y) {a1 a2 : A.obj x} (h : a1 ⟶ a2) :
    (lamFibObjObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f).map h
    ≫ lamFibObjObjCompSigmaMap.app A β f a2 =
    lamFibObjObjCompSigmaMap.app A β f a1
    ≫ (A.map f ⋙ lamFibObjObj A β y).map h := by
  apply Grothendieck.Groupoidal.hext
  · simp
  · have β_ιNatTrans_naturality : β.map ((ι A x).map h) ≫ β.map ((ιNatTrans f).app a2)
        = β.map ((ιNatTrans f).app a1) ≫ β.map ((A.map f ⋙ ι A y).map h) := by
      simp [← Functor.map_comp, (ιNatTrans f).naturality h]
    have h_naturality : (β.map ((ιNatTrans f).app a2)).base.map (β.map ((ι A x).map h)).fiber
        ≫ (β.map ((ιNatTrans f).app a2)).fiber ≍
        (β.map ((ι A y).map ((A.map f).map h))).base.map (β.map ((ιNatTrans f).app a1)).fiber
        ≫ (β.map ((ι A y).map ((A.map f).map h))).fiber := by
      simpa [← heq_eq_eq] using Grothendieck.congr β_ιNatTrans_naturality
    simp only [Functor.comp_obj, sigmaMap_obj_base, Functor.comp_map, comp_base, sigmaMap_map_base,
      comp_fiber, sigmaMap_map_fiber, lamFibObjObj_map_fiber, Functor.map_comp, eqToHom_map,
      app_fiber_eq, Category.assoc, heq_eqToHom_comp_iff, eqToHom_comp_heq_iff]
    rw [← Category.assoc]
    apply HEq.trans _ h_naturality
    apply heq_comp _ rfl rfl _ HEq.rfl
    · aesop_cat
    · simp only [← Functor.comp_map, ← Grpd.comp_eq_comp, comp_eqToHom_heq_iff]
      congr 3
      aesop_cat

@[simp] lemma lamFibObjObjCompSigmaMap.app_id (a) : lamFibObjObjCompSigmaMap.app A β (𝟙 x) a
    = eqToHom (by simp) := by
  apply Grothendieck.Groupoidal.hext
  · simp
  · simp [app]
    rw! (castMode := .all) [ιNatTrans_id_app]
    simp only [Grothendieck.congr (eqToHom_map β _), Grothendieck.fiber_eqToHom, eqToHom_trans]
    apply (eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm

lemma lamFibObjObjCompSigmaMap.app_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) (a) :
    lamFibObjObjCompSigmaMap.app A β (f ≫ g) a
    = eqToHom (by simp)
    ≫ (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g).map (app A β f a)
    ≫ app A β g ((A.map f).obj a) ≫ eqToHom (by simp) := by
  fapply Grothendieck.Groupoidal.ext
  · simp
  · have h : (β.map ((ιNatTrans (f ≫ g)).app a)) = β.map ((ιNatTrans f).app a)
      ≫ β.map ((ιNatTrans g).app ((A.map f).obj a))
      ≫ eqToHom (by simp) := by
      simp [ιNatTrans_comp_app]
    simp only [Grpd.forgetToCat.eq_1, comp_obj, Grothendieck.forget_obj, sigmaObj,
      sigmaMap_obj_base, app, Functor.comp_map, Grothendieck.forget_map, sigmaMap_obj_fiber,
      Cat.of_α, id_eq, comp_base, sigmaMap_map_base, homMk_base, homMk_fiber, Grothendieck.congr h,
      Grothendieck.comp_base, Grpd.comp_eq_comp, Grothendieck.comp_fiber, eqToHom_refl,
      Grothendieck.fiber_eqToHom, Category.id_comp, eqToHom_trans_assoc, comp_fiber, eqToHom_fiber,
      eqToHom_map, sigmaMap_map_fiber, map_comp, Category.assoc]
    rw! [Grothendieck.eqToHom_base, Category.id_comp, eqToHom_base, eqToHom_base, eqToHom_map,
      eqToHom_map, eqToHom_map, Grothendieck.eqToHom_base]
    aesop_cat

/-
a ---h---> a' in A.obj x

B(x,a) ----> B(y,Afa)
 |               |
 |               |
 v               v
B(x,a')----> B(y,Afa')
-/

def lamFibObjObjCompSigmaMap :
    lamFibObjObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⟶
    A.map f ⋙ lamFibObjObj A β y where
  app := lamFibObjObjCompSigmaMap.app A β f
  naturality _ _ h := lamFibObjObjCompSigmaMap.naturality A β f h

@[simp] lemma lamFibObjObjCompSigmaMap_id (x : Γ) : lamFibObjObjCompSigmaMap A β (𝟙 x) =
    eqToHom (by simp [sigmaMap_id]) := by
  ext a
  simp [lamFibObjObjCompSigmaMap]

/-
lamFibObjObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) (f ≫ g)

_ ⟶ lamFibObjObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) g
:= eqToHom ⋯

_ ⟶ A.map f ⋙ lamFibObjObj A β y ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) g
:= whiskerRight (lamFibObjObjCompSigmaMap A β f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)

_ ⟶ A.map f ⋙ A.map g ⋙ lamFibObjObj A β z
:= whiskerLeft (A.map f) (lamFibObjObjCompSigmaMap A β g)

_ ⟶ A.map (f ≫ g) ⋙ lamFibObjObj A β z
:= eqToHom ⋯

-/

lemma lamFibObjObjCompSigmaMap_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    lamFibObjObjCompSigmaMap A β (f ≫ g) =
    eqToHom (by rw [sigmaMap_comp]; rfl)
    ≫ whiskerRight (lamFibObjObjCompSigmaMap A β f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)
    ≫ whiskerLeft (A.map f) (lamFibObjObjCompSigmaMap A β g)
    ≫ eqToHom (by rw [Functor.map_comp, Grpd.comp_eq_comp, Functor.assoc]) := by
  ext a
  simp [lamFibObjObjCompSigmaMap, lamFibObjObjCompSigmaMap.app_comp]

def whiskerLeftInvLamObjObjSigmaMap :
    A.map (CategoryTheory.inv f) ⋙ lamFibObjObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⟶
    lamFibObjObj A β y :=
  whiskerLeft (A.map (CategoryTheory.inv f)) (lamFibObjObjCompSigmaMap A β f)
  ≫ eqToHom (by simp [← Functor.assoc, ← Grpd.comp_eq_comp])

@[simp] lemma whiskerLeftInvLamObjObjSigmaMap_id (x : Γ) :
    whiskerLeftInvLamObjObjSigmaMap A β (𝟙 x) = eqToHom (by simp [sigmaMap_id]) := by
  simp [whiskerLeftInvLamObjObjSigmaMap]

-- TODO find a better proof. This should not need `ext`,
-- instead should be by manipulating whiskerLeft and whiskerRight lemmas
lemma whiskerLeftInvLamObjObjSigmaMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    whiskerLeftInvLamObjObjSigmaMap A β (f ≫ g)
    = eqToHom (by simp [Functor.assoc, sigmaMap_comp])
    ≫ whiskerRight (whiskerLeft (A.map (CategoryTheory.inv g)) (whiskerLeftInvLamObjObjSigmaMap A β f))
      (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)
    ≫ whiskerLeftInvLamObjObjSigmaMap A β g := by
  simp only [whiskerLeftInvLamObjObjSigmaMap, lamFibObjObjCompSigmaMap_comp]
  rw! [Functor.map_inv, Functor.map_inv, Functor.map_inv,
    Functor.map_comp, IsIso.inv_comp]
  ext
  simp only [Grpd.forgetToCat.eq_1, sigmaObj, Grpd.comp_eq_comp, comp_obj, eqToHom_refl,
    Category.comp_id, whiskerLeft_comp, whiskerLeft_eqToHom, whiskerLeft_twice, Category.assoc,
    NatTrans.comp_app, eqToHom_app, whiskerLeft_app, whiskerRight_app, associator_inv_app,
    associator_hom_app, Category.id_comp, whiskerRight_comp, eqToHom_whiskerRight, map_id]
  congr 2
  simp only [← comp_obj, Functor.assoc]
  simp only [← Grpd.comp_eq_comp]
  rw! (castMode := .all) [IsIso.inv_hom_id]
  apply eq_of_heq
  simp [- heq_eq_eq]
  rfl

def lamFibMap :
    ((pi A (β ⋙ PGrpd.forgetToGrpd)).map f).obj (lamFibObj A β x) ⟶ lamFibObj A β y :=
  whiskerLeftInvLamObjObjSigmaMap A β f

@[simp] lemma lamFibMap_id (x : Γ) : lamFibMap A β (𝟙 x) = eqToHom (by simp) := by
  simp [lamFibMap]
  rfl

lemma lamFibMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    lamFibMap A β (f ≫ g)
    = eqToHom (by rw [← Functor.comp_obj]; apply Functor.congr_obj; simp [piMap_comp])
    ≫ ((piMap A (β ⋙ PGrpd.forgetToGrpd)) g).map ((lamFibMap A β) f)
    ≫ lamFibMap A β g := by
  simp [lamFibMap, piMap, whiskerLeftInvLamObjObjSigmaMap_comp]
  rfl

def lam : Γ ⥤ PGrpd.{u₁,u₁} :=
  PGrpd.functorTo
  (pi A (β ⋙ PGrpd.forgetToGrpd))
  (lamFibObj A β)
  (lamFibMap A β)
  (lamFibMap_id A β)
  (lamFibMap_comp A β)

lemma lam_comp_forgetToGrpd : lam A β ⋙ PGrpd.forgetToGrpd = pi A (β ⋙ PGrpd.forgetToGrpd) :=
  rfl

end
end

section
variable {Γ : Ctx}

namespace smallUPi

def Pi_app (AB : y(Γ) ⟶ smallU.{v}.Ptp.obj smallU.{v}.Ty) :
    y(Γ) ⟶ smallU.{v}.Ty :=
  yonedaCategoryEquiv.symm (pi _ (smallU.PtpEquiv.snd AB))

def Pi_naturality {Δ Γ} (f : Δ ⟶ Γ) (α : y(Γ) ⟶ smallU.Ptp.obj smallU.Ty) :
    Pi_app (ym(f) ≫ α) = ym(f) ≫ Pi_app α := sorry

/-- The formation rule for Π-types for the natural model `smallU` -/
def Pi : smallU.{v}.Ptp.obj smallU.{v}.Ty ⟶ smallU.{v}.Ty :=
  NatTrans.yonedaMk Pi_app Pi_naturality

lemma Pi_app_eq {Γ : Ctx} (ab : y(Γ) ⟶ _) : ab ≫ Pi =
    yonedaCategoryEquiv.symm (FunctorOperation.pi _ (smallU.PtpEquiv.snd ab)) := by
  rw [Pi, NatTrans.yonedaMk_app, Pi_app]

def lam_app (ab : y(Γ) ⟶ smallU.{v}.Ptp.obj smallU.{v}.Tm) :
    y(Γ) ⟶ smallU.{v}.Tm :=
  yonedaCategoryEquiv.symm (lam _ (smallU.PtpEquiv.snd ab))

def lam_naturality {Δ Γ} (f : Δ ⟶ Γ) (α : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) :
    lam_app (ym(f) ≫ α) = ym(f) ≫ lam_app α := sorry

/-- The introduction rule for Π-types for the natural model `smallU` -/
def lam : smallU.{v}.Ptp.obj smallU.{v}.Tm ⟶ smallU.{v}.Tm :=
  NatTrans.yonedaMk lam_app lam_naturality

lemma lam_app_eq {Γ : Ctx} (ab : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) : ab ≫ lam =
    yonedaCategoryEquiv.symm (FunctorOperation.lam _ (smallU.PtpEquiv.snd ab)) := by
  rw [lam, NatTrans.yonedaMk_app, lam_app]

lemma smallU.PtpEquiv.fst_app_comp_map_tp {Γ : Ctx} (ab : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) :
    smallU.PtpEquiv.fst (ab ≫ smallU.Ptp.map smallU.tp) = smallU.PtpEquiv.fst ab :=
  sorry

lemma smallU.PtpEquiv.snd_app_comp_map_tp {Γ : Ctx} (ab : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) :
    smallU.PtpEquiv.snd (ab ≫ smallU.Ptp.map smallU.tp)
    ≍ smallU.PtpEquiv.snd ab ⋙ PGrpd.forgetToGrpd :=
  sorry

theorem lam_tp : smallUPi.lam ≫ smallU.tp = smallU.Ptp.map smallU.tp ≫ Pi := by
  apply hom_ext_yoneda
  intros Γ ab
  rw [← Category.assoc, ← Category.assoc, lam_app_eq, Pi_app_eq, smallU_tp, π,
    ← yonedaCategoryEquiv_symm_naturality_right, lam_comp_forgetToGrpd]
  symm; congr 2
  · apply smallU.PtpEquiv.fst_app_comp_map_tp
  · apply smallU.PtpEquiv.snd_app_comp_map_tp

section
variable {Γ : Ctx} (AB : y(Γ) ⟶ smallU.Ptp.obj.{v} y(U.{v}))
  (αβ : y(Γ) ⟶ y(E.{v})) (hαβ : αβ ≫ ym(π) = AB ≫ smallUPi.Pi)

include hαβ in
theorem yonedaCategoryEquiv_forgetToGrpd : yonedaCategoryEquiv αβ ⋙ PGrpd.forgetToGrpd
    = pi (smallU.PtpEquiv.fst AB) (smallU.PtpEquiv.snd AB) := by
  erw [← yonedaCategoryEquiv_naturality_right, hαβ]
  rw [smallUPi.Pi_app_eq, yonedaCategoryEquiv.apply_symm_apply]

def lift : y(Γ) ⟶ smallU.Ptp.obj.{v} smallU.Tm.{v} :=
  let αβ' := yonedaCategoryEquiv αβ
  smallU.PtpEquiv.mk (smallU.PtpEquiv.fst AB) sorry

  -- let β' := smallU.PtpEquiv.snd AB
  -- let αβ' := yonedaCategoryEquiv αβ
  -- let hαβ' : yonedaCategoryEquiv αβ ⋙ forgetToGrpd
  --   = sigma (smallU.PtpEquiv.fst AB) (smallU.PtpEquiv.snd AB) :=
  --   yonedaCategoryEquiv_forgetToGrpd _ _ hαβ
  -- mk (sigma.fst' β' αβ' hαβ') (sigma.dependent' β' αβ' hαβ')
  -- (sigma.snd' β' αβ' hαβ') (sigma.snd'_forgetToGrpd β' αβ' hαβ')

-- theorem fac_left : lift.{v} AB αβ hαβ ≫ smallUSigma.pair.{v} = αβ := by
--   rw [smallUSigma.pair_app_eq]
--   dsimp only [lift]
--   rw! [dependent_mk, snd_mk, fst_mk]
--   simp only [eqToHom_refl, map_id_eq, Cat.of_α, Functor.id_comp]
--   rw [yonedaCategoryEquiv.symm_apply_eq, sigma.eta]

-- theorem fac_right : lift.{v} AB αβ hαβ ≫ smallU.comp.{v} = AB := by
--   apply smallU.PtpEquiv.hext
--   · rw [← fst_forgetToGrpd]
--     dsimp only [lift]
--     rw [fst_mk, sigma.fst'_forgetToGrpd]
--   · apply HEq.trans (dependent_heq _).symm
--     rw [lift, dependent_mk]
--     dsimp [sigma.dependent']
--     simp [map_id_eq, Functor.id_comp]
--     apply map_eqToHom_comp_heq

-- theorem hom_ext (m n : y(Γ) ⟶ smallU.compDom.{v})
--     (hComp : m ≫ smallU.comp = n ≫ smallU.comp)
--     (hPair : m ≫ smallUSigma.pair = n ≫ smallUSigma.pair) : m = n := by
--   have h : (pair (fst m) (snd m) (dependent m)
--         (snd_forgetToGrpd m)) =
--       (pair (fst n) (snd n) (dependent n)
--         (snd_forgetToGrpd n)) :=
--       calc _
--         _ = yonedaCategoryEquiv (m ≫ smallUSigma.pair) := by
--           simp [smallUSigma.pair_app_eq m]
--         _ = yonedaCategoryEquiv (n ≫ smallUSigma.pair) := by rw [hPair]
--         _ = _ := by
--           simp [smallUSigma.pair_app_eq n]
--   have hdep : HEq (dependent m) (dependent n) := by
--     refine (dependent_heq _).trans
--       $ HEq.trans ?_ $ (dependent_heq _).symm
--     rw [hComp]
--   have : fst m ⋙ forgetToGrpd = fst n ⋙ forgetToGrpd := by
--     rw [fst_forgetToGrpd, fst_forgetToGrpd, hComp]
--   apply smallU.compDom.hext
--   · calc fst m
--       _ = sigma.fst' _ (FunctorOperation.pair (fst m) (snd m)
--         (dependent m) (snd_forgetToGrpd m)) _ :=
--           (sigma.fst'_pair _).symm
--       _ = sigma.fst' _ (FunctorOperation.pair (fst n) (snd n)
--         (dependent n) (snd_forgetToGrpd n)) _ := by
--           rw! [h]
--           congr!
--       _ = fst n := sigma.fst'_pair _
--   · exact hdep
--   · calc snd m
--       _ = sigma.snd' _ (FunctorOperation.pair (fst m) (snd m)
--         (dependent m) (snd_forgetToGrpd m)) _ :=
--           (sigma.snd'_pair _).symm
--       _ = sigma.snd' _ (FunctorOperation.pair (fst n) (snd n)
--         (dependent n) (snd_forgetToGrpd n)) _ := by
--           rw! [h]
--           congr!
--       _ = snd n := sigma.snd'_pair _

-- theorem uniq (m : y(Γ) ⟶ smallU.compDom)
--     (hmAB : m ≫ smallU.comp = AB) (hmαβ : m ≫ smallUSigma.pair = αβ) :
--     m = lift AB αβ hαβ := by
--   apply hom_ext
--   · rw [hmAB, fac_right]
--   · rw [hmαβ, fac_left]

end
theorem isPullback : IsPullback lam.{v,u} (smallU.Ptp.{v,u}.map smallU.tp)
    smallU.{v, u}.tp Pi.{v, u} :=
  Limits.RepPullbackCone.is_pullback lam_tp
    (fun s => sorry)
    (fun s => sorry)
    (fun s => sorry)
    (fun s m fac_left fac_right => sorry)
  -- Limits.RepPullbackCone.is_pullback smallUSigma.lam_tp.{v,u}
  --   (fun s => lift s.snd s.fst s.condition)
  --   (fun s => fac_left.{v,u} _ _ s.condition)
  --   (fun s => fac_right.{v,u} _ _ s.condition)
  --   (fun s m fac_left fac_right => uniq.{v,u} _ _ s.condition m fac_right fac_left)

end smallUPi

def smallUPi : NaturalModelPi smallU.{v} where
  Pi := smallUPi.Pi.{v}
  lam := smallUPi.lam.{v}
  Pi_pullback := sorry

def uHomSeqPis' (i : ℕ) (ilen : i < 4) :
  NaturalModelPi (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUPi.{0,4}
  | 1 => smallUPi.{1,4}
  | 2 => smallUPi.{2,4}
  | 3 => smallUPi.{3,4}
  | (n+4) => by omega

def uHomSeqPis : UHomSeqPiSigma Ctx := { uHomSeq with
  nmPi := uHomSeqPis'
  nmSigma := uHomSeqSigmas' }

end

end FunctorOperation

end GroupoidModel
