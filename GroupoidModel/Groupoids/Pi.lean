import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.ForMathlib.CategoryTheory.Whiskering
import GroupoidModel.ForMathlib.CategoryTheory.NatTrans

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
namespace CategoryTheory

variable {Γ : Type u} [Groupoid Γ]

def Grpd.Functor.iso (A : Γ ⥤ Grpd) {x y : Γ} (f : x ⟶ y) : A.obj x ≅≅ A.obj y where
  hom := A.map f
  inv := A.map (inv f)
  hom_inv_id := by simp [← Grpd.comp_eq_comp, ← Grpd.id_eq_id,
    ← Functor.map_comp, - Functor.map_inv]
  inv_hom_id := by simp [← Grpd.comp_eq_comp, ← Grpd.id_eq_id,
    ← Functor.map_comp, - Functor.map_inv]

lemma Grpd.Functor.iso_hom (A : Γ ⥤ Grpd) {x y : Γ} (f : x ⟶ y) :
  (Grpd.Functor.iso A f).hom = A.map f := rfl

lemma Grpd.Functor.iso_inv (A : Γ ⥤ Grpd) {x y : Γ} (f : x ⟶ y) :
  (Grpd.Functor.iso A f).inv = A.map (inv f) := rfl
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

open CategoryTheory NaturalModelBase Opposite Functor.Groupoidal

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp Functor.comp_id

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
  apply Hom.hext
  · simp
  · have β_ιNatTrans_naturality : β.map ((ι A x).map h) ≫ β.map ((ιNatTrans f).app a2)
        = β.map ((ιNatTrans f).app a1) ≫ β.map ((A.map f ⋙ ι A y).map h) := by
      simp [← Functor.map_comp, (ιNatTrans f).naturality h]
    have h_naturality : (β.map ((ιNatTrans f).app a2)).base.map (β.map ((ι A x).map h)).fiber
        ≫ (β.map ((ιNatTrans f).app a2)).fiber ≍
        (β.map ((ι A y).map ((A.map f).map h))).base.map (β.map ((ιNatTrans f).app a1)).fiber
        ≫ (β.map ((ι A y).map ((A.map f).map h))).fiber := by
      simpa [← heq_eq_eq] using Grothendieck.Hom.congr β_ιNatTrans_naturality
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
  apply Hom.hext
  · simp
  · simp [app]
    rw! (castMode := .all) [ιNatTrans_id_app]
    simp [Grothendieck.Hom.congr (eqToHom_map β _), Functor.Grothendieck.fiber_eqToHom,
      eqToHom_trans]
    apply (eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm

lemma lamFibObjObjCompSigmaMap.app_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) (a) :
    app A β (f ≫ g) a
    = eqToHom (by simp)
    ≫ (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g).map (app A β f a)
    ≫ app A β g ((A.map f).obj a) ≫ eqToHom (by simp) := by
  fapply Hom.hext
  · simp only [Grpd.forgetToCat.eq_1, sigmaObj, comp_obj, sigmaMap_obj_base, app_base, comp_base,
      base_eqToHom, sigmaMap_map_base, map_id, lamFibObjObj_obj_base, map_comp, Grpd.comp_eq_comp,
      eqToHom_naturality, Category.comp_id, eqToHom_trans, eqToHom_refl]
  · have : (β.map ((ιNatTrans (f ≫ g)).app a)) = β.map ((ιNatTrans f).app a)
      ≫ β.map ((ιNatTrans g).app ((A.map f).obj a))
      ≫ eqToHom (by simp) := by
      simp [ιNatTrans_comp_app]
    simp only [comp_obj, sigmaObj, sigmaMap_obj_base, app, Functor.comp_map,
      PGrpd.forgetToGrpd_map, sigmaMap_obj_fiber, homMk_base, homMk_fiber,
      Grothendieck.Hom.congr this, Grothendieck.Hom.comp_base, Grpd.comp_eq_comp,
      Grothendieck.Hom.comp_fiber, eqToHom_refl, Functor.Grothendieck.fiber_eqToHom,
      Category.id_comp, eqToHom_trans_assoc, comp_base, sigmaMap_map_base, comp_fiber,
      fiber_eqToHom, eqToHom_map, sigmaMap_map_fiber, map_comp, Category.assoc,
      heq_eqToHom_comp_iff, eqToHom_comp_heq_iff]
    have : ((ιNatTrans g).app ((A.map f).obj a)) = homMk g (𝟙 _) := by
      apply Hom.ext _ _ (by simp) (by aesop_cat)
    rw! [Category.id_comp, base_eqToHom, eqToHom_map, eqToHom_map,
      Functor.Grothendieck.base_eqToHom, ιNatTrans_app_base, this]
    aesop_cat

def lamFibObjObjCompSigmaMap :
    lamFibObjObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⟶
    A.map f ⋙ lamFibObjObj A β y where
  app := lamFibObjObjCompSigmaMap.app A β f
  naturality _ _ h := lamFibObjObjCompSigmaMap.naturality A β f h

@[simp] lemma lamFibObjObjCompSigmaMap_id (x : Γ) : lamFibObjObjCompSigmaMap A β (𝟙 x) =
    eqToHom (by simp [sigmaMap_id]) := by
  ext a
  simp [lamFibObjObjCompSigmaMap]

/--
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

lemma Functor.associator_eq {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : associator F G H = CategoryTheory.Iso.refl _ :=
  rfl

attribute [local simp] Functor.assoc in
lemma whiskerLeftInvLamObjObjSimgaMap_comp_aux {A A' B B' C C' : Type*}
    [Category A] [Category A'] [Category B] [Category B'] [Category C] [Category C']
    (F : Functor.Iso A B) (G : Functor.Iso B C) (lamA : A ⥤ A') (lamB : B ⥤ B') (lamC : C ⥤ C')
    (F' : A' ⥤ B') (G' : B' ⥤ C')
    (lamF : lamA ⋙ F' ⟶ F.hom ⋙ lamB) (lamG : lamB ⋙ G' ⟶ G.hom ⋙ lamC)
    (H1 : A ⥤ C') (e1 : H1 = _) (H2 : A ⥤ C') (e2 : F.hom ⋙ G.hom ⋙ lamC = H2) :
    whiskerLeft (G.inv ⋙ F.inv)
      (eqToHom e1 ≫ whiskerRight lamF G' ≫ whiskerLeft F.hom lamG ≫ eqToHom e2) =
    eqToHom (by aesop) ≫
      whiskerRight (whiskerLeft G.inv (whiskerLeft F.inv lamF ≫ eqToHom (by simp))) G' ≫
      whiskerLeft G.inv lamG ≫
      eqToHom (by aesop) :=
  calc _
    _ = whiskerLeft (G.inv ⋙ F.inv) (eqToHom e1) ≫
      whiskerLeft (G.inv ⋙ F.inv) (whiskerRight lamF G') ≫
      whiskerLeft (G.inv ⋙ F.inv) (whiskerLeft F.hom lamG) ≫
      whiskerLeft (G.inv ⋙ F.inv) (eqToHom e2)
      := rfl
    _ = eqToHom (by aesop) ≫
      (G.inv ⋙ F.inv).whiskerLeft (whiskerRight lamF G') ≫
      (G.inv ⋙ F.inv ⋙ F.hom).whiskerLeft lamG ≫
      eqToHom (by aesop) := by aesop
    _ = (eqToHom (by aesop)) ≫
      whiskerLeft (G.inv ⋙ F.inv) (whiskerRight lamF G') ≫
      eqToHom (by simp) ≫
      whiskerLeft G.inv lamG ≫
      eqToHom (by aesop) := by
        congr 2
        simp only [Functor.assoc, ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
          comp_eqToHom_heq_iff]
        rw! (castMode := .all) [F.inv_hom_id, Functor.comp_id]
        simp
    _ = eqToHom (by aesop) ≫
      whiskerRight (whiskerLeft G.inv (whiskerLeft F.inv lamF ≫ eqToHom (by simp))) G' ≫
      whiskerLeft G.inv lamG ≫
      eqToHom (by aesop) := by aesop_cat

lemma whiskerLeftInvLamObjObjSigmaMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    whiskerLeftInvLamObjObjSigmaMap A β (f ≫ g)
    = eqToHom (by simp [Functor.assoc, sigmaMap_comp])
    ≫ whiskerRight (whiskerLeft (A.map (CategoryTheory.inv g)) (whiskerLeftInvLamObjObjSigmaMap A β f))
      (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)
    ≫ whiskerLeftInvLamObjObjSigmaMap A β g := by
  simp only [whiskerLeftInvLamObjObjSigmaMap, lamFibObjObjCompSigmaMap_comp]
  have hAfg : A.map (CategoryTheory.inv (f ≫ g)) = (Grpd.Functor.iso A g).inv ≫
    (Grpd.Functor.iso A f).inv := by simp [Grpd.Functor.iso]
  rw! (castMode := .all) [hAfg, ← Grpd.Functor.iso_inv A f, ← Grpd.Functor.iso_inv A g,
    ← Grpd.Functor.iso_hom A f]
  erw [whiskerLeftInvLamObjObjSimgaMap_comp_aux (Grpd.Functor.iso A f) (Grpd.Functor.iso A g)
    _ _ _ (sigmaMap (β ⋙ PGrpd.forgetToGrpd) f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)]
  simp only [Category.assoc, eqToHom_trans]

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

end
end

def smallUPi_app {Γ : Ctx.{max u (v+1)}}
    (AB : y(Γ) ⟶ smallU.{v, max u (v+1)}.Ptp.obj smallU.{v, max u (v+1)}.Ty) :
    y(Γ) ⟶ smallU.{v, max u (v+1)}.Ty :=
  yonedaCategoryEquiv.symm (pi _ (smallU.PtpEquiv.snd AB))

/-- The formation rule for Π-types for the natural model `smallU` -/
def smallUPi.Pi : smallU.{v}.Ptp.obj smallU.{v}.Ty ⟶ smallU.{v}.Ty :=
  NatTrans.yonedaMk smallUPi_app sorry

/-- The introduction rule for Π-types for the natural model `smallU` -/
def smallUPi.lam : smallU.{v}.Ptp.obj smallU.{v}.Tm ⟶ smallU.{v}.Tm :=
  NatTrans.yonedaMk sorry sorry

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

end FunctorOperation

end GroupoidModel
