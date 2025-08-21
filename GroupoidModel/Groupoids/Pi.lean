import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.ForMathlib.CategoryTheory.Whiskering
import GroupoidModel.ForMathlib.CategoryTheory.NatTrans

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

lemma hcongr_fun {α α' : Type u} (hα : α ≍ α') (β : α → Type v) (β' : α' → Type v) (hβ : β ≍ β')
    (f : (x : α) → β x) (f' : (x : α') → β' x) (hf : f ≍ f')
    {x : α} {x' : α'} (hx : x ≍ x') : f x ≍ f' x' := by
  subst hα hβ hf hx
  rfl

namespace CategoryTheory

lemma Functor.Iso.whiskerLeft_inv_hom_heq {C : Type u} [Category.{v} C] {D : Type u₁}
    [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E] (F : C ≅≅ D) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.inv ⋙ F.hom).whiskerLeft η ≍ η := by
  rw [F.inv_hom_id]
  aesop_cat

lemma Functor.Iso.whiskerLeft_inv_hom {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : C ≅≅ D) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.inv ⋙ F.hom).whiskerLeft η = eqToHom (by aesop) ≫ η ≫ eqToHom (by aesop) := by
  simpa [← heq_eq_eq] using
    Functor.Iso.whiskerLeft_inv_hom_heq F G H η

lemma Functor.Iso.whiskerLeft_hom_inv_heq {C : Type u} [Category.{v} C] {D : Type u₁}
    [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E] (F : D ≅≅ C) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.hom ⋙ F.inv).whiskerLeft η ≍ η := by
  rw [F.hom_inv_id]
  aesop_cat

lemma Functor.Iso.whiskerLeft_hom_inv {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : D ≅≅ C) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.hom ⋙ F.inv).whiskerLeft η = eqToHom (by aesop) ≫ η ≫ eqToHom (by aesop) := by
  simpa [← heq_eq_eq] using
    Functor.Iso.whiskerLeft_hom_inv_heq F G H η

variable {Γ : Type u} [Groupoid Γ] {Δ : Type u₁} [Groupoid.{v₁} Δ]

@[simps]
def Grpd.functorIsoOfIso {A B : Grpd} (F : A ≅ B) : A ≅≅ B where
  hom := F.hom
  inv := F.inv
  hom_inv_id := F.hom_inv_id
  inv_hom_id := F.inv_hom_id

def Grpd.Functor.iso (A : Γ ⥤ Grpd) {x y : Γ} (f : x ⟶ y) : A.obj x ≅≅ A.obj y :=
  Grpd.functorIsoOfIso (Functor.mapIso A (asIso f))

-- Note: this should not be a simp lemma, because we want simp to
-- see the Functor.Iso structure
def Grpd.Functor.iso_hom (A : Γ ⥤ Grpd) {x y : Γ} (f : x ⟶ y) :
  (iso A f).hom = A.map f := rfl

-- Note: this should not be a simp lemma, because we want simp to
-- see the Functor.Iso structure
def Grpd.Functor.iso_inv (A : Γ ⥤ Grpd) {x y : Γ} (f : x ⟶ y) :
  (iso A f).inv = A.map (inv f) := rfl

@[simp]
lemma Grpd.Functor.iso_id (A : Γ ⥤ Grpd) (x : Γ) : Grpd.Functor.iso A (𝟙 x) =
    Functor.Iso.refl _ := by
  ext
  simp [Grpd.id_eq_id, iso]

@[simp]
lemma Grpd.Functor.iso_comp (A : Γ ⥤ Grpd) {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    Grpd.Functor.iso A (f ≫ g) = Grpd.Functor.iso A f ≪⋙ Grpd.Functor.iso A g := by
  ext
  simp [Grpd.comp_eq_comp, iso]

@[simp]
lemma Grpd.Functor.iso_naturality (A : Γ ⥤ Grpd) (σ : Δ ⥤ Γ) {x y : Δ} (f : x ⟶ y) :
    Grpd.Functor.iso (σ ⋙ A) f = Grpd.Functor.iso A (σ.map f) := by
  ext
  simp [iso]

open Functor

lemma Grpd.Functor.hcongr_obj {C C' D D' : Grpd.{v,u}} (hC : C = C') (hD : D = D')
    {F : C ⥤ D} {F' : C' ⥤ D'} (hF : F ≍ F') {x} {x'} (hx : x ≍ x') :
    HEq (F.obj x) (F'.obj x') := by
  subst hC hD hF hx
  rfl

lemma Grpd.whiskerLeft_hcongr_right {C D : Type*} [Category C] [Category D]
    {E E' : Grpd.{v,u}} (hE : E ≍ E') (F : C ⥤ D) {G H : D ⥤ E} {G' H' : D ⥤ E'}
    (hG : G ≍ G') (hH : H ≍ H') {α : G ⟶ H} {α' : G' ⟶ H'} (hα : α ≍ α') :
    whiskerLeft F α ≍ whiskerLeft F α' := by
  subst hE hG hH hα
  rfl

lemma Grpd.comp_hcongr {C C' D D' E E' : Grpd.{v,u}} (hC : C ≍ C') (hD : D ≍ D')
    (hE : E ≍ E') {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    (hF : F ≍ F') (hG : G ≍ G')
    : F ⋙ G ≍ F' ⋙ G' := by
  subst hC hD hE hF hG
  rfl

lemma Grpd.NatTrans.hext {X X' Y Y' : Grpd.{v,u}} (hX : X = X') (hY : Y = Y')
    {F G : X ⥤ Y} {F' G' : X' ⥤ Y'} (hF : F ≍ F') (hG : G ≍ G')
    (α : F ⟶ G) (α' : F' ⟶ G') (happ : ∀ x : X, α.app x ≍ α'.app ((eqToHom hX).obj x)) :
    α ≍ α' := by
  subst hX hY hF hG
  aesop_cat

lemma Functor.associator_eq {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : associator F G H = CategoryTheory.Iso.refl _ :=
  rfl

section
variable {A B : Type*} [Category A] [Category B] (F : B ⥤ A)

-- NOTE to follow mathlib convention can use camelCase for definitions, and capitalised first letter when that definition is a Prop or Type
def IsSection (s : A ⥤ B) := s ⋙ F = Functor.id A

abbrev Section := ObjectProperty.FullSubcategory (IsSection F)

instance Section.category : Category (Section F) :=
  ObjectProperty.FullSubcategory.category (IsSection F)

abbrev Section.ι : Section F ⥤ (A ⥤ B) :=
  ObjectProperty.ι (IsSection F)

end

namespace ObjectProperty

lemma ι_mono {T C : Type u} [Category.{v} C] [Category.{v} T]
    {Z : C → Prop} (f g : T ⥤ FullSubcategory Z)
    (e : f ⋙ ι Z = g ⋙ ι Z) : f = g := by
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

instance {C : Type*} [Groupoid C] (P : ObjectProperty C) :
    Groupoid (P.FullSubcategory) :=
  InducedCategory.groupoid C (ObjectProperty.ι _).obj

instance Grpd.ι_mono (G : Grpd) (P : ObjectProperty G) : Mono (Grpd.homOf (ObjectProperty.ι P)) :=
  ⟨ fun _ _ e => ObjectProperty.ι_mono _ _ e ⟩

-- lemma Grpd.ObjectProperty.fullSubcategory_heq {A A' : Grpd.{v,u}} (hA : A ≍ A')
--     (P : ObjectProperty A) (P' : ObjectProperty A') (hP : ∀ x : A, P x ↔ P' (hA.elim x)) :
--     (⟨ ObjectProperty.FullSubcategory P, inferInstance ⟩ : Grpd) ≍
--     (⟨ ObjectProperty.FullSubcategory P', inferInstance ⟩ : Grpd) := by
--   subst hA
--   have : P = P' := by aesop
--   rw [this]

lemma Grpd.ObjectProperty.FullSubcategory.congr {A A' : Grpd.{v,u}} (hA : A ≍ A')
    (P : ObjectProperty A) (P' : ObjectProperty A') (hP : P ≍ P')
    (a : A) (a' : A') (ha : a ≍ a') (ha : P a) (ha' : P' a') :
    (⟨ a, ha ⟩ : P.FullSubcategory) ≍ (⟨ a', ha' ⟩ : P'.FullSubcategory) := by
  subst hA ha hP
  rfl

lemma Grpd.ObjectProperty.FullSubcategory.hext {A A' : Grpd.{v,u}} (hA : A ≍ A')
    (P : ObjectProperty A) (P' : ObjectProperty A') (hP : P ≍ P')
    (p : P.FullSubcategory) (p' : P'.FullSubcategory)
    (hp : p.obj ≍ p'.obj) : p ≍ p' := by
  cases p; cases p'
  subst hA hP hp
  rfl

end CategoryTheory

namespace GroupoidModel

open CategoryTheory NaturalModel Opposite Functor.Groupoidal

lemma smallU.PtpEquiv.fst_app_comp_map_tp {Γ : Ctx} (ab : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) :
    smallU.PtpEquiv.fst (ab ≫ smallU.Ptp.map smallU.tp) = smallU.PtpEquiv.fst ab := by
  dsimp[fst]
  --erw[fst_naturality]
  sorry

lemma smallU.PtpEquiv.snd_app_comp_map_tp {Γ : Ctx} (ab : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) :
    smallU.PtpEquiv.snd (ab ≫ smallU.Ptp.map smallU.tp)
    ≍ smallU.PtpEquiv.snd ab ⋙ PGrpd.forgetToGrpd :=
  sorry

end GroupoidModel

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModel Opposite Functor.Groupoidal

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp Functor.comp_id

namespace FunctorOperation
section

open CategoryTheory.Functor

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A B : Γ ⥤ Grpd.{v₁,u₁})

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

@[simp]
def conjugating' {x y : Γ} (f : x ⟶ y) : (A.obj x ⥤ B.obj x) ⥤
    (A.obj y ⥤ B.obj y) :=
  whiskeringLeftObjWhiskeringRightObj (A.map (inv f)) (B.map f)

def conjugating {x y : Γ} (f : x ⟶ y) : Grpd.of (A.obj x ⥤ B.obj x) ⟶
    Grpd.of (A.obj y ⥤ B.obj y) :=
  conjugating' A B f

lemma conjugating_obj {x y : Γ} (f : x ⟶ y) (s : A.obj x ⥤ B.obj x) :
    (conjugating A B f).obj s = A.map (inv f) ⋙ s ⋙ B.map f := by
  rfl

lemma conjugating_map {x y : Γ} (f : x ⟶ y) {s1 s2 : A.obj x ⥤ B.obj x} (h : s1 ⟶ s2) :
    (conjugating A B f).map h
    = whiskerRight (whiskerLeft (A.map (inv f)) h) (B.map f) := by
  rfl

@[simp] lemma conjugating_id (x : Γ) : conjugating A B (𝟙 x) = 𝟭 _ := by
  simp [conjugating]

@[simp] lemma conjugating_comp (x y z : Γ) (f : x ⟶ y) (g : y ⟶ z) :
    conjugating A B (f ≫ g) = conjugating A B f ⋙ conjugating A B g := by
  simp [conjugating]

@[simp] lemma conjugating_naturality_map {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)
    {x y} (f : x ⟶ y) : conjugating (σ ⋙ A) (σ ⋙ B) f = conjugating A B (σ.map f) := by
  simp [conjugating]

def conjugatingObjNatTransEquiv' {x y : Γ} (f : x ⟶ y) (S) (T) :
    ((Grpd.Functor.iso A f).inv ⋙ S ⋙ (Grpd.Functor.iso B f).hom ⟶ T) ≃
    (S ⋙ (Grpd.Functor.iso B f).hom ⟶ (Grpd.Functor.iso A f).hom ⋙ T) where
  toFun η := eqToHom (by simp) ≫ whiskerLeft (Grpd.Functor.iso A f).hom η
  invFun η := whiskerLeft (Grpd.Functor.iso A f).inv η ≫ eqToHom (by simp)
  left_inv η := by
    simp only [whiskerLeft_comp, whiskerLeft_eqToHom, whiskerLeft_twice, associator_eq,
      CategoryTheory.Iso.refl_inv, CategoryTheory.Iso.refl_hom, Category.comp_id, Category.assoc,
      ← heq_eq_eq, eqToHom_comp_heq_iff]
    rw! [Category.id_comp, comp_eqToHom_heq_iff]
    apply Functor.Iso.whiskerLeft_inv_hom_heq
  right_inv η := by
    simp only [whiskerLeft_comp, whiskerLeft_twice, associator_eq, CategoryTheory.Iso.refl_inv,
      CategoryTheory.Iso.refl_hom, Category.comp_id, whiskerLeft_eqToHom, Category.assoc, ←
      heq_eq_eq, eqToHom_comp_heq_iff]
    rw! [Category.id_comp, comp_eqToHom_heq_iff]
    apply Functor.Iso.whiskerLeft_hom_inv_heq

def conjugatingObjNatTransEquiv {x y : Γ} (f : x ⟶ y) (S) (T) :
    (A.map (inv f) ⋙ S ⋙ B.map f ⟶ T) ≃
    (S ⋙ B.map f ⟶ A.map f ⋙ T) := conjugatingObjNatTransEquiv' A B f S T

def conjugatingObjNatTransEquiv₁ {x y : Γ} (f : x ⟶ y) (S) (T) :
    (A.map (inv f) ⋙ S ⋙ B.map f ⟶ T) ≃
    (S ⋙ B.map f ≅ A.map f ⋙ T) := (conjugatingObjNatTransEquiv' A B f S T).trans
    (Groupoid.isoEquivHom (S ⋙ B.map f) (A.map f ⋙ T)).symm

end

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
  (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ)

-- NOTE: domain changed from sigmaObj, since we don't want to view domain as an object in `Grpd`
abbrev sigma.fstAuxObj : ∫ ι A x ⋙ B ⥤ A.obj x := forget

open sigma

def piObj : Grpd := Grpd.of (Section (fstAuxObj B x))

lemma piObj.hext {A A' : Γ ⥤ Grpd.{v,u}} (hA : A ≍ A') {B : ∫ A ⥤ Grpd.{v,u}}
    {B' : ∫ A' ⥤ Grpd.{v,u}} (hB : B ≍ B') (x : Γ)
    (f : piObj B x) (f' : piObj B' x) (hf : f.obj ≍ f'.obj) : f ≍ f' := by
  subst hA hB
  simp only [heq_eq_eq] at *
  unfold piObj Section Grpd.of Bundled.of
  ext
  rw [hf]

end

section
variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (B : ∫(A) ⥤ Grpd.{u₁,u₁})
variable {x y : Γ} (f: x ⟶ y)

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
    conjugating_obj, Functor.assoc, sigma_map, fstAuxObj]
  rw [sigmaMap_forget]
  convert_to (Grpd.Functor.iso A f).inv ⋙ (s.obj ⋙ fstAuxObj B x) ⋙ (Grpd.Functor.iso A f).hom = _
  rw [s.property]
  simp

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
  obj x := piObj B x
  map := piMap A B
  map_id := piMap_id A B
  map_comp := piMap_comp A B

end

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (B : ∫(A) ⥤ Grpd.{u₁,u₁})
  {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

theorem IsSection_eq (x) : sigma.fstAuxObj B (σ.obj x) ≍ sigma.fstAuxObj (pre A σ ⋙ B) x := by
  dsimp [sigma.fstAuxObj]
  rw [sigma_naturality_aux]

lemma piObj_naturality (x):
  piObj B (σ.obj x) = piObj (pre A σ ⋙ B) x := by
  dsimp [pi, piObj, sigma.fstAuxObj]
  rw [sigma_naturality_aux]

section

variable (x y : Δ)

lemma eqToHom_ι_aux :
    Grpd.of ((A.obj (σ.obj x)) ⥤ ∫(ι A (σ.obj x) ⋙ B))
    = Grpd.of (A.obj (σ.obj x) ⥤ ∫(ι (σ ⋙ A) x ⋙ pre A σ ⋙ B)) :=
  by rw [sigma_naturality_aux]

lemma ObjectProperty.eqToHom_comp_ι {C D : Grpd} (h : C = D) (P : ObjectProperty C)
    (Q : ObjectProperty D) (hP : P ≍ Q) :
    let h' : Grpd.of P.FullSubcategory = Grpd.of Q.FullSubcategory := by
      subst h hP; rfl
    eqToHom h' ⋙ (ObjectProperty.ι Q) = (ObjectProperty.ι P) ⋙ eqToHom h := by
  subst h hP; rfl

lemma eqToHom_ι' (x) :
    ObjectProperty.ι (IsSection (sigma.fstAuxObj (pre A σ ⋙ B) x)) ≍
    ObjectProperty.ι (IsSection (sigma.fstAuxObj B (σ.obj x))) := by
  dsimp [sigma.fstAuxObj]
  rw [sigma_naturality_aux]

lemma eqToHom_ι (x) :
    eqToHom (piObj_naturality A B σ x) ≫
    Grpd.homOf (ObjectProperty.ι (IsSection (sigma.fstAuxObj (pre A σ ⋙ B) x))) =
    Grpd.homOf (ObjectProperty.ι (IsSection (sigma.fstAuxObj B (σ.obj x)))) ≫
    eqToHom (eqToHom_ι_aux A B σ x) := by
  rw [← heq_eq_eq, eqToHom_comp_heq_iff, heq_comp_eqToHom_iff]
  apply eqToHom_ι'

end

section
variable  {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (P Q : ObjectProperty D)
  (F : C ⥤ D) (hF : ∀ X, P (F.obj X))

theorem FullSubcategory.lift_comp_inclusion_eq :
    P.lift F hF ⋙ P.ι = F :=
  rfl

end

lemma conjugating_naturality_sigma {x y} (f : x ⟶ y):
    conjugating (σ ⋙ A) (sigma (σ ⋙ A) (pre A σ ⋙ B)) f ≍
    conjugating A (sigma A B) (σ.map f) := by
  rw! [← sigma_naturality]
  rw [conjugating_naturality_map]

lemma eqToHom_conjugating {x y} (f : x ⟶ y):
    eqToHom (eqToHom_ι_aux A B σ x) ≫ conjugating (σ ⋙ A) (sigma (σ ⋙ A) (pre A σ ⋙ B)) f =
    conjugating A (sigma A B) (σ.map f) ≫ eqToHom (eqToHom_ι_aux A B σ y) := by
  rw [← heq_eq_eq, eqToHom_comp_heq_iff, heq_comp_eqToHom_iff]
  exact conjugating_naturality_sigma A B σ f

lemma comm_sq_of_comp_mono {C : Type*} [Category C]
    {X Y Z W X' Y' Z' W' : C}
    (f : X ⟶ Y) (h : X ⟶ W) (g : Y ⟶ Z) (i : W ⟶ Z)
    (f' : X' ⟶ Y') (h' : X' ⟶ W') (g' : Y' ⟶ Z') (i' : W' ⟶ Z')
    (mX : X ⟶ X') (mY : Y ⟶ Y') (mW : W ⟶ W') (mZ : Z ⟶ Z')
    (hbot : f' ≫ g' = h' ≫ i')
    (hf : f ≫ mY = mX ≫ f')
    (hh : h ≫ mW = mX ≫ h')
    (hg : g ≫ mZ = mY ≫ g')
    (hi : i ≫ mZ = mW ≫ i')
    [e : Mono mZ]
    : f ≫ g = h ≫ i := by
  apply e.right_cancellation
  calc (f ≫ g) ≫ mZ
    _ = f ≫ g ≫ mZ := by aesop
    _ = f ≫ mY ≫ g' := by aesop
    _ = (f ≫ mY) ≫ g' := by simp
    _  = (mX ≫ f') ≫ g' := by aesop
    _  = mX ≫ f' ≫ g' := by simp
    _  = mX ≫ h' ≫ i' := by aesop
    _  = (mX ≫ h') ≫ i' := by simp
    _  = (h ≫ mW) ≫ i' := by aesop
    _  = h ≫ mW ≫ i' := by simp
    _  = h ≫ i ≫ mZ := by aesop
    _  = (h ≫ i) ≫ mZ := by aesop

theorem pi_naturality_map {x y} (f : x ⟶ y) :
    Grpd.homOf (piMap A B (σ.map f)) ≫ eqToHom (piObj_naturality A B σ y)
    = eqToHom (piObj_naturality A B σ x) ≫ (Grpd.homOf (piMap (σ ⋙ A) (pre A σ ⋙ B) f)) := by
  apply comm_sq_of_comp_mono (e := Grpd.ι_mono (Grpd.of (_ ⥤ _))
      (IsSection (sigma.fstAuxObj (pre A σ ⋙ B) y)))
    (Grpd.homOf (piMap A B (σ.map f)))
    (eqToHom (piObj_naturality A B σ x))
    (eqToHom (piObj_naturality A B σ y)) (Grpd.homOf (piMap (σ ⋙ A) (pre A σ ⋙ B) f))
    (Grpd.homOf (conjugating A (sigma A B) (σ.map f)))
    (eqToHom (eqToHom_ι_aux A B σ x)) (eqToHom (eqToHom_ι_aux A B σ y))
    (Grpd.homOf (conjugating (σ ⋙ A) (sigma (σ ⋙ A) (pre A σ ⋙ B)) f))
    (Grpd.homOf (ObjectProperty.ι _))
    (Grpd.homOf (ObjectProperty.ι _))
    (Grpd.homOf (ObjectProperty.ι _))
    (Grpd.homOf (ObjectProperty.ι _))
  · rw [eqToHom_conjugating]
  · apply FunctorOperation.FullSubcategory.lift_comp_inclusion_eq
  · apply eqToHom_ι
  · apply eqToHom_ι
  · apply FunctorOperation.FullSubcategory.lift_comp_inclusion_eq

theorem pi_naturality : σ ⋙ pi A B = pi (σ ⋙ A) (pre A σ ⋙ B) := by
  fapply CategoryTheory.Functor.ext
  · apply piObj_naturality
  · intro x y f
    erw [← Category.assoc, ← pi_naturality_map]
    simp [- Grpd.comp_eq_comp, - Grpd.id_eq_id]

end

namespace pi

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{u₁,u₁}} (B : ∫(A) ⥤ Grpd.{u₁,u₁})
  (s : Γ ⥤ PGrpd.{u₁,u₁}) (hs : s ⋙ PGrpd.forgetToGrpd = pi A B)

def strongTrans.naturality {x y : Γ} (g : x ⟶ y) :
    A.map g ⋙ (PGrpd.objFiber' hs y).obj ≅ (PGrpd.objFiber' hs x).obj ⋙ sigmaMap B g :=
  let fib : A.map (CategoryTheory.inv g) ⋙ (PGrpd.objFiber' hs x).obj ⋙ (sigma A B).map g ⟶
      (PGrpd.objFiber' hs y).obj := PGrpd.mapFiber' hs g
  ((conjugatingObjNatTransEquiv₁ _ _ _ _ _).toFun fib).symm

@[simps]
def strongTrans : (A ⋙ Grpd.forgetToCat).toPseudoFunctor'.StrongTrans
  (sigma A B ⋙ Grpd.forgetToCat).toPseudoFunctor' where
    app x := (PGrpd.objFiber' hs x.as).obj
    naturality {x y} g := strongTrans.naturality B s hs g.as
    naturality_naturality := sorry
    naturality_id := sorry
    naturality_comp := sorry

def mapStrongTrans : ∫ A ⥤ ∫ sigma A B :=
  Functor.Grothendieck.toPseudoFunctor'Iso.hom _ ⋙
  Pseudofunctor.Grothendieck.map (strongTrans B s hs) ⋙
  Functor.Grothendieck.toPseudoFunctor'Iso.inv _

/--  Let `Γ` be a category.
For any pair of functors `A : Γ ⥤ Grpd` and `B : ∫(A) ⥤ Grpd`,
and any "term of pi", meaning a functor `f : Γ ⥤ PGrpd`
satisfying `f ⋙ forgetToGrpd = pi A B : Γ ⥤ Grpd`,
there is a "term of `B`" `inversion : Γ ⥤ PGrpd` such that `inversion ⋙ forgetToGrpd = B`.
-/
def inversion : ∫(A) ⥤ PGrpd := mapStrongTrans B s hs ⋙ sigma.assoc B ⋙ toPGrpd B

lemma mapStrongTrans_comp_fstAux' : mapStrongTrans B s hs ⋙ sigma.fstAux' B = 𝟭 _ := by
  apply Functor.Groupoidal.FunctorTo.hext
  · rw [Functor.assoc, sigma.fstAux', map_forget, mapStrongTrans, Functor.assoc,
      Functor.assoc, Functor.Groupoidal.forget,
      Functor.Grothendieck.toPseudoFunctor'Iso.inv_comp_forget,
      Pseudofunctor.Grothendieck.map_comp_forget, Functor.id_comp,
      Functor.Grothendieck.toPseudoFunctor'Iso.hom_comp_forget,
      Functor.Groupoidal.forget]
  · intro x
    simp only [sigma.fstAux', Functor.comp_obj, map_obj_fiber, sigma_obj, sigma.fstAux_app,
      Functor.Groupoidal.forget_obj, Functor.id_obj, heq_eq_eq]
    exact Functor.congr_obj (PGrpd.objFiber' hs x.base).property x.fiber
  · sorry

lemma inversion_comp_forgetToGrpd : inversion B s hs ⋙ PGrpd.forgetToGrpd = B :=
  calc mapStrongTrans B s hs ⋙ sigma.assoc B ⋙ toPGrpd B ⋙ PGrpd.forgetToGrpd
  _ = mapStrongTrans B s hs ⋙ (sigma.assoc B ⋙ forget) ⋙ B := by
    simp [toPGrpd_forgetToGrpd, Functor.assoc]
  _ = mapStrongTrans B s hs ⋙ sigma.fstAux' B ⋙ B := by rw [sigma.assoc_forget]
  _ = B := by simp [← Functor.assoc, mapStrongTrans_comp_fstAux']

-- JH: make some API for this? Mixture of Pseudofunctor.Grothendieck
-- and Functor.Grothendieck and Functor.Groupoidal is messy.
lemma ι_comp_inversion {x} : ι A x ⋙ inversion B s hs =
    (PGrpd.objFiber' hs x).obj ⋙ toPGrpd (ι A x ⋙ B) := by
  apply PGrpd.Functor.hext
  · simp only [Functor.assoc, inversion_comp_forgetToGrpd, toPGrpd_forgetToGrpd]
    rw [← Functor.assoc, (PGrpd.objFiber' hs x).property, Functor.id_comp]
  · intro a
    rfl -- This is probably bad practice
  · intro a b h
    sorry

end pi

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (β : ∫(A) ⥤ PGrpd.{u₁,u₁})

section
variable (x : Γ)

def lamObjFiberObj : Grpd.of (A.obj x ⥤ sigmaObj (β ⋙ PGrpd.forgetToGrpd) x) :=
  sec (ι A x ⋙ β ⋙ PGrpd.forgetToGrpd) (ι A x ⋙ β) rfl

@[simp] lemma lamObjFiberObj_obj_base (a) : ((lamObjFiberObj A β x).obj a).base = a := by
  simp [lamObjFiberObj]

@[simp] lemma lamObjFiberObj_obj_fiber (a) : ((lamObjFiberObj A β x).obj a).fiber
    = PGrpd.objFiber (ι A x ⋙ β) a := by
  simp [lamObjFiberObj]

@[simp] lemma lamObjFiberObj_map_base {a a'} (h: a ⟶ a'):
    ((lamObjFiberObj A β x).map h).base = h := by
  simp [lamObjFiberObj]

@[simp] lemma lamObjFiberObj_map_fiber {a a'} (h: a ⟶ a'):
    ((lamObjFiberObj A β x).map h).fiber = PGrpd.mapFiber (ι A x ⋙ β) h := by
  simp [lamObjFiberObj]

def lamObjFiber : piObj (β ⋙ PGrpd.forgetToGrpd) x :=
  ⟨lamObjFiberObj A β x , rfl⟩

@[simp] lemma lamObjFiber_obj : (lamObjFiber A β x).obj = lamObjFiberObj A β x :=
  rfl

@[simp] lemma lamObjFiber_obj_obj : (lamObjFiber A β x).obj = lamObjFiberObj A β x :=
  rfl

end

section
variable {x y : Γ} (f : x ⟶ y)

open CategoryTheory.Functor

def lamObjFiberObjCompSigMap.app (a : A.obj x) :
    (lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f).obj a ⟶
    (A.map f ⋙ lamObjFiberObj A β y).obj a :=
  homMk (𝟙 _) (eqToHom (by simp; rfl) ≫ (β.map ((ιNatTrans f).app a)).fiber)

@[simp] lemma lamObjFiberObjCompSigMap.app_base (a : A.obj x) : (app A β f a).base = 𝟙 _ := by
  simp [app]

lemma lamObjFiberObjCompSigMap.app_fiber_eq (a : A.obj x) : (app A β f a).fiber =
    eqToHom (by simp; rfl) ≫ (β.map ((ιNatTrans f).app a)).fiber := by
  simp [app]

lemma lamObjFiberObjCompSigMap.app_fiber_heq (a : A.obj x) : (app A β f a).fiber ≍
    (β.map ((ιNatTrans f).app a)).fiber := by
  simp [app]

lemma lamObjFiberObjCompSigMap.naturality {x y : Γ} (f : x ⟶ y) {a1 a2 : A.obj x} (h : a1 ⟶ a2) :
    (lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f).map h
    ≫ lamObjFiberObjCompSigMap.app A β f a2 =
    lamObjFiberObjCompSigMap.app A β f a1
    ≫ (A.map f ⋙ lamObjFiberObj A β y).map h := by
  apply Hom.hext
  · simp [sigmaObj]
  · have β_ιNatTrans_naturality : β.map ((ι A x).map h) ≫ β.map ((ιNatTrans f).app a2)
        = β.map ((ιNatTrans f).app a1) ≫ β.map ((A.map f ⋙ ι A y).map h) := by
      simp [← Functor.map_comp, (ιNatTrans f).naturality h]
    have h_naturality : (β.map ((ιNatTrans f).app a2)).base.map (β.map ((ι A x).map h)).fiber
        ≫ (β.map ((ιNatTrans f).app a2)).fiber ≍
        (β.map ((ι A y).map ((A.map f).map h))).base.map (β.map ((ιNatTrans f).app a1)).fiber
        ≫ (β.map ((ι A y).map ((A.map f).map h))).fiber := by
      simpa [← heq_eq_eq] using Grothendieck.Hom.congr β_ιNatTrans_naturality
    simp only [Grpd.forgetToCat.eq_1, sigmaObj, Grpd.coe_of, comp_obj, sigmaMap_obj_base,
      Functor.comp_map, comp_base, sigmaMap_map_base, sigmaMap_obj_fiber, comp_fiber,
      sigmaMap_map_fiber, lamObjFiberObj_map_fiber, map_comp, eqToHom_map, app_fiber_eq, Cat.of_α,
      id_eq, Category.assoc, eqToHom_trans_assoc, heq_eqToHom_comp_iff, eqToHom_comp_heq_iff]
    rw [← Category.assoc]
    apply HEq.trans _ h_naturality
    apply heq_comp _ rfl rfl _ HEq.rfl
    · aesop_cat
    · simp only [← Functor.comp_map, ← Grpd.comp_eq_comp, comp_eqToHom_heq_iff]
      congr 3
      aesop_cat

@[simp] lemma lamObjFiberObjCompSigMap.app_id (a) : lamObjFiberObjCompSigMap.app A β (𝟙 x) a
    = eqToHom (by simp) := by
  apply Hom.hext
  · rw [base_eqToHom]
    simp
  · simp [app]
    rw! (castMode := .all) [ιNatTrans_id_app, fiber_eqToHom]
    simp [Grothendieck.Hom.congr (eqToHom_map β _), Functor.Grothendieck.fiber_eqToHom,
      eqToHom_trans]
    apply (eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm

lemma lamObjFiberObjCompSigMap.app_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) (a) :
    app A β (f ≫ g) a
    = eqToHom (by simp)
    ≫ (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g).map (app A β f a)
    ≫ app A β g ((A.map f).obj a) ≫ eqToHom (by simp) := by
  fapply Hom.hext
  · simp only [Grpd.forgetToCat.eq_1, sigmaObj, Grpd.coe_of, comp_obj, sigmaMap_obj_base, app_base,
    comp_base, base_eqToHom, sigmaMap_map_base, map_id, lamObjFiberObj_obj_base, map_comp,
    Grpd.comp_eq_comp, eqToHom_naturality, Category.comp_id, eqToHom_trans, eqToHom_refl]
  · have : (β.map ((ιNatTrans (f ≫ g)).app a)) = β.map ((ιNatTrans f).app a)
      ≫ β.map ((ιNatTrans g).app ((A.map f).obj a))
      ≫ eqToHom (by simp) := by
      simp [ιNatTrans_comp_app]
    simp only [Grpd.forgetToCat.eq_1, sigmaObj, Grpd.coe_of, comp_obj, sigmaMap_obj_base, app,
      Functor.comp_map, PGrpd.forgetToGrpd_map, sigmaMap_obj_fiber, Cat.of_α, id_eq, homMk_base,
      homMk_fiber, Grothendieck.Hom.congr this, Grothendieck.Hom.comp_base, Grpd.comp_eq_comp,
      Grothendieck.Hom.comp_fiber, eqToHom_refl, Functor.Grothendieck.fiber_eqToHom,
      Category.id_comp, eqToHom_trans_assoc, comp_base, sigmaMap_map_base, comp_fiber,
      fiber_eqToHom, eqToHom_map, sigmaMap_map_fiber, map_comp, Category.assoc,
      heq_eqToHom_comp_iff, eqToHom_comp_heq_iff]
    have : ((ιNatTrans g).app ((A.map f).obj a)) = homMk g (𝟙 _) := by
      apply Hom.ext _ _ (by simp) (by aesop_cat)
    rw! [Category.id_comp, base_eqToHom, eqToHom_map, eqToHom_map,
      Functor.Grothendieck.base_eqToHom, ιNatTrans_app_base, this]
    aesop_cat

def lamObjFiberObjCompSigMap :
    lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⟶
    A.map f ⋙ lamObjFiberObj A β y where
  app := lamObjFiberObjCompSigMap.app A β f
  naturality _ _ h := lamObjFiberObjCompSigMap.naturality A β f h

@[simp] lemma lamObjFiberObjCompSigMap_id (x : Γ) : lamObjFiberObjCompSigMap A β (𝟙 x) =
    eqToHom (by simp [sigmaMap_id]) := by
  ext a
  simp [lamObjFiberObjCompSigMap]

/-
lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) (f ≫ g)

_ ⟶ lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) g
:= eqToHom ⋯

_ ⟶ A.map f ⋙ lamObjFiberObj A β y ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) g
:= whiskerRight (lamObjFiberObjCompSigMap A β f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)

_ ⟶ A.map f ⋙ A.map g ⋙ lamObjFiberObj A β z
:= whiskerLeft (A.map f) (lamObjFiberObjCompSigMap A β g)

_ ⟶ A.map (f ≫ g) ⋙ lamObjFiberObj A β z
:= eqToHom ⋯

-/
lemma lamObjFiberObjCompSigMap_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    lamObjFiberObjCompSigMap A β (f ≫ g) =
    eqToHom (by rw [sigmaMap_comp]; rfl)
    ≫ whiskerRight (lamObjFiberObjCompSigMap A β f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)
    ≫ whiskerLeft (A.map f) (lamObjFiberObjCompSigMap A β g)
    ≫ eqToHom (by rw [Functor.map_comp, Grpd.comp_eq_comp, Functor.assoc]) := by
  ext a
  simp [lamObjFiberObjCompSigMap, lamObjFiberObjCompSigMap.app_comp]

def whiskerLeftInvLamObjObjSigMap :
    A.map (CategoryTheory.inv f) ⋙ lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⟶
    lamObjFiberObj A β y :=
  whiskerLeft (A.map (CategoryTheory.inv f)) (lamObjFiberObjCompSigMap A β f)
  ≫ eqToHom (by simp [← Grpd.comp_eq_comp])

@[simp] lemma whiskerLeftInvLamObjObjSigMap_id (x : Γ) :
    whiskerLeftInvLamObjObjSigMap A β (𝟙 x) = eqToHom (by simp [sigmaMap_id]) := by
  simp [whiskerLeftInvLamObjObjSigMap]

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

lemma whiskerLeftInvLamObjObjSigMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    whiskerLeftInvLamObjObjSigMap A β (f ≫ g)
    = eqToHom (by simp [Functor.assoc, sigmaMap_comp])
    ≫ whiskerRight (whiskerLeft (A.map (CategoryTheory.inv g))
      (whiskerLeftInvLamObjObjSigMap A β f)) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)
    ≫ whiskerLeftInvLamObjObjSigMap A β g := by
  simp only [whiskerLeftInvLamObjObjSigMap, lamObjFiberObjCompSigMap_comp]
  have hAfg : A.map (CategoryTheory.inv (f ≫ g)) = (Grpd.Functor.iso A g).inv ≫
    (Grpd.Functor.iso A f).inv := by simp [Grpd.Functor.iso]
  rw! (castMode := .all) [hAfg]
  erw [whiskerLeftInvLamObjObjSimgaMap_comp_aux (Grpd.Functor.iso A f) (Grpd.Functor.iso A g)
    _ _ _ (sigmaMap (β ⋙ PGrpd.forgetToGrpd) f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)]
  simp only [Category.assoc, eqToHom_trans, Grpd.Functor.iso_hom, Grpd.Functor.iso_inv]

def lamMapFiber :
    ((pi A (β ⋙ PGrpd.forgetToGrpd)).map f).obj (lamObjFiber A β x) ⟶ lamObjFiber A β y :=
  whiskerLeftInvLamObjObjSigMap A β f

@[simp] lemma lamMapFiber_id (x : Γ) : lamMapFiber A β (𝟙 x) = eqToHom (by simp) := by
  simp [lamMapFiber]
  rfl

lemma lamMapFiber_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    lamMapFiber A β (f ≫ g)
    = eqToHom (by rw [← Functor.comp_obj]; apply Functor.congr_obj; simp [piMap_comp])
    ≫ ((piMap A (β ⋙ PGrpd.forgetToGrpd)) g).map ((lamMapFiber A β) f)
    ≫ lamMapFiber A β g := by
  simp [lamMapFiber, piMap, whiskerLeftInvLamObjObjSigMap_comp]
  rfl

def lam : Γ ⥤ PGrpd.{u₁,u₁} :=
  PGrpd.functorTo
  (pi A (β ⋙ PGrpd.forgetToGrpd))
  (lamObjFiber A β)
  (lamMapFiber A β)
  (lamMapFiber_id A β)
  (lamMapFiber_comp A β)

@[simp]
lemma lam_obj_base (x) : ((lam A β).obj x).base = piObj (β ⋙ PGrpd.forgetToGrpd) x := rfl

@[simp]
lemma lam_obj_fib (x) : ((lam A β).obj x).fiber = lamObjFiber A β x :=
  rfl

@[simp]
lemma lam_map_base {x y} (f : x ⟶ y) : ((lam A β).map f).base =
    piMap A (β ⋙ PGrpd.forgetToGrpd) f :=
  rfl

@[simp]
lemma lam_map_fib {x y} (f : x ⟶ y) : ((lam A β).map f).fiber = lamMapFiber A β f :=
  rfl

lemma lam_comp_forgetToGrpd : lam A β ⋙ PGrpd.forgetToGrpd = pi A (β ⋙ PGrpd.forgetToGrpd) :=
  rfl

variable {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

lemma lam_naturality_aux (x) :
    ι A (σ.obj x) ⋙ β ⋙ PGrpd.forgetToGrpd = ι (σ ⋙ A) x ⋙ pre A σ ⋙ β ⋙ PGrpd.forgetToGrpd := by
  simp [← Functor.assoc, ← ι_comp_pre]

lemma lamObjFiberObj_naturality (x) :
    lamObjFiberObj A β (σ.obj x) ≍ lamObjFiberObj (σ ⋙ A) (pre A σ ⋙ β) x := by
  simp only [lamObjFiberObj, ← ι_comp_pre, comp_obj, Functor.assoc]
  congr!

lemma lam_naturality_obj_aux (x) :
    Grpd.of (A.obj (σ.obj x) ⥤ sigmaObj (β ⋙ PGrpd.forgetToGrpd) (σ.obj x)) ≍
    Grpd.of (A.obj (σ.obj x) ⥤ sigmaObj ((pre A σ ⋙ β) ⋙ PGrpd.forgetToGrpd) x) := by
  rw [sigmaObj_naturality, Functor.assoc]

theorem lam_naturality_obj (x : Δ) : HEq (lamObjFiber A β (σ.obj x))
    (lamObjFiber (σ ⋙ A) (pre A σ ⋙ β) x) := by
  simp only [lamObjFiber]
  apply Grpd.ObjectProperty.FullSubcategory.hext (lam_naturality_obj_aux A β σ x)
  · simp only [sigma.fstAuxObj, Functor.assoc]
    congr!
    any_goals simp [lam_naturality_aux]
  · apply lamObjFiberObj_naturality

lemma lamObjFiberObjCompSigMap.app_naturality {x y} (f : x ⟶ y) (a) :
    lamObjFiberObjCompSigMap.app A β (σ.map f) a ≍
    lamObjFiberObjCompSigMap.app (σ ⋙ A) (pre A σ ⋙ β) f a := by
  apply Hom.hext'
  any_goals apply Grpd.Functor.hcongr_obj
  any_goals apply Grpd.comp_hcongr
  any_goals simp only [comp_obj, Functor.comp_map, heq_eq_eq]
  any_goals apply sigmaObj_naturality
  any_goals apply lam_naturality_aux
  any_goals apply sigmaMap_naturality_heq
  any_goals apply lamObjFiberObj_naturality
  any_goals simp [app]; rfl

lemma lamObjFiberObjCompSigMap_naturality {x y} (f : x ⟶ y) :
    lamObjFiberObjCompSigMap A β (σ.map f) ≍
    lamObjFiberObjCompSigMap (σ ⋙ A) (pre A σ ⋙ β) f := by
  apply Grpd.NatTrans.hext
  any_goals apply Grpd.comp_hcongr
  any_goals simp only [comp_obj, Functor.comp_map, heq_eq_eq, eqToHom_refl]
  any_goals apply sigmaObj_naturality
  any_goals apply lamObjFiberObj_naturality
  · apply sigmaMap_naturality_heq
  · apply lamObjFiberObjCompSigMap.app_naturality

lemma whiskerLeftInvLamObjObjSigMap_naturality_heq {x y} (f : x ⟶ y) :
    whiskerLeftInvLamObjObjSigMap A β (σ.map f) ≍
    whiskerLeftInvLamObjObjSigMap (σ ⋙ A) (pre A σ ⋙ β) f := by
  simp only [whiskerLeftInvLamObjObjSigMap, Functor.comp_map]
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans _ (comp_eqToHom_heq _ _).symm
  rw [Functor.map_inv, Functor.map_inv, Functor.map_inv]
  apply Grpd.whiskerLeft_hcongr_right
  any_goals apply Grpd.comp_hcongr
  any_goals simp only [comp_obj, heq_eq_eq]
  any_goals apply sigmaObj_naturality
  any_goals apply lamObjFiberObj_naturality
  · apply sigmaMap_naturality_heq
  · apply lamObjFiberObjCompSigMap_naturality

lemma lam_naturality_map {x y} (f : x ⟶ y) :
    lamMapFiber A β (σ.map f) ≍ lamMapFiber (σ ⋙ A) (pre A σ ⋙ β) f := by
  apply whiskerLeftInvLamObjObjSigMap_naturality_heq

theorem lam_naturality : σ ⋙ lam A β = lam (σ ⋙ A) (pre A σ ⋙ β)
     := by
  apply PGrpd.Functor.hext
  · apply pi_naturality
  · apply lam_naturality_obj
  · apply lam_naturality_map

end

section

variable (B : ∫ A ⥤ Grpd) (s : Γ ⥤ PGrpd) (hs : s ⋙ PGrpd.forgetToGrpd = pi A B)

lemma lamObjFiberObj_inversion_heq (x) :
    lamObjFiberObj A (pi.inversion B s hs) x ≍ (PGrpd.objFiber' hs x).obj := by
  dsimp only [lamObjFiberObj]
  rw! [pi.inversion_comp_forgetToGrpd B s hs]
  simp only [sec_eq_lift, Grpd.forgetToCat.eq_1, heq_eq_eq]
  symm
  apply Functor.IsPullback.lift_uniq
  · symm
    apply pi.ι_comp_inversion
  · exact (PGrpd.objFiber' hs x).property

lemma lamObjFiber_inversion_heq' (x) :
    lamObjFiber A (pi.inversion B s hs) x ≍ PGrpd.objFiber' hs x := by
  dsimp [pi_obj]
  apply piObj.hext
  · rfl
  · simp [pi.inversion_comp_forgetToGrpd]
  · apply lamObjFiberObj_inversion_heq

lemma lamObjFiber_inversion_heq (x) :
    lamObjFiber A (pi.inversion B s hs) x ≍ PGrpd.objFiber s x :=
  HEq.trans (lamObjFiber_inversion_heq' A B s hs x) (PGrpd.objFiber'_heq hs)

lemma lamMapFiber_inversion_heq {x y} (f : x ⟶ y) :
    lamMapFiber A (pi.inversion B s hs) f ≍ PGrpd.mapFiber s f :=
  sorry

lemma pi.eta : lam A (inversion B s hs) = s := by
  apply PGrpd.Functor.hext -- TODO: rename to PGrpd.ToFunctor.hext
  · rw [lam_comp_forgetToGrpd, inversion_comp_forgetToGrpd, hs]
  · apply lamObjFiber_inversion_heq
  · apply lamMapFiber_inversion_heq

end

end
end FunctorOperation

section
variable {Γ : Ctx}

namespace smallUPi

open FunctorOperation

def Pi_app (AB : y(Γ) ⟶ smallU.{v}.Ptp.obj smallU.{v}.Ty) :
    y(Γ) ⟶ smallU.{v}.Ty :=
  --by
  --#check (smallU.PtpEquiv.fst AB)
 -- #check (smallU.PtpEquiv.snd AB)
  yonedaCategoryEquiv.symm (pi _ (smallU.PtpEquiv.snd AB))

def Pi_naturality {Δ Γ} (f : Δ ⟶ Γ) (α : y(Γ) ⟶ smallU.Ptp.obj smallU.Ty) :
    Pi_app (ym(f) ≫ α) = ym(f) ≫ Pi_app α := by
  dsimp only [Pi_app]
  rw [← yonedaCategoryEquiv_symm_naturality_left, pi_naturality,
    smallU.PtpEquiv.snd_comp_left]
  rw! [smallU.PtpEquiv.fst_comp_left]
  simp [map_id_eq, Functor.id_comp]

/-- The formation rule for Π-types for the natural model `smallU` -/
def Pi : smallU.{v}.Ptp.obj smallU.{v}.Ty ⟶ smallU.{v}.Ty :=
  NatTrans.yonedaMk Pi_app Pi_naturality

lemma Pi_app_eq {Γ : Ctx} (ab : y(Γ) ⟶ _) : ab ≫ Pi =
    yonedaCategoryEquiv.symm (FunctorOperation.pi _ (smallU.PtpEquiv.snd ab)) := by
  rw [Pi, NatTrans.yonedaMk_app, Pi_app]

def lam_app (ab : y(Γ) ⟶ smallU.{v}.Ptp.obj smallU.{v}.Tm) :
    y(Γ) ⟶ smallU.{v}.Tm :=
  yonedaCategoryEquiv.symm (lam _ (smallU.PtpEquiv.snd ab))

open smallU.PtpEquiv

def lam_naturality {Δ Γ} (f : Δ ⟶ Γ) (α : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) :
    lam_app (ym(f) ≫ α) = ym(f) ≫ lam_app α := by
  dsimp only [lam_app]
  rw [← yonedaCategoryEquiv_symm_naturality_left, FunctorOperation.lam_naturality]
  rw! [snd_comp_left, fst_comp_left]
  simp [map_id_eq]

/-- The introduction rule for Π-types for the natural model `smallU` -/
def lam : smallU.{v}.Ptp.obj smallU.{v}.Tm ⟶ smallU.{v}.Tm :=
  NatTrans.yonedaMk lam_app lam_naturality

lemma lam_app_eq {Γ : Ctx} (ab : y(Γ) ⟶ smallU.Ptp.obj smallU.Tm) : ab ≫ lam =
    yonedaCategoryEquiv.symm (FunctorOperation.lam _ (smallU.PtpEquiv.snd ab)) := by
  rw [lam, NatTrans.yonedaMk_app, lam_app]


/-lemma smallUSig.pair_app_eq {Γ : Ctx} (ab : y(Γ) ⟶ _) : ab ≫ smallUSig.pair =
    yonedaCategoryEquiv.symm (FunctorOperation.pair _ _ _ (snd_forgetToGrpd ab)) := by
  simp only [smallUSig.pair, smallUSig.pair_app, NatTrans.yonedaMk_app]

namespace SigPullback

open Limits

section

theorem smallUSig.pair_tp : smallUSig.pair.{v} ≫ smallU.{v}.tp =
    smallU.comp.{v} ≫ smallUSig.Sig.{v} := by
  apply hom_ext_yoneda
  intros Γ ab
  rw [← Category.assoc, ← Category.assoc, smallUSig.pair_app_eq,
    smallUSig.Sig_app_eq, smallU_tp, π,
    ← yonedaCategoryEquiv_symm_naturality_right,
    pair_comp_forgetToGrpd, smallUSig.Sig_app]
  congr 2
  · rw [fst_forgetToGrpd]
  · exact dependent_heq.{v} ab
-/

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
  (s : y(Γ) ⟶ y(E.{v})) (hs : s ≫ ym(π) = AB ≫ smallUPi.Pi)

include hs in
theorem yonedaCategoryEquiv_forgetToGrpd : yonedaCategoryEquiv s ⋙ PGrpd.forgetToGrpd
    = pi (smallU.PtpEquiv.fst AB) (smallU.PtpEquiv.snd AB) := by
  erw [← yonedaCategoryEquiv_naturality_right, hs]
  rw [smallUPi.Pi_app_eq, yonedaCategoryEquiv.apply_symm_apply]

def lift : y(Γ) ⟶ smallU.Ptp.obj.{v} smallU.Tm.{v} :=
  have hs' : yonedaCategoryEquiv s ⋙ PGrpd.forgetToGrpd = pi (fst AB) (snd AB) := by
    erw [← yonedaCategoryEquiv_naturality_right, hs]
    rw [Pi_app_eq, yonedaCategoryEquiv.apply_symm_apply]
  mk (fst AB) (pi.inversion (snd AB) (yonedaCategoryEquiv s) hs')

theorem fac_left : lift.{v} AB s hs ≫ lam.{v} = s := by
  rw [lam_app_eq, yonedaCategoryEquiv.symm_apply_eq]
  dsimp only [lift]
  conv => left; right; rw! [smallU.PtpEquiv.snd_mk]
  rw! [smallU.PtpEquiv.fst_mk]
  simp [map_id_eq, pi.eta]

theorem fac_right : lift.{v} AB s hs ≫ smallU.Ptp.{v}.map smallU.tp = AB := by
  apply smallU.PtpEquiv.hext
  · sorry
  · sorry

theorem hom_ext (m n : y(Γ) ⟶ smallU.Ptp.{v}.obj smallU.Tm.{v})
    (hMap : m ≫ smallU.Ptp.{v}.map smallU.tp.{v} = n ≫ smallU.Ptp.{v}.map smallU.tp.{v})
    (hLam : m ≫ lam.{v} = n ≫ lam) : m = n := by
    sorry

end

-- TODO: is this the best way to do universe levels?
theorem isPullback : IsPullback lam.{v, max u (v+1)}
    (smallU.Ptp.{v, max u (v+1)}.map smallU.tp.{v, max u (v+1)})
    smallU.{v, max u (v+1)}.tp Pi.{v, max u (v+1)} :=
  Limits.RepPullbackCone.is_pullback lam_tp
    (fun s => lift.{v, max u (v+1)} s.snd s.fst s.condition)
    (fun s => fac_left.{v, max u (v+1)} s.snd s.fst s.condition)
    (fun s => fac_right.{v, max u (v+1)} s.snd s.fst s.condition)
    (fun s m hml hmr =>
      hom_ext.{v, max u (v+1)} m (lift.{v, max u (v+1)} s.snd s.fst s.condition)
      (by rw [hmr, fac_right.{v, max u (v+1)}]) (by rw [hml, fac_left.{v, max u (v+1)}]))

end smallUPi

def smallUPi : Pi smallU.{v} where
  Pi := smallUPi.Pi.{v}
  lam := smallUPi.lam.{v}
  Pi_pullback := smallUPi.isPullback.{v}

def uHomSeqPis' (i : ℕ) (ilen : i < 4) :
  Pi (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUPi.{0,4}
  | 1 => smallUPi.{1,4}
  | 2 => smallUPi.{2,4}
  | 3 => smallUPi.{3,4}
  | (n+4) => by omega

def uHomSeqPiSig : UHomSeqPiSig Ctx := { uHomSeq with
  nmPi := uHomSeqPis'
  nmSig := uHomSeqSigs' }

end

end GroupoidModel
