import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Russell_PER_MS.NaturalModel

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
namespace CategoryTheory

section
variable {A B C D E: Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
-- NOTE is there a better way of doing this?
-- NOTE associativity of functors is definitional, so we can always use `rfl`
lemma func_middle_assoc
    (f1: A ⥤ B) (f2: B ⥤ C) (f3: C ⥤ D) (f4: D ⥤ E):
  f1 ⋙ f2 ⋙ f3 ⋙ f4 = f1 ⋙ (f2 ⋙ f3) ⋙ f4 := rfl

lemma func_split_assoc
    (f1: A ⥤ B) (f2: B ⥤ C) (f3: C ⥤ D) (f4: D ⥤ E):
  f1 ⋙ (f2 ⋙ f3) ⋙ f4 = (f1 ⋙ f2) ⋙ (f3 ⋙ f4) := rfl

end

lemma whiskeringLeft_Right_comm {A B C D: Type*} [Category A] [Category B]
    [Category C] [Category D] (F: A⥤ B)  (H: C ⥤ D):
    (whiskeringRight _ _ _).obj H ⋙ (whiskeringLeft  _ _ _ ).obj F =
    (whiskeringLeft _ _ _).obj F ⋙ (whiskeringRight _ _ _).obj H := by
  aesop_cat

section
variable {A : Type u} [Category.{v} A] {B: Type u₁} [Groupoid.{v₁} B]
    {F G : A ⥤ B} (h : NatTrans F G)

-- NOTE not sure if this is the best way to organize this
@[simps] def NatTrans.iso : F ≅ G where
  hom := h
  inv := {app a := Groupoid.inv (h.app a)}

def NatTrans.inv : G ⟶ F := h.iso.inv

@[simp] lemma NatTrans.inv_vcomp : h.inv.vcomp h = NatTrans.id G := by
  ext a
  simp [NatTrans.inv]

@[simp] lemma NatTrans.vcomp_inv : h.vcomp h.inv = NatTrans.id F := by
  ext a
  simp [NatTrans.inv]

end

namespace ObjectProperty
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

section

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  (F : C ⥤ A) (G : B ⥤ D)

/--
The functor that, on objects `H : A ⥤ B` acts by
composing left and right with functors `F ⋙ H ⋙ G`
         F
   A <---------  C
   |             .
   |             |
   |             .
H  |             | whiskeringLeftObjWhiskeringRightObj.obj H
   |             .
   V             V
   B ----------> D
         G
-/
def whiskeringLeftObjWhiskeringRightObj : (A ⥤ B) ⥤ (C ⥤ D) :=
  (whiskeringLeft C A B).obj F ⋙ (whiskeringRight C B D).obj G

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_obj (S : A ⥤ B) :
    (whiskeringLeftObjWhiskeringRightObj F G).obj S
    = F ⋙ S ⋙ G := by
  simp [whiskeringLeftObjWhiskeringRightObj, Functor.assoc]

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_id_id :
    whiskeringLeftObjWhiskeringRightObj (𝟭 A) (𝟭 B) = 𝟭 (A ⥤ B) :=
  rfl

@[simp] lemma whiskeringLeftObjWhiskeringRightObj_comp_comp {C' D' : Type*} [Category C']
    [Category D'] (F' : C' ⥤ C) (G' : D ⥤ D') :
    whiskeringLeftObjWhiskeringRightObj (F' ⋙ F) (G ⋙ G')
    = whiskeringLeftObjWhiskeringRightObj F G ⋙ whiskeringLeftObjWhiskeringRightObj F' G' :=
  rfl

end
end CategoryTheory

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck  Groupoid


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

instance functorToGroupoid_Groupoid {A : Type*} [Category A] {B : Type*} [Groupoid B] :
    Groupoid (A ⥤ B) where
  inv nt := nt.inv
  inv_comp := NatTrans.inv_vcomp
  comp_inv := NatTrans.vcomp_inv

-- NOTE commented out until it is needed
-- def Funcgrpd {A : Type u} [Category.{v,u} A] {B : Type u₁} [Groupoid.{v₁} B]  : Grpd :=
--  Grpd.of (A ⥤ B)

namespace FunctorOperation
section

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
  whiskeringLeftObjWhiskeringRightObj (A.map (Groupoid.inv f)) (B.map f)

@[simp] lemma conjugating_obj {x y : Γ} (f : x ⟶ y) (s : A.obj x ⥤ B.obj x) :
    (conjugating A B f).obj s = CategoryTheory.inv (A.map f) ⋙ s ⋙ B.map f := by
  simp [conjugating, Functor.assoc]

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

-- since Section is an abbrev we don't actually need these
-- three lemmas
-- @[simp] lemma Section.ι_obj (s: Section F) :
--   (Section.ι F).obj s = s.obj := rfl
-- @[simp] lemma Section.inc_map (s1 s2: Section F) (η : s1 ⟶ s2) :
--   (Section.ι F).map η = η := rfl
-- lemma Section.ι_eq (s1 s2: Section F) (η₁ η₂ : s1 ⟶ s2) :
--     (Section.ι F).map η₁ = (Section.ι F).map η₂ → η₁ = η₂ := by
--   simp

instance Section.groupoid {B : Type*} [Groupoid B] (F : B ⥤ A) :
    Groupoid (Section F) :=
  InducedCategory.groupoid (A ⥤ B) (fun (f: Section F) ↦ f.obj)

end
end FunctorOperation

-- --Q:Should this be def or abbrev? JH: abbrev I think?
-- abbrev Section.grpd {A:Type u} [Category.{v ,u} A] {B : Type u₁}
--     [Groupoid.{v₁} B] (F : B ⥤ A) : Grpd :=
--   Grpd.of (Section F)

open FunctorOperation

section

variable {Γ : Type*} [Category Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
  (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ)

-- NOTE: JH changed this to be
def piObj : Type _ := Section ((fstAux B).app x)

instance piObj.groupoid : Groupoid (piObj B x) :=
  inferInstanceAs (Groupoid (Section ((fstAux B).app x)))

end

-- lemma fiberGrpd.α {Γ : Type*} [Category Γ] (A : Γ ⥤ Grpd.{v₁,u₁})
--     (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ) :
--     (Grpd.of $ fiberGrpd A B x).α = Section ((fstAux B).app x) := rfl

def conjugate {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    {x y: C} (f: x ⟶ y) (s: A.obj x ⟶  B.obj x) :
     A.obj y ⟶  B.obj y := A.map (Groupoid.inv f) ≫ s ≫ B.map f

lemma conjugate_id {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    (x : C) (s: A.obj x ⟶  B.obj x)  : conjugate C A B (𝟙 x) s = s:= by
     simp only [conjugate, inv_eq_inv, IsIso.inv_id, CategoryTheory.Functor.map_id,
       Category.comp_id, Category.id_comp]

lemma conjugate_comp {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    {x y z: C} (f: x ⟶ y) (g: y ⟶ z) (s: A.obj x ⟶  B.obj x):
     conjugate C A B (f ≫ g) s = conjugate C A B g (conjugate C A B f s) := by
      simp only [conjugate, inv_eq_inv, IsIso.inv_comp, Functor.map_comp, Functor.map_inv,
        Category.assoc]

/-only need naturality of η-/
/-therefore, the fact that the conjugation sends section to section is by naturality of
 the projection map from sigma, and the fact that some functor has sections as its codomain-/
lemma conjugate_PreserveSection {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    (η: NatTrans B A)
    {x y: C} (f: x ⟶ y) (s: A.obj x ⟶  B.obj x):
    s ≫ η.app x = 𝟙 (A.obj x) → (conjugate C A B f s) ≫ η.app y = 𝟙 (A.obj y) :=
     by
     intro ieq
     simp only [conjugate, inv_eq_inv, Functor.map_inv, ← Category.assoc, NatTrans.naturality,
      IsIso.inv_comp_eq, Category.comp_id]
     simp only [Category.assoc, NatTrans.naturality, IsIso.inv_comp_eq, Category.comp_id]
     simp only [← Category.assoc,ieq,Category.id_comp]

section
variable {Γ : Grpd} (A : Γ ⥤ Grpd.{u₁,u₁}) (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
variable {x y: Γ} (f: x ⟶ y)

def conjugate_Fiber (s : A.obj x ⥤ (sigma A B).obj x) :
    (A.obj y ⥤ (sigma A B).obj y) :=
    conjugate Γ A (sigma A B) f s

-- def conjugate_FiberFunc :
--     (A.obj x ⥤ (sigma A B).obj x) ⥤
--     (A.obj y ⥤ (sigma A B).obj y) :=
--      conjugating A (sigma A B) f

-- lemma conjugate_FiberFunc.obj :
--      (conjugate_FiberFunc A B f).obj = conjugate _ A (sigma A B) f
--      := rfl

-- lemma conjugate_FiberFunc.map
--     (s1 s2: A.obj x ⥤ (sigma A B).obj x)
--     (η: s1 ⟶ s2):
--      (conjugate_FiberFunc A B f).map η =
--      CategoryTheory.whiskerLeft (A.map (Groupoid.inv f))
--      (CategoryTheory.whiskerRight η
--          ((sigma A B).map f))
--      := rfl

lemma sigmaMap_fstAux_app : sigmaMap B f ⋙ (fstAux B).app y = (fstAux B).app x ⋙ A.map f := rfl

/--
If `s : piObj B x` then the underlying functor is of the form `s : A x ⥤ sigma A B x`
and it is a section of the forgetful functor `sigma A B x ⥤ A x`.
This theorem states that conjugating `A f⁻¹ ⋙ s ⋙ sigma A B f⁻¹ : A y ⥤ sigma A B y`
using some `f : x ⟶ y` produces a section of the forgetful functor `sigma A B y ⥤ A y`.
-/
theorem isSection_conjugating_isSection (s : piObj B x) : IsSection ((fstAux B).app y)
    ((Section.ι ((fstAux B).app x) ⋙ conjugating A (sigma A B) f).obj s) := by
  simp only [IsSection, Functor.comp_obj, ObjectProperty.ι_obj,
    conjugating_obj, Functor.assoc, sigmaMap_fstAux_app]
  convert_to CategoryTheory.inv (A.map f) ⋙ (s.obj ⋙ (fstAux B).app x) ⋙ A.map f = _
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
  ObjectProperty.lift (IsSection ((fstAux B).app y))
  ((Section.ι ((fstAux B).app x) ⋙ conjugating A (sigma A B) f))
  (isSection_conjugating_isSection A B f)

lemma piMap.obj (s: piObj B x) : ((piMap A B f).obj s).obj =
    (conjugating A (sigma A B) f).obj s.obj := rfl

lemma piMap.map (s1 s2: piObj B x) (η: s1 ⟶ s2) :
    (Section.ι ((fstAux B).app y)).map ((piMap A B f).map η) =
    (conjugating A (sigma A B) f).map η := rfl

/--
The square commutes

   piObj B x   ⥤   (A x ⥤ sigma A B x)
     ⋮                     ||
piMap⋮                     || conjugating A (sigma A B) f
     VV                     VV
   piObj B y   ⥤   (A y ⥤ sigma A B y)
-/
lemma piMap_ι : piMap A B f ⋙ Section.ι ((fstAux B).app y)
    = Section.ι ((fstAux B).app x) ⋙ conjugating A (sigma A B) f :=
  rfl

@[simp] lemma piMap_id (x : Γ) : piMap A B (𝟙 x) = 𝟭 (piObj B x) := by
  simp only [piMap, conjugating_id]
  rfl

lemma piMap_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    piMap A B (f ≫ g) = (piMap A B f) ⋙ (piMap A B g) := by
  simp only [piMap, conjugating_comp]
  rfl

end

/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors -/

def pi {Γ : Grpd} {A : Γ ⥤ Grpd.{u,u}} (B : Groupoidal A ⥤ Grpd.{u,u}) :
    Γ ⥤ Grpd.{u,u} where
  obj x := Grpd.of $ piObj B x
  map := piMap A B
  map_id := piMap_id A B
  map_comp := piMap_comp A B

def smallUPi_app {Γ : Ctx.{max u (v+1)}}
    (AB : y(Γ) ⟶ smallU.{v, max u (v+1)}.Ptp.obj smallU.{v, max u (v+1)}.Ty) :
    y(Γ) ⟶ smallU.{v, max u (v+1)}.Ty :=
  yonedaCategoryEquiv.symm (pi (smallUPTpEquiv AB).2)

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

end GroupoidModel

end
