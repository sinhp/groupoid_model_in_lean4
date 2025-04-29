import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Russell_PER_MS.NaturalModelSigma
import SEq.Tactic.DepRewrite
universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

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

def Conjugating {Γ : Grpd.{v,u}} (A B : Γ ⥤ Cat)
    {x y: Γ } (f: x ⟶ y) : (A.obj x ⥤ B.obj x) ⥤ (A.obj y⥤ B.obj y) :=
     (whiskeringLeft (A.obj y) (A.obj x) (B.obj x)).obj (A.map (Groupoid.inv f)) ⋙
     (whiskeringRight (A.obj y) (B.obj x) (B.obj y)).obj (B.map f)


def Conjugating_id {Γ : Grpd.{v,u}} (A B : Γ ⥤ Cat)
    (x : Γ ) : Conjugating A B (𝟙 x) = Functor.id _ := by
     simp only [Conjugating, inv_eq_inv, IsIso.inv_id, CategoryTheory.Functor.map_id]
     have e: (𝟙 (B.obj x)) = (𝟭 (B.obj x)) := rfl
     simp only [e,CategoryTheory.whiskeringRight_obj_id,Functor.comp_id]
     have e': (𝟙 (A.obj x)) = (𝟭 (A.obj x)) := rfl
     simp only[e',CategoryTheory.whiskeringLeft_obj_id]

lemma Func_middle_assoc {A B C D E: Type*} [Category A][Category B][Category C][Category D][Category E]
 (f1: A ⥤ B) (f2: B ⥤ C) (f3: C ⥤ D)(f4: D⥤ E):
 f1 ⋙ f2 ⋙ f3 ⋙ f4 = f1 ⋙ (f2 ⋙ f3) ⋙ f4 := by simp only [Functor.assoc]

lemma Func_split_assoc {A B C D E: Type*} [Category A][Category B][Category C][Category D][Category E]
 (f1: A ⥤ B) (f2: B ⥤ C) (f3: C ⥤ D)(f4: D⥤ E):
 f1 ⋙ (f2 ⋙ f3) ⋙ f4 = (f1 ⋙ f2) ⋙ (f3 ⋙ f4) := by simp only [Functor.assoc]

lemma whiskeringLeft_Right_comm {A B C D: Type*} [Category A][Category B][Category C][Category D]
    (F: A⥤ B)  (H: C ⥤ D):
    (whiskeringRight _ _ _).obj H ⋙
    (whiskeringLeft  _ _ _ ).obj F =
    (whiskeringLeft _ _ _).obj F ⋙
    (whiskeringRight _ _ _).obj H := by
     fapply CategoryTheory.Functor.ext
     · simp only [Functor.comp_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj, Functor.assoc,
       implies_true]
     · intro F1 F2 η
       simp only [Functor.comp_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj,
         Functor.comp_map, whiskeringRight_obj_map, whiskeringLeft_obj_map, eqToHom_refl,
         Category.comp_id, Category.id_comp,whiskerRight_left]

def Conjugating_comp {Γ : Grpd.{v,u}} (A B : Γ ⥤ Cat)
    (x y z : Γ ) (f:x⟶ y) (g:y⟶ z) :
    Conjugating A B (f ≫ g) = Conjugating A B f ⋙ Conjugating A B g := by
    simp only [Conjugating, inv_eq_inv, IsIso.inv_comp, Functor.map_comp, Functor.map_inv]
    have e: (whiskeringRight (A.obj y) (B.obj x) (B.obj y)).obj (B.map f) ⋙
    (whiskeringLeft (A.obj z) (A.obj y) (B.obj y)).obj (CategoryTheory.inv (A.map g)) =
    (whiskeringLeft _ _ _).obj (CategoryTheory.inv (A.map g)) ⋙
    (whiskeringRight _ _ _).obj (B.map f) := by
     apply whiskeringLeft_Right_comm
    simp only [Functor.assoc,Func_middle_assoc,e]
    simp only[Func_split_assoc,whiskeringRight_obj_comp,← whiskeringLeft_obj_comp]
    congr

def toGrpd_inv {A :Type u} [Category.{v,u} A] (B: Grpd.{v₁,u₁}) {F G:A ⥤ B} (h: NatTrans F G) :
 NatTrans G F where
   app a := Groupoid.inv (h.app a)

lemma toGrpd_inv_comp {A :Type u} [Category.{v,u} A]  (B: Grpd.{v₁,u₁}) {F G:A ⥤ B} (h: NatTrans F G):
  NatTrans.vcomp (toGrpd_inv B h) h = NatTrans.id G := by
    ext a
    simp[toGrpd_inv]


lemma toGrpd_inv_comp' {A :Type u} [Category.{v,u} A]  (B: Grpd.{v₁,u₁}) {F G:A ⥤ B} (h: NatTrans F G):
  NatTrans.vcomp h (toGrpd_inv B h) = NatTrans.id F := by
    ext a
    simp[toGrpd_inv]

instance toGrpd_Groupoid {A :Type u} [Category.{v,u} A]  (B: Grpd.{v₁,u₁}) :
  Groupoid (A ⥤ B) where
  Hom := NatTrans
  id := NatTrans.id
  comp {X Y Z} nt1 nt2 := nt1 ≫ nt2
  inv {X Y} nt:= toGrpd_inv B nt
  inv_comp f :=  toGrpd_inv_comp _ f -- Q: can I just write toGrpd_inv_comp by some method?
  comp_inv f := toGrpd_inv_comp' _ f

def Funcgrpd {A :Type u} [Category.{v,u} A]  (B: Grpd.{v₁,u₁}): Grpd :=
 Grpd.of (A ⥤ B)

def is_sec {A B:Type*} [Category A] [Category B] (F:B ⥤ A) (s:A ⥤ B) :=
 s ⋙ F = Functor.id A


abbrev Section {A B:Type*} [Category A] [Category B] (F:B ⥤ A) :=
  FullSubcategory (is_sec F)

instance Section.Category {A B:Type*} [Category A] [Category B] (F:B ⥤ A) :
  Category (Section F) := FullSubcategory.category (is_sec F)

abbrev SectionInc {A B:Type*} [Category A] [Category B] (F:B ⥤ A) :
  Section F ⥤ (A ⥤ B) := CategoryTheory.fullSubcategoryInclusion (is_sec F)

lemma SectionInc_obj {A B:Type*} [Category A] [Category B] (F:B ⥤ A) (s: Section F):
  (SectionInc F).obj s = s.obj := rfl

lemma SectionInc_map {A B:Type*} [Category A] [Category B] (F:B ⥤ A)
  (s1 s2: Section F) (η : s1 ⟶ s2):
  (SectionInc F).map η = η := rfl

lemma SectionInc_eq {A B:Type*} [Category A] [Category B] (F:B ⥤ A)
  (s1 s2: Section F) (η₁ η₂ : s1 ⟶ s2):
  (SectionInc F).map η₁ = (SectionInc F).map η₂ → η₁ = η₂ := by
   intro a
   simp only [fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map] at a
   assumption

instance Section_Groupoid {A:Type u} [Category.{v} A] (B: Grpd.{v₁,u₁}) (F:B ⥤ A) :
  Groupoid (Section F) :=
  InducedCategory.groupoid (A ⥤ B)
  (fun (f: Section F) ↦ f.obj)

--Q:Should this be def or abbrev?
def Section_Grpd  {A:Type u} [Category.{v ,u} A] (B: Grpd.{v₁,u₁}) (F:B ⥤ A) : Grpd :=
  Grpd.of (Section F)


def sigma_fst {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Grothendieck.Groupoidal A ⥤ Grpd.{v₁,u₁}) :
    NatTrans (GroupoidModel.FunctorOperation.sigma A B) A := sorry

def Fiber_Grpd {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{v₁,u₁}) (x : Γ) : Grpd :=
    Section_Grpd ((GroupoidModel.FunctorOperation.sigma A B).obj x)
    ((sigma_fst A B).app x)

lemma Fiber_Grpd.α {Γ : Grpd.{v₂,u₂}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{v₁,u₁}) (x : Γ) :
    (Fiber_Grpd A B x).α = Section ((sigma_fst A B).app x) := rfl


def Conjugate {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    {x y: C} (f: x ⟶ y) (s: A.obj x ⟶  B.obj x) :
     A.obj y ⟶  B.obj y := A.map (Groupoid.inv f) ≫ s ≫ B.map f


lemma Conjugate_id {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    (x : C) (s: A.obj x ⟶  B.obj x)  : Conjugate C A B (𝟙 x) s = s:= by
     simp only [Conjugate, inv_eq_inv, IsIso.inv_id, CategoryTheory.Functor.map_id,
       Category.comp_id, Category.id_comp]


lemma Conjugate_comp {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    {x y z: C} (f: x ⟶ y) (g: y ⟶ z) (s: A.obj x ⟶  B.obj x):
     Conjugate C A B (f ≫ g) s = Conjugate C A B g (Conjugate C A B f s) := by
      simp only [Conjugate, inv_eq_inv, IsIso.inv_comp, Functor.map_comp, Functor.map_inv,
        Category.assoc]


/-only need naturality of η-/
/-therefore, the fact that the conjugation sends section to section is by naturality of
 the projection map from sigma, and the fact that some functor has sections as its codomain-/
lemma Conjugate_PreserveSection {D: Type*} (C: Grpd.{v₁,u₁}) [Category D] (A B : C ⥤ D)
    (η: NatTrans B A)
    {x y: C} (f: x ⟶ y) (s: A.obj x ⟶  B.obj x):
    s ≫ η.app x = 𝟙 (A.obj x) → (Conjugate C A B f s) ≫ η.app y = 𝟙 (A.obj y) :=
     by
     intro ieq
     simp only [Conjugate, inv_eq_inv, Functor.map_inv, ← Category.assoc, NatTrans.naturality,
      IsIso.inv_comp_eq, Category.comp_id]
     simp only [Category.assoc, NatTrans.naturality, IsIso.inv_comp_eq, Category.comp_id]
     simp only [← Category.assoc,ieq,Category.id_comp]


def Conjugate_Fiber {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y)
    (s: A.obj x ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj x) :
    (A.obj y ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj y) :=
    Conjugate Γ A (GroupoidModel.FunctorOperation.sigma A B) f s

def Conjugate_FiberFunc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
    (A.obj x ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj x) ⥤
    (A.obj y ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj y) :=
     Conjugating (Groupoid.compForgetToCat A)
      (Groupoid.compForgetToCat (GroupoidModel.FunctorOperation.sigma A B)) f

lemma Conjugate_FiberFunc.obj {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
     (Conjugate_FiberFunc A B f).obj = Conjugate _ A (FunctorOperation.sigma A B) f
     := rfl

lemma Conjugate_FiberFunc.map {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y)
    (s1 s2: A.obj x ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj x)
    (η: s1 ⟶ s2):
     (Conjugate_FiberFunc A B f).map η =
     CategoryTheory.whiskerLeft (A.map (Groupoid.inv f))
     (CategoryTheory.whiskerRight η
         ((GroupoidModel.FunctorOperation.sigma A B).map f))
     := rfl

def ConjugateLiftCond {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
    ∀ (X : Section ((sigma_fst A B).app x)),
    is_sec ((sigma_fst A B).app y)
    ((SectionInc ((sigma_fst A B).app x) ⋙ Conjugate_FiberFunc A B f).obj X)
    := by
      intro s
      simp only [is_sec, FunctorOperation.sigma_obj, Grpd.coe_of, Functor.comp_obj,
        fullSubcategoryInclusion.obj,Conjugate_FiberFunc.obj]
      have a:= s.property
      simp only [is_sec, FunctorOperation.sigma_obj, Grpd.coe_of] at a
      have a':= Conjugate_PreserveSection Γ A (FunctorOperation.sigma A B)
                (sigma_fst A B) f _ a
      assumption


def ConjugateLiftFunc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
     Section ((sigma_fst A B).app x) ⥤ Section ((sigma_fst A B).app y) :=
     CategoryTheory.FullSubcategory.lift (is_sec ((sigma_fst A B).app y))
            ((SectionInc ((sigma_fst A B).app x) ⋙ Conjugate_FiberFunc A B f))
     (ConjugateLiftCond A B f)


lemma ConjugateLiftFunc.obj {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y) (s: Section ((sigma_fst A B).app x)):
    ((ConjugateLiftFunc A B f).obj s).obj =
    (Conjugate_FiberFunc A B f).obj s.obj := rfl



lemma ConjugateLiftFunc.map {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y) (s1 s2: Section ((sigma_fst A B).app x))
    (η: s1 ⟶ s2):
    (SectionInc ((sigma_fst A B).app y)).map
     ((ConjugateLiftFunc A B f).map η) =
    (Conjugate_FiberFunc A B f).map η := rfl


lemma ConjugateLiftFunc_Inc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
    (ConjugateLiftFunc A B f) ⋙ SectionInc ((sigma_fst A B).app y)
    = ((SectionInc ((sigma_fst A B).app x) ⋙ Conjugate_FiberFunc A B f))
    := by
     simp only [FunctorOperation.sigma_obj, Grpd.coe_of, ConjugateLiftFunc, SectionInc,
       FullSubcategory.lift_comp_inclusion_eq]

lemma idSection_Inc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    (x : Γ) :
    𝟙 (Fiber_Grpd A B x) ⋙ SectionInc ((sigma_fst A B).app x)
    = ((SectionInc ((sigma_fst A B).app x) ⋙ Conjugate_FiberFunc A B (𝟙 x))) :=
     by
     simp only [FunctorOperation.sigma_obj, Grpd.coe_of]
     rw[Conjugate_FiberFunc,Conjugating_id]
     rfl


lemma fullSubcategoryInclusion_Mono_lemma {T C:Type u}
   [Category.{v} C] [Category.{v} T]  (Z: C → Prop)
 (f g: T ⥤ FullSubcategory Z)
 (e: f ⋙ (fullSubcategoryInclusion Z) = g ⋙ (fullSubcategoryInclusion Z)) : f = g := by
  let iso:= eqToIso e
  let fgiso := CategoryTheory.Functor.fullyFaithfulCancelRight (fullSubcategoryInclusion Z) iso
  have p : ∀ (X : T), f.obj X = g.obj X := by
    intro X
    have e1: (f ⋙ fullSubcategoryInclusion Z).obj X = (g ⋙ fullSubcategoryInclusion Z).obj X
     := Functor.congr_obj e X
    simp only [Functor.comp_obj, fullSubcategoryInclusion.obj] at e1
    ext
    exact e1
  fapply CategoryTheory.Functor.ext_of_iso fgiso
  · exact p
  intro X
  simp only [Functor.fullyFaithfulCancelRight, NatIso.ofComponents_hom_app, Functor.preimageIso_hom,
    fullSubcategoryInclusion.obj, Iso.app_hom, fgiso]
  have e2: (fullSubcategoryInclusion Z).map (eqToHom (p X)) = (iso.hom.app X) := by
    simp only [fullSubcategoryInclusion, inducedFunctor_obj, inducedFunctor_map, eqToIso.hom,
      eqToHom_app, Functor.comp_obj, iso, fgiso]
    rfl
  simp only[← e2,Functor.preimage, fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map,
    Classical.choose_eq, fgiso, iso]


lemma ConjugateLiftFunc_id
    {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    (x: Γ) : ConjugateLiftFunc A B (𝟙 x) = 𝟙 (Fiber_Grpd A B x) :=
     by
      fapply fullSubcategoryInclusion_Mono_lemma
      simp only [FunctorOperation.sigma_obj, Grpd.coe_of, ConjugateLiftFunc_Inc A B (𝟙 x),
        idSection_Inc A B x]


lemma ConjugateLiftFunc_comp
    {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y z: Γ} (f : x ⟶ y) (g : y ⟶ z):
    ConjugateLiftFunc A B (f ≫ g) =  (ConjugateLiftFunc A B f) ⋙ (ConjugateLiftFunc A B g) := by
    fapply fullSubcategoryInclusion_Mono_lemma
    simp only [FunctorOperation.sigma_obj, Grpd.coe_of, Functor.assoc]
    have e: ConjugateLiftFunc A B (f ≫ g) ⋙ SectionInc ((sigma_fst A B).app z) =
  ConjugateLiftFunc A B f ⋙ ConjugateLiftFunc A B g ⋙  SectionInc ((sigma_fst A B).app z) :=
    by
     simp only [FunctorOperation.sigma_obj, Grpd.coe_of, ConjugateLiftFunc_Inc A B g,
                ← Functor.assoc,ConjugateLiftFunc_Inc A B f, FunctorOperation.sigma_obj,
                Grpd.coe_of, Conjugate_FiberFunc]
     simp only [Functor.assoc, ← Conjugating_comp (compForgetToCat A),
                ConjugateLiftFunc_Inc A B (f ≫ g),Conjugate_FiberFunc]
    refine e

/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors -/

def pi {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    : Γ ⥤ Grpd.{u₁,u₁} where
      obj x := Fiber_Grpd A B x
      map f := ConjugateLiftFunc A B f
      map_id x:= ConjugateLiftFunc_id A B x
      map_comp := ConjugateLiftFunc_comp A B


/-- The formation rule for Π-types for the ambient natural model `base` -/
def basePi.Pi : base.Ptp.obj base.{u}.Ty ⟶ base.Ty where
  app Γ := fun pair =>
    let ⟨A,B⟩ := baseUvPolyTpEquiv pair
    yonedaEquiv (yonedaCatEquiv.symm (pi A B))
  naturality := sorry

def basePi : NaturalModelPi base where
  Pi := basePi.Pi
  lam := sorry
  Pi_pullback := sorry

def smallUPi : NaturalModelPi smallU := sorry

def uHomSeqPis' (i : ℕ) (ilen : i < 4) :
  NaturalModelPi (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUPi
  | 1 => smallUPi
  | 2 => smallUPi
  | 3 => basePi
  | (n+4) => by omega

def uHomSeqPis : UHomSeqPiSigma Ctx := { uHomSeq with
  nmPi := uHomSeqPis'
  nmSigma := uHomSeqSigmas' }

end GroupoidModel

end
