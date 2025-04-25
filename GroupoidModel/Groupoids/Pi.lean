import GroupoidModel.Groupoids.Sigma
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck  Groupoid




def toGrpd_inv {A :Type u} [Category.{v,u} A] (B: Grpd.{v₁,u₁}) {F G:A ⥤ B} (h: NatTrans F G) :
 NatTrans G F where
   app a := Groupoid.inv (h.app a)

--toGrpdInv
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
  inv_comp f :=  toGrpd_inv_comp _ f -- can I just write toGrpd_inv_comp by some method?
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
   simp[SectionInc_map] at a
   assumption

instance Section_Groupoid {A:Type u} [Category.{v} A] (B: Grpd.{v₁,u₁}) (F:B ⥤ A) :
  Groupoid (Section F) :=
  InducedCategory.groupoid (A ⥤ B)
  (fun (f: Section F) ↦ f.obj)


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
     -- A.map (Groupoid.inv f) ≫ s ≫ (GroupoidModel.FunctorOperation.sigma A B).map f


def Conjugate_FiberFunc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    {x y: Γ} (f: x ⟶ y):
    (A.obj x ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj x) ⥤
    (A.obj y ⥤ (GroupoidModel.FunctorOperation.sigma A B).obj y) where
      obj := Conjugate_Fiber A B f
      map {s1 s2} η :=
        let a := CategoryTheory.whiskerRight η
         ((GroupoidModel.FunctorOperation.sigma A B).map f)
        let a' := CategoryTheory.whiskerLeft (A.map (Groupoid.inv f)) a
        a'
      map_id s := by
       simp[Conjugate_Fiber,Conjugate]
       rfl


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
      simp[is_sec]
      simp[Conjugate_FiberFunc.obj]
      have a:= s.property
      simp[is_sec] at a
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

lemma Conjugate_FiberFunc_id {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁}) (x: Γ):
   Conjugate_FiberFunc A B (𝟙 x) = Functor.id _ := by
    simp[Conjugate_FiberFunc]
    apply
    sorry

lemma idSection_Inc {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    (x : Γ) :
    𝟙 (Fiber_Grpd A B x) ⋙ SectionInc ((sigma_fst A B).app x)
    = ((SectionInc ((sigma_fst A B).app x) ⋙ Conjugate_FiberFunc A B (𝟙 x))) :=
     by
     simp
     rw[Conjugate_FiberFunc_id]
     rfl

lemma fullSubcategoryInclusion_Mono {C:Type*} [Category C] (Z: C → Prop) :
Mono (Cat.homOf (fullSubcategoryInclusion Z)) where
  right_cancellation := by
   intro T f1 f2 e
   --cases f1; cases f2
   --simp at e
   apply CategoryTheory.Functor.ext
   · sorry
  --  · intro X Y f
  --    have a:= CategoryTheory.Functor.congr_hom f
  --    rw![CategoryTheory.Functor.congr_hom]
   · sorry

theorem whiskerLeft_Lid {C D: Type*} [Category C] [Category D]
     {G H : C⥤ D} (η: G ⟶ H):
    whiskerLeft (Functor.id C) η = η := rfl

lemma ConjugateLiftFunc_id
    {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    (x: Γ) : ConjugateLiftFunc A B (𝟙 x) = 𝟙 (Fiber_Grpd A B x) :=
     by
     --#check (Cat.homOf (SectionInc ((sigma_fst A B).app x)))
     let a :=
      @CategoryTheory.cancel_mono
       _ _
       (Cat.of (Section ((sigma_fst A B).app x)))
       (Cat.of (↑(A.obj x) ⥤ ↑((FunctorOperation.sigma A B).obj x))) _
       (Cat.homOf (SectionInc ((sigma_fst A B).app x)))
       sorry
       (Cat.homOf (ConjugateLiftFunc A B (𝟙 x)))
       (Cat.homOf (𝟙 (Fiber_Grpd A B x)))
     have a1 : Cat.homOf (ConjugateLiftFunc A B (𝟙 x)) = Cat.homOf (𝟙 (Fiber_Grpd A B x))
      := by
      rw[← a]
      sorry
     refine a1

/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors -/

def pi {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{u₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{u₁,u₁})
    : Γ ⥤ Grpd.{u₁,u₁} where
      obj x := Fiber_Grpd A B x
      map {x y} f := ConjugateLiftFunc A B f
      map_id x:= ConjugateLiftFunc_id A B x
      map_comp := sorry


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
