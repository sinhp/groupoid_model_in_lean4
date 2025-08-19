import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone

import GroupoidModel.Syntax.NaturalModel

import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone

import SEq.Tactic.DepRewrite

universe w v u v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory

open Functor.Groupoidal


-- def PGrpd.inc (G : Type) [Groupoid G] : G ⥤ PGrpd  where
--   obj x := {base := Grpd.of G,fiber := x}
--   map f := {base := Functor.id G, fiber := f}
--   map_comp {X Y Z} f g := by
--     fapply Functor.Grothendieck.Hom.ext
--     · simp [Grpd.comp_eq_comp]
--     · simp [Grpd.forgetToCat]

-- namespace GrothendieckPointedCategories

-- abbrev BPCat := Grothendieck (PCat.forgetToCat)

-- namespace BPCat

-- abbrev forgetToCat : BPCat ⥤ Cat where
--   obj x := x.base.base
--   map f := f.base.base
--   map_comp := by
--     intros x y z f g
--     exact rfl

-- abbrev FirstPointed  : BPCat ⥤ PCat := Grothendieck.forget _

-- def SecondPointed : BPCat ⥤ PCat where
--   obj x := {base := x.base.base, fiber := x.fiber}
--   map f := {base := f.base.base, fiber := f.fiber}
--   map_comp := by
--     intros x y z f g
--     exact rfl

-- /- This needs a better name but I cant come up with one now-/
-- theorem Comutes : FirstPointed ⋙ PCat.forgetToCat = SecondPointed ⋙ PCat.forgetToCat := by
--   simp[FirstPointed,SecondPointed,PCat.forgetToCat,Functor.comp]


-- def isPullback : Functor.IsPullback SecondPointed.{u,v} FirstPointed.{u,v} PCat.forgetToCat.{u,v} PCat.forgetToCat.{u,v}
--   := @CategoryTheory.Grothendieck.isPullback PCat _ (PCat.forgetToCat)

-- end BPCat

abbrev BPGrpd := ∫ PGrpd.forgetToGrpd

namespace BPGrpd

@[simp]
def snd : BPGrpd ⥤ PGrpd := Functor.Groupoidal.forget

abbrev forgetToGrpd : BPGrpd ⥤ Grpd := snd ⋙ PGrpd.forgetToGrpd

@[simp]
def fst : BPGrpd ⥤ PGrpd := toPGrpd _

/-- The commutative square
  BPGrpd ----> PGrpd
    |            |
    |            |
    |            |
    |            |
    V            V
   PGrpd ----> Grpd
-/
theorem snd_forgetToGrpd : fst ⋙ PGrpd.forgetToGrpd = snd ⋙ PGrpd.forgetToGrpd := by
  simp [toPGrpd_forgetToGrpd]

/- BPGrpd is the pullback of PGrpd.forgetToGrpd with itself -/
def isPullback : Functor.IsPullback fst.{u,v} snd.{u,v} PGrpd.forgetToGrpd.{u,v}
    PGrpd.forgetToGrpd.{u,v} := by
  apply @Functor.Groupoidal.isPullback PGrpd _ (PGrpd.forgetToGrpd)

lemma isPullback_lift_obj_base {Γ : Type*} [Category Γ] (F G : Γ ⥤ PGrpd) (hFG) (x) :
    ((BPGrpd.isPullback.lift F G hFG).obj x).base = G.obj x :=
  calc ((BPGrpd.isPullback.lift F G hFG).obj x).base
  _ = (BPGrpd.isPullback.lift F G hFG ⋙ BPGrpd.snd).obj x := by
    rw [Functor.comp_obj]
    simp
  _ = _ := by simp only [BPGrpd.fst, BPGrpd.snd, Functor.IsPullback.lift_snd]

lemma isPullback_lift_obj_fiber {Γ : Type*} [Category Γ] (F G : Γ ⥤ PGrpd) (hFG) (x) :
    ((BPGrpd.isPullback.lift F G hFG).obj x).fiber ≍ PGrpd.objFiber F x := by
  rw [← Functor.Groupoidal.toPGrpd_obj_fiber]
  rw! (castMode := .all)
    [← Functor.comp_obj (BPGrpd.isPullback.lift F G hFG) (toPGrpd PGrpd.forgetToGrpd),
    Functor.IsPullback.lift_fst]
  simp [PGrpd.objFiber]

lemma isPullback_lift_map_base {Γ : Type*} [Category Γ] (F G : Γ ⥤ PGrpd) (hFG) {x y}
    (f : x ⟶ y) :
    ((BPGrpd.isPullback.lift F G hFG).map f).base =
    eqToHom (BPGrpd.isPullback_lift_obj_base _ _ _ _) ≫
    G.map f ≫ eqToHom (BPGrpd.isPullback_lift_obj_base _ _ _ _).symm :=
  calc ((BPGrpd.isPullback.lift F G hFG).map f).base
  _ = (BPGrpd.isPullback.lift F G hFG ⋙ BPGrpd.snd).map f := by
    rw [Functor.comp_map]
    simp
  _ = _ := by
    apply Functor.congr_hom
    simp

lemma isPullback_lift_map_fiber {Γ : Type*} [Category Γ] (F G : Γ ⥤ PGrpd) (hFG) {x y}
    (f : x ⟶ y) :
    ((BPGrpd.isPullback.lift F G hFG).map f).fiber ≍
    PGrpd.mapFiber F f := by
  rw [← Functor.Groupoidal.toPGrpd_map_fiber]
  rw! (castMode := .all)
    [← Functor.comp_map (BPGrpd.isPullback.lift F G hFG) (toPGrpd PGrpd.forgetToGrpd),
    Functor.IsPullback.lift_fst]
  simp only [eqRec_heq_iff_heq]
  congr 1
  any_goals rw [← Functor.comp_obj]
  all_goals simp

end BPGrpd

end CategoryTheory

namespace GroupoidModel

open CategoryTheory Functor.Groupoidal

attribute [local simp] Functor.assoc

namespace FunctorOperation

section Id

/-
In this section we build this diagram

PGrpd-----Refl---->PGrpd
  |                 |
  |                 |
  |                 |
Diag                |
  |                 |
  |                 |
  v                 v
BPGrpd----Id----->Grpd

This is NOT a pullback.

Instead we use Diag and Refl to define a functor R : PGrpd ⥤ Grothendieck.Groupoidal Id
-/

/-- The identity type former takes a bipointed groupoid `((A,a0),a1)` to the set of isomorphisms
between its two given points `A(a0,a1)`.
Here `A = x.base.base`, `a0 = x.base.fiber` and `a1 = x.fiber`. -/
def idObj (x : BPGrpd) : Grpd := Grpd.of (CategoryTheory.Discrete (x.base.fiber ⟶ x.fiber))

/-- The identity type former takes a morphism of bipointed groupoids
`((F,f0),f1) : ((A,a0),a1) ⟶ ((B,b0),b1)`
to the function `A(a0,a1) → B(b0,b1)` taking `g : a0 ≅ a1` to `f0⁻¹ ⋙ F g ⋙ f1` where
`f0⁻¹ : b0 ⟶ F a0`, `F g : F a0 ⟶ F a1` and `f1 : F a1 ⟶ b1`. -/
def idMap {x y : BPGrpd} (f : x ⟶ y) : idObj x ⥤ idObj y :=
  Discrete.functor (fun g => ⟨ inv f.base.fiber ≫ (f.base.base.map g) ≫ f.fiber ⟩)

lemma Discrete.functor_ext' {X C : Type*} [Category C] {F G : X → C} (h : ∀ x : X, F x = G x) :
    Discrete.functor F = Discrete.functor G := by
  have : F = G := by aesop
  subst this
  rfl

lemma Discrete.functor_eq {X C : Type*} [Category C] {F : Discrete X ⥤ C} :
    F = Discrete.functor fun x ↦ F.obj ⟨x⟩ := by
  fapply CategoryTheory.Functor.ext
  · aesop
  · intro x y f
    cases x ; rcases f with ⟨⟨h⟩⟩
    cases h
    simp

lemma Discrete.functor_ext {X C : Type*} [Category C] (F G : Discrete X ⥤ C)
    (h : ∀ x : X, F.obj ⟨x⟩ = G.obj ⟨x⟩) :
    F = G :=
  calc F
    _ = Discrete.functor (fun x => F.obj ⟨x⟩) := Discrete.functor_eq
    _ = Discrete.functor (fun x => G.obj ⟨x⟩) := Discrete.functor_ext' h
    _ = G := Discrete.functor_eq.symm

lemma Discrete.ext {X : Type*} {x y : Discrete X} (h : x.as = y.as) : x = y := by
  cases x; cases h
  rfl

/-- The identity type formation rule, equivalently viewed as a functor. -/
@[simps]
def id : BPGrpd.{u,u} ⥤ Grpd.{u,u} where
  obj := idObj
  map := idMap
  map_id X := by
    apply Discrete.functor_ext
    intro x
    apply Discrete.ext
    dsimp only [idMap, Grpd.forgetToCat]
    aesop
  map_comp {X Y Z} f g := by
    apply Discrete.functor_ext
    intro a
    apply Discrete.ext
    dsimp only [idMap, Grpd.forgetToCat]
    aesop

/--
The diagonal functor into the pullback.
It creates a second copy of the point from the input pointed groupoid.

This version of `diag` is used for better definitional reduction.
-/
def diag : PGrpd ⥤ BPGrpd where
  obj x := objMk x x.fiber
  map f := homMk f f.fiber
  map_comp {X Y Z} f g:= by
    fapply Hom.ext
    · simp
    · simp [Grpd.forgetToCat]

@[simp]
lemma diag_comp_toPGrpd : diag ⋙ toPGrpd _ = 𝟭 _ := rfl

@[simp]
lemma diag_comp_forget : diag ⋙ forget = 𝟭 _ := rfl

/--
This version of `diag` is used for functor equational reasoning.
-/
def diag' : PGrpd ⥤ BPGrpd :=
  BPGrpd.isPullback.lift (𝟭 _) (𝟭 _) rfl

lemma diag_eq_diag' : diag = diag' :=
  BPGrpd.isPullback.hom_ext (by simp [diag']) (by simp [diag'])

def reflObjFiber (x : PGrpd) : Discrete (x.fiber ⟶ x.fiber) := ⟨𝟙 x.fiber⟩

def refl : PGrpd ⥤ PGrpd :=
  PGrpd.functorTo (diag ⋙ id) reflObjFiber (fun f => Discrete.eqToHom (by
    simp [idMap, diag, reflObjFiber, Grpd.forgetToCat]))
    (by simp)
    (by intros; simp [Discrete.eqToHom, eqToHom_map])

theorem refl_comp_forgetToGrpd : refl ⋙ PGrpd.forgetToGrpd = diag ⋙ id := rfl

/- This is the universal lift
            Refl
PGrpd ------------>
 |----> ∫Id -----> PGrpd
 |  R   |            |
 |      |            |
 Diag   |            | forget
 |      |            |
 |      V            V
 ---> BPGrpd -----> Grpd
              Id
-/
def comparison : PGrpd ⥤ ∫ id :=
  (isPullback id).lift refl diag refl_comp_forgetToGrpd

/- This is the composition

PGrpd
 |----> ∫Id
 |  R   |
 |      |
 Diag   | forget
 |      |
 |      V
 ---> BPGrpd
        |
        |
        | BPGrpd.forgetToGrpd
        |
        V
      Grpd
-/

/- This is the universal lift
            Refl
PGrpd ------------>
 |----> ∫Id -----> PGrpd
 |  R   |            |
 |      |            |
 Diag   |            | forget
 |      |            |
 |      V            V
 ---> BPGrpd -----> Grpd
              Id
-/
theorem comparison_comp_forget_comp_forgetToGrpd : comparison ⋙ forget ⋙ BPGrpd.forgetToGrpd =
    PGrpd.forgetToGrpd := by
  simp only [comparison, diag, ← Functor.assoc, Functor.IsPullback.lift_snd]
  fapply CategoryTheory.Functor.ext
  . intro X
    simp
  . intro X Y f
    simp


-- /- Here I define the path groupoid and how it can be used to create identities
-- Note that this is not the same as Id.
-- -/

-- def Path : Type u := ULift.{u} Bool

-- instance : Groupoid.{u,u} Path where
--   Hom x y := PUnit
--   id := fun _ => PUnit.unit
--   comp := by intros; fconstructor
--   inv := fun _ => PUnit.unit
--   id_comp := by intros; rfl
--   comp_id := by intros; rfl
--   assoc := by intros; rfl

-- abbrev Paths (G : Type u) [Groupoid.{u,u} G] : Type u := (Path ⥤ G)

-- /- This should be able to be made into a groupoid but I am having trouble with leans instances-/
-- instance (G : Type u) [Groupoid G] : Category.{u,u} (Paths G) := by
--   exact Functor.category

-- def Path_Refl (G : Type u) [Groupoid G] : G ⥤ (Paths G) where
--   obj x := by
--     fconstructor
--     fconstructor
--     . exact fun _ => x
--     . exact fun _ => 𝟙 x
--     . exact congrFun rfl
--     . simp
--   map f := by
--     fconstructor
--     . intro x
--       exact f
--     . simp

-- def PreJ (G : Type u) [Groupoid G]  : Paths G ⥤ G := by
--   fconstructor
--   fconstructor
--   . intro p
--     refine p.obj { down := false }
--   . intros X Y f
--     refine f.app ?_
--   . exact congrFun rfl
--   . simp

-- theorem PreJLift  (G : Type u) [Groupoid G] : (Path_Refl G) ⋙ (PreJ G) = 𝟭 G := by
--   simp [Path_Refl,PreJ,Functor.comp,Functor.id]

def mkId {Γ : Type*} [Category Γ] (a0 a1 : Γ ⥤ PGrpd.{u,u})
    (a0_tp_eq_a1_tp : a0 ⋙ PGrpd.forgetToGrpd = a1 ⋙ PGrpd.forgetToGrpd) :
    Γ ⥤ Grpd :=
  BPGrpd.isPullback.lift a1 a0 (by rw [a0_tp_eq_a1_tp]) ⋙ FunctorOperation.id

section
variable {Γ : Type*} [Groupoid Γ] (a : Γ ⥤ PGrpd.{u,u})

/-- The context appearing in the motive for identity elimination `J`
  Here `A = a ⋙ PGrpd.forgetToGrpd`
  ```
  Γ ⊢ A
  Γ ⊢ a : A
  Γ.(x:A).(h:Id(A,a,x)) ⊢ C
  motiveCtx a := Γ.(x:A).(h:Id(A,a,x))
  ...
  ```
-/
def motiveCtx : Grpd :=
  Grpd.of $ ∫ mkId (forget ⋙ a) (toPGrpd (a ⋙ PGrpd.forgetToGrpd)) rfl

def reflSubst' : Γ ⥤ motiveCtx a :=
  (isPullback _).lift (a ⋙ refl) (sec _ a rfl) (by
    simp only [Functor.assoc, refl_comp_forgetToGrpd, mkId]
    simp only [← Functor.assoc]
    congr 1
    apply (isPullback _).hom_ext
    · simp
    · simp only [Functor.assoc, diag_comp_forget, Functor.simpCompId, BPGrpd.fst, BPGrpd.snd,
        Functor.IsPullback.lift_snd]
      simp [← Functor.assoc])

-- This seems like a bad way of going about it.
@[simps]
def reflSubst : Γ ⥤ motiveCtx a where
  obj x := objMk (objMk x (PGrpd.objFiber a x)) (Discrete.mk (eqToHom (by
    rw! (castMode := .all) [BPGrpd.isPullback_lift_obj_base]
    rw! (castMode := .all) [BPGrpd.isPullback_lift_obj_fiber]
    simp only [← heq_eq_eq, heq_eqRec_iff_heq]
    simp [PGrpd.objFiber])))
  map := sorry
  map_id := sorry
  map_comp := sorry

lemma reflSubst_eq_reflSubst' : reflSubst a = reflSubst' a := by
  apply (isPullback _).hom_ext
  · simp [reflSubst']
    sorry
  · sorry

variable (C : motiveCtx a ⥤ Grpd.{v,v}) (r : Γ ⥤ PGrpd.{v,v})
  (r_tp : r ⋙ PGrpd.forgetToGrpd = reflSubst a ⋙ C)

def motiveCtx.fiber_as' (x : motiveCtx a) : PGrpd.objFiber a _ ⟶ (base x).fiber := by
  have h := x.fiber.as
  rw! [BPGrpd.isPullback_lift_obj_fiber, BPGrpd.isPullback_lift_obj_base] at h
  exact h

lemma motiveCtx.fiber_as'_heq (x : motiveCtx a) : motiveCtx.fiber_as' a x ≍ x.fiber.as := by
  simp [fiber_as']

-- TODO: replace `reflSubst` with `reflSubst'` in the following definition.
/--
The morphism in the groupoid `motiveCtx` from `(reflSubst a).obj x.base.base` to any
`x : motiveCtx a = (x.base.base : Γ) · (x.base.fiber : a.base) · a.base(a.fiber,x.fiber)`
given by the triple `(𝟙 x : x ⟶ x, x.fiber : a.base ⟶ x.fiber, 𝟙 x.fiber)`
-/
def retraction (x : motiveCtx a) : (reflSubst a).obj x.base.base ⟶ x :=
  homMk (homMk (𝟙 x.base.base)
    (eqToHom (by simp [CategoryTheory.Functor.map_id]) ≫ motiveCtx.fiber_as' a x))
  (eqToHom (by
    apply Discrete.ext
    simp only [mkId, Functor.comp_map, id_map, idMap]
    rw! (castMode := .all) [BPGrpd.isPullback_lift_map_fiber, BPGrpd.isPullback_lift_map_base,
      ← motiveCtx.fiber_as'_heq]
    simp only [BPGrpd.fst, BPGrpd.snd, reflSubst_obj, objMk_base, Functor.comp_obj, id_obj,
      Functor.Groupoidal.forget_obj, Functor.Grothendieck.forget_obj,
      Functor.Grothendieck.forget_map, objMk_fiber, Functor.comp_map, forget_map, homMk_base,
      Functor.Grothendieck.Hom.comp_base, Functor.Grothendieck.Hom.comp_fiber, eqToHom_refl,
      Functor.Grothendieck.fiber_eqToHom, eqToHom_map, PGrpd.map_id_fiber, eqToHom_trans,
      Category.id_comp, inv_eqToHom, Grpd.comp_obj, toPGrpd_obj_base, PGrpd.mapFiber,
      toPGrpd_map_fiber, homMk_fiber, Discrete.functor_obj_eq_as, eqToHom_trans_assoc, ← heq_eq_eq,
      heq_cast_iff_heq]
    generalize_proofs _ _ _ p1 p2 p3 p4
    apply HEq.trans (b := cast p3 (eqToHom p4 ≫ motiveCtx.fiber_as' a x))
    · rw [eqToHom_comp_heq_iff]
    · simp))

/-- Identity elimination in the groupoid model,
as an operation on functor categories.
On objects, this is defined by transport along a path from the diagonal:
suppose `x : motiveCtx a = (x.base : Γ) · (x.fiber.base : a.base) · a.base(a.fiber,x.fiber.fiber)`.
Then there is a morphism in the groupoid `motiveCtx` from `reflSubst a` to `x`
given by the triple `(𝟙 x : x ⟶ x, x.fiber.fiber : a.base ⟶ x.fiber.fiber, 𝟙 x.fiber.fiber)`
-/
def j : motiveCtx a ⥤ PGrpd.{v,v} :=
  PGrpd.functorTo C
  (fun x => (C.map (retraction a x)).obj $ PGrpd.objFiber' r_tp x.base.base)
  sorry sorry sorry

/-- The typing rule for identity elimination `j` -/
lemma j_comp_forgetToGrpd : j a C r r_tp ⋙ PGrpd.forgetToGrpd = C := rfl

/-- The identity type `β` computation rule for the groupoid model. -/
lemma reflSubst_comp_j : reflSubst a ⋙ j a C r r_tp = r := sorry

end
end Id
end FunctorOperation

-- section Contract
-- /-
-- At some point I think we will need to contract groupoids along there isomorphisms. In this sections
-- I define how to do that.
-- -/

-- variable {C : Type u} [Category C] (a b : C) (f : a ⟶ b) [iso : IsIso f]

-- inductive ContractBase : Type u where
--   | inc (x : {x : C // x ≠ a ∧ x ≠ b}) : ContractBase
--   | p : ContractBase

-- def ContractHom (x y : ContractBase a b) : Type := match x,y with
--   | ContractBase.inc t, ContractBase.inc u => t.val ⟶ u.val
--   | ContractBase.inc t, ContractBase.p => t.val ⟶ a
--   | ContractBase.p , ContractBase.inc t => b ⟶ t.val
--   | ContractBase.p, ContractBase.p => b ⟶ a

-- def ContractHomId (x : ContractBase a b) : ContractHom a b x x := match x with
--   | ContractBase.inc t => 𝟙 t.val
--   | ContractBase.p => inv f

-- def ContractHomComp {x y z : ContractBase a b} (g : ContractHom a b x y) (h : ContractHom a b y z) :
--   ContractHom a b x z := match x,y,z with
--   | ContractBase.inc _, ContractBase.inc _, ContractBase.inc _ => g ≫ h
--   | ContractBase.inc _, ContractBase.inc _, ContractBase.p => g ≫ h
--   | ContractBase.inc _, ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
--   | ContractBase.inc _, ContractBase.p, ContractBase.p => g ≫ f ≫  h
--   | ContractBase.p , ContractBase.inc _, ContractBase.inc _ => g ≫ h
--   | ContractBase.p , ContractBase.inc _, ContractBase.p => g ≫ h
--   | ContractBase.p , ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
--   | ContractBase.p , ContractBase.p, ContractBase.p => g ≫ f ≫ h

-- instance ic (iso : IsIso f) : Category (ContractBase a b) where
--   Hom := ContractHom a b
--   id := ContractHomId a b f
--   comp := ContractHomComp a b f
--   id_comp := by
--     intros x y g
--     cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--   comp_id := by
--     intros x y g
--     cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--   assoc := by
--     intros w x y z g h i
--     cases w <;> cases x <;> cases y <;> cases z <;> simp [ContractHomId, ContractHomComp]
-- end Contract
-- section GrpdContract

-- variable {G : Type u} [Groupoid G]

-- def Grpd.Contract (a b : G) : Type u := ContractBase a b

-- instance icc {a b : G} (f : a ⟶ b) : Category (Grpd.Contract a b) := ic a b f (isIso_of_op f)

-- instance {a b : G} (f : a ⟶ b) : Groupoid (Grpd.Contract a b) where
--     Hom := ContractHom a b
--     id := ContractHomId a b f
--     comp := ContractHomComp a b f
--     id_comp := by
--       intros x y g
--       cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--     comp_id := by
--       intros x y g
--       cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
--     assoc := by
--       intros w x y z g h i
--       cases w <;> cases x <;> cases y <;> cases z <;> simp [ContractHomId, ContractHomComp]
--     inv {a b} g := by
--       cases a <;> cases b
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact inv g
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact inv (g ≫ f)
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact inv (f ≫ g)
--       . dsimp[Quiver.Hom, ContractHom]
--         dsimp[ContractHom] at g
--         exact (inv f) ≫ (inv g) ≫ (inv f)
--     inv_comp {a b} g := sorry
--     comp_inv := by sorry

-- def CTtoGrpd {a b : G} (f : a ⟶ b) : Grpd := by
--   refine @Grpd.of (Grpd.Contract a b) ?_
--   exact instGroupoidContractOfHom f

-- end GrpdContract

-- section ContractMap

-- -- def PJ : Grothendieck.Groupoidal Id ⥤ PGrpd where
-- --   obj x := by
-- --     rcases x with ⟨base,fiber⟩
-- --     rcases base with ⟨pg,p2⟩
-- --     rcases pg with ⟨base,p1⟩
-- --     simp[Grpd.forgetToCat] at p2 p1
-- --     fconstructor
-- --     . refine CTtoGrpd ?_ (G := base) (a := p1) (b := p2)
-- --       simp[Grpd.forgetToCat,Id] at fiber
-- --       rcases fiber with ⟨f⟩
-- --       simp[Grothendieck.Groupoidal.base,Grothendieck.Groupoidal.fiber] at f
-- --       exact f
-- --     . simp[Grpd.forgetToCat,CTtoGrpd,Grpd.Contract]
-- --       exact ContractBase.p
-- --   map {x y} F := by
-- --     simp[Quiver.Hom]
-- --     rcases F with ⟨base,fiber⟩
-- --     rcases base with ⟨pg,p2⟩
-- --     rcases pg with ⟨base,p1⟩
-- --     simp[Grpd.forgetToCat] at p2 p1
-- --     fconstructor
-- --     . fconstructor
-- --       fconstructor
-- --       . intro x
-- --         cases x
-- --         rename_i x'
-- --         rcases x' with ⟨x',p⟩
-- --         fconstructor
-- --         fconstructor
-- --         . refine base.obj x'
-- --         . simp

-- end ContractMap

/-
In this section I am trying to move the previous results about groupoids to the
category of contexts
-/


def Refl' : GroupoidModel.E.{u,u} ⟶ GroupoidModel.E.{u,u} :=
  AsSmall.up.map (𝟭 (Core (AsSmall PGrpd)))

namespace smallUId

lemma isKernelPair : IsKernelPair smallU.tp.{u} ym(Ctx.homOfFunctor BPGrpd.fst)
    ym(Ctx.homOfFunctor BPGrpd.snd) :=
  Functor.map_isPullback yoneda (IsPullback.isPullback_homOfFunctor _ _ _ _ BPGrpd.isPullback)

def Id : y(Ctx.ofCategory BPGrpd.{u,u}) ⟶ smallU.Ty.{u} :=
  ym(Ctx.homOfFunctor FunctorOperation.id)

def refl : smallU.Tm.{u} ⟶ smallU.Tm.{u} :=
  ym(Ctx.homOfFunctor FunctorOperation.refl)

lemma refl_tp : refl ≫ smallU.tp.{u} = isKernelPair.lift (𝟙 smallU.Tm) (𝟙 smallU.Tm) rfl ≫ Id := by
  convert_to _ = ym(Ctx.homOfFunctor (BPGrpd.isPullback.lift (𝟭 PGrpd.{u,u}) (𝟭 PGrpd.{u,u}) rfl)) ≫ Id
  · congr 1
    apply isKernelPair.hom_ext
    · erw [isKernelPair.lift_fst]
      simp [← Functor.map_comp, ← Ctx.homOfFunctor_comp, E]
    · erw [isKernelPair.lift_snd]
      simp [← Functor.map_comp, ← Ctx.homOfFunctor_comp, E]
  · simp only [smallU_Ty, smallU_Tm, refl, smallU_tp, π, ← Functor.map_comp, ←
      Ctx.homOfFunctor_comp, FunctorOperation.refl_comp_forgetToGrpd, FunctorOperation.diag_eq_diag',
      FunctorOperation.diag', Id]
    rfl

lemma i_isPullback : IsPullback ym(Ctx.homOfFunctor (toPGrpd FunctorOperation.id))
    ym(Ctx.homOfFunctor Functor.Groupoidal.forget) smallU.tp Id :=
  Functor.map_isPullback yoneda
    (IsPullback.isPullback_homOfFunctor _ _ _ _ (isPullback FunctorOperation.id))

def smallUIdIntro : NaturalModelBase.IdIntro smallU.{u} where
  k := y(Ctx.ofCategory BPGrpd.{u,u})
  k1 := ym(Ctx.homOfFunctor BPGrpd.fst)
  k2 := ym(Ctx.homOfFunctor BPGrpd.snd)
  isKernelPair := isKernelPair
  Id := Id
  refl := refl
  refl_tp := refl_tp

open NaturalModelBase

def j {Γ : Ctx.{(max u v w) + 1}} (a : y(Γ) ⟶ smallU.Tm.{u,(max u v w) + 1})
    (C : y(smallUIdIntro.{u,(max u v w) + 1}.motiveCtx a) ⟶ smallU.Ty.{v,(max u v w) + 1})
    (r : y(Γ) ⟶ smallU.Tm.{v,(max u v w) + 1})
    (r_tp : r ≫ smallU.tp.{v} = ym(smallUIdIntro.{u}.reflSubst a) ≫ C)
    : y(smallUIdIntro.{u,(max u v w) + 1}.motiveCtx a) ⟶ smallU.Tm.{v,(max u v w) + 1} := by
  let a' := yonedaCategoryEquiv a
  let C' := yonedaCategoryEquiv C
  let r' := yonedaCategoryEquiv r
  have r'_forgetToGrpd : r' ⋙ PGrpd.forgetToGrpd =
      Ctx.toGrpd.map (smallUIdIntro.reflSubst a) ⋙ C' := sorry
  -- simp [IdIntro.motiveCtx] at C
  sorry

lemma j_tp {Γ : Ctx.{(max u v w) + 1}} (a : y(Γ) ⟶ smallU.Tm.{u,(max u v w) + 1})
    (C : y(smallUIdIntro.{u,(max u v w) + 1}.motiveCtx a) ⟶ smallU.Ty.{v,(max u v w) + 1})
    (r : y(Γ) ⟶ smallU.Tm.{v,(max u v w) + 1})
    (r_tp : r ≫ smallU.tp.{v} = ym(smallUIdIntro.{u}.reflSubst a) ≫ C)
    : j.{w,v,u} a C r r_tp ≫ smallU.tp.{v} = C := sorry

lemma reflSubst_j {Γ : Ctx.{(max u v w) + 1}} (a : y(Γ) ⟶ smallU.Tm.{u,(max u v w) + 1})
    (C : y(smallUIdIntro.{u,(max u v w) + 1}.motiveCtx a) ⟶ smallU.Ty.{v,(max u v w) + 1})
    (r : y(Γ) ⟶ smallU.Tm.{v,(max u v w) + 1})
    (r_tp : r ≫ smallU.tp.{v} = ym(smallUIdIntro.{u}.reflSubst a) ≫ C)
    : ym(smallUIdIntro.{u}.reflSubst a) ≫ j.{w,v,u} a C r r_tp = r := sorry

-- TODO: can universe variables be improved?
-- TODO: make namespaces consistent with Sigma file
def smallUId : NaturalModelBase.Id smallU.{u, (max u v w) + 1} smallU.{v, (max u v w) + 1} := {
  smallUIdIntro.{u, (max u v w) + 1} with
  j := j.{w,v,u}
  j_tp := j_tp.{w,v,u}
  reflSubst_j := reflSubst_j.{w,v,u}
}

-- def smallUIdBase : NaturalModelBase.Id smallU.{u} where
--   k := y(smallU.ext.{u} smallU.tp.{u})
--   k1 := smallU.var smallU.tp
--   k2 := ym(smallU.disp smallU.tp)
--   isKernelPair := smallU.disp_pullback _
--   Id := Id
--   refl := sorry
--   refl_tp := sorry
--   i := sorry
--   i1 := sorry
--   i2 := sorry
--   i_isPullback := sorry
--   weakPullback := sorry

end smallUId

end GroupoidModel
