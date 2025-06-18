import Mathlib.CategoryTheory.Category.Grpd
import GroupoidModel.ForMathlib
import GroupoidModel.Grothendieck.Groupoidal.Basic
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.ForMathlib.CategoryTheory.Functor.IsPullback
import GroupoidModel.Pointed.Basic
import GroupoidModel.Pointed.IsPullback
import Mathlib.CategoryTheory.Groupoid.Discrete

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

noncomputable section DoublePointedGroupoid

namespace GrothendieckPointedCategories

abbrev BPCat := Grothendieck (PCat.forgetToCat)

namespace BPCat

abbrev forgetToCat : BPCat ⥤ Cat where
  obj x := x.base.base
  map f := f.base.base
  map_comp := by
    intros x y z f g
    exact rfl

abbrev FirstPointed  : BPCat ⥤ PCat := Grothendieck.forget _

def SecondPointed : BPCat ⥤ PCat where
  obj x := {base := x.base.base, fiber := x.fiber}
  map f := {base := f.base.base, fiber := f.fiber}
  map_comp := by
    intros x y z f g
    exact rfl

theorem Comutes : FirstPointed ⋙ PCat.forgetToCat = SecondPointed ⋙ PCat.forgetToCat := by
  simp[FirstPointed,SecondPointed,PCat.forgetToCat,Functor.comp]

def isPullback : Functor.IsPullback SecondPointed.{u,v} FirstPointed.{u,v} PCat.forgetToCat.{u,v} PCat.forgetToCat.{u,v}
  := @CategoryTheory.Grothendieck.isPullback PCat _ (PCat.forgetToCat)

end BPCat

abbrev BPGrpd := Grothendieck.Groupoidal (PGrpd.forgetToGrpd)

namespace BPGrpd

abbrev forgetToGrpd : BPGrpd ⥤ Grpd where
  obj x := x.base.base
  map f := f.base.base
  map_comp := by
    intros x y z f g
    exact rfl

abbrev FirstPointed  : BPGrpd ⥤ PGrpd := @Grothendieck.Groupoidal.forget _ _ (PGrpd.forgetToGrpd)

def SecondPointed : BPGrpd ⥤ PGrpd where
  obj x := {base := x.base.base, fiber := x.fiber}
  map f := {base := f.base.base, fiber := f.fiber}
  map_comp := by
    intros x y z f g
    exact rfl

theorem Comutes : FirstPointed ⋙ PGrpd.forgetToGrpd = SecondPointed ⋙ PGrpd.forgetToGrpd := by
  simp[FirstPointed,SecondPointed,PGrpd.forgetToGrpd,Functor.comp]
  exact Prod.mk_inj.mp rfl

-- def isPullback : Functor.IsPullback SecondPointed.{u,v} FirstPointed.{u,v} PGrpd.forgetToGrpd.{u,v} PGrpd.forgetToGrpd.{u,v}
--   := sorry

end BPGrpd


def Id : BPGrpd ⥤ Grpd where
  obj x := Grpd.of (CategoryTheory.Discrete (x.base.fiber ⟶ x.fiber))
  map f := Discrete.functor (fun(a) => { as := inv f.base.fiber ≫ (f.base.base.map a) ≫ f.fiber})
  map_comp {X Y Z} f g := by
    simp
    fapply CategoryTheory.Functor.ext
    . intros a
      rcases a with ⟨a⟩
      simp
      exact
        IsIso.hom_inv_id_assoc
          ((Grothendieck.Groupoidal.Hom.base g).base.map (Grothendieck.Groupoidal.Hom.base f).fiber)
          ((Grothendieck.Groupoidal.Hom.base g).base.map
              ((Grothendieck.Groupoidal.Hom.base f).base.map a) ≫
            (Grothendieck.Groupoidal.Hom.base g).base.map (Grothendieck.Groupoidal.Hom.fiber f) ≫
              Grothendieck.Groupoidal.Hom.fiber g)
    . intro x y t
      simp[Discrete.functor]
      exact Eq.symm (eq_of_comp_right_eq fun {X_1} ↦ congrFun rfl)
  map_id X := by
    simp[Discrete.functor]
    apply CategoryTheory.Functor.ext
    . intro a b f
      refine eq_of_comp_right_eq fun {X_1} h ↦ rfl
    . intro x
      simp[Discrete.functor]
      congr
      simp[Functor.id,Grpd.forgetToCat]

def Diag : PGrpd ⥤ BPGrpd where
  obj x := {base := x, fiber := x.fiber}
  map f := {base := f, fiber := f.fiber}
  map_comp {X Y Z} f g:= by
    simp[CategoryStruct.comp,Grothendieck.Groupoidal.comp,Grothendieck.comp]


def Refl : PGrpd ⥤ PGrpd where
  obj x := {base := Grpd.of (CategoryTheory.Discrete (x.fiber ⟶ x.fiber)), fiber := { as := 𝟙 x.fiber}}
  map {X Y} f := by
    fconstructor
    . refine Discrete.functor (fun g => {as := (inv f.fiber ≫ f.base.map g ≫ f.fiber)})
    . simp[Grpd.forgetToCat]
      sorry






section Contract
variable {C : Type} [Category C] (a b : C) (f : a ⟶ b) [iso : IsIso f]

inductive ContractBase : Type where
  | inc (x : {x : C // x ≠ a ∧ x ≠ b}) : ContractBase
  | p : ContractBase

def ContractHom (x y : ContractBase a b) : Type := match x,y with
  | ContractBase.inc t, ContractBase.inc u => t.val ⟶ u.val
  | ContractBase.inc t, ContractBase.p => t.val ⟶ a
  | ContractBase.p , ContractBase.inc t => b ⟶ t.val
  | ContractBase.p, ContractBase.p => b ⟶ a

def ContractHomId (x : ContractBase a b) : ContractHom a b x x := match x with
  | ContractBase.inc t => 𝟙 t.val
  | ContractBase.p => inv f

def ContractHomComp {x y z : ContractBase a b} (g : ContractHom a b x y) (h : ContractHom a b y z) :
  ContractHom a b x z := match x,y,z with
  | ContractBase.inc _, ContractBase.inc _, ContractBase.inc _ => g ≫ h
  | ContractBase.inc _, ContractBase.inc _, ContractBase.p => g ≫ h
  | ContractBase.inc _, ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
  | ContractBase.inc _, ContractBase.p, ContractBase.p => g ≫ f ≫  h
  | ContractBase.p , ContractBase.inc _, ContractBase.inc _ => g ≫ h
  | ContractBase.p , ContractBase.inc _, ContractBase.p => g ≫ h
  | ContractBase.p , ContractBase.p, ContractBase.inc _ => g ≫ f ≫ h
  | ContractBase.p , ContractBase.p, ContractBase.p => g ≫ f ≫ h

instance (iso : IsIso f) : Category (ContractBase a b) where
  Hom := ContractHom a b
  id := ContractHomId a b f
  comp := ContractHomComp a b f
  id_comp := by
    intros x y g
    cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
  comp_id := by
    intros x y g
    cases x <;> cases y <;> simp [ContractHomId, ContractHomComp]
  assoc := by
    intros w x y z g h i
    cases w <;> cases x <;> cases y <;> cases z <;> simp [ContractHomId, ContractHomComp]
