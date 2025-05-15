import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import GroupoidModel.Pointed.Basic
import GroupoidModel.ForMathlib

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace Grothendieck

open Functor

section morphism_universe_v₁


variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Cat.{v₁,u₁}}

@[simps] def toPCatObj (x : Grothendieck A) : PCat.{v₁,u₁} :=
  ⟨(A.obj x.base), PointedCategory.of (A.obj x.base) x.fiber⟩

def toPCatMap {x y : Grothendieck A} (f : x ⟶ y) :
    toPCatObj x ⟶ toPCatObj y :=
  ⟨ A.map f.base , f.fiber ⟩

variable (A)

def toPCat : Grothendieck A ⥤ PCat.{v₁,u₁} where
  obj := toPCatObj
  map := toPCatMap
  map_id x := by
    dsimp
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    apply PointedFunctor.ext
    · simp [toPCatMap]
    · simp [CategoryStruct.id, Functor.id, Grothendieck.id, PointedFunctor.id, toPCatMap]
  map_comp {x y z} f g := by
    dsimp [PointedFunctor.comp]
    let _ := (PointedCategory.of (A.obj x.base) x.fiber)
    let _ := (PointedCategory.of (A.obj z.base) z.fiber)
    apply PointedFunctor.ext
    · simp [toPCatMap]
    · simp [toPCatMap, A.map_comp, Cat.comp_eq_comp]

theorem toPCat_comp_forgetPoint : toPCat A ⋙ PCat.forgetToCat
    = Grothendieck.forget A ⋙ A := by
  apply Functor.ext
  · intro X Y f
    rfl
  · intro
    rfl

theorem toPCatObj_fiber_inj {x y : Grothendieck A}
    (h : HEq ((toPCat A).obj x).str.pt ((toPCat A).obj y).str.pt) :
  HEq x.fiber y.fiber := h

theorem comm_sq : toPCat A ⋙ PCat.forgetToCat
  = Grothendieck.forget A ⋙ A := rfl

namespace IsMegaPullback

variable {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PCat.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PCat.forgetToCat = snd ⋙ A)

abbrev pt (x : C) := (fst.obj x).str.pt

abbrev point {x y : C} (f : x ⟶ y) :
    ((fst.map f)).obj (pt fst x) ⟶ pt fst y :=
  (fst.map f).point

variable {A} {fst} {snd}

def lift_obj (x : C) : Grothendieck A :=
  ⟨ snd.obj x , ((eqToHom w).app x).obj (pt fst x) ⟩

@[simp] theorem lift_obj_base (x : C) : (lift_obj w x).base = snd.obj x := by
  simp [lift_obj]

theorem lift_obj_fiber (x : C) : (lift_obj w x).fiber =
    ((eqToHom w).app x).obj (pt fst x) := by
  simp [lift_obj]

variable {x y : C} (f : x ⟶ y)

def lift_map : lift_obj w x ⟶ lift_obj w y :=
  ⟨ (snd.map f) ,
    let m1 := ((eqToHom w).app y).map (point fst f)
    let m2 := (eqToHom ((eqToHom w).naturality f).symm).app
      (pt fst x)
    m2 ≫ m1 ⟩

@[simp] theorem lift_map_base :
  (lift_map w f).base = (snd.map f) := rfl

theorem lift_map_fiber :
    (lift_map w f).fiber =
      (eqToHom ((eqToHom w).naturality f).symm).app (pt fst x)
        ≫ ((eqToHom w).app y).map (point fst f) :=
  rfl

include w in
theorem lift_map_fiber_pf3 :
    Cat.of (fst.obj y).α = A.obj (snd.obj y) :=
  Functor.congr_obj w y

theorem lift_map_fiber_pf2 :
    (A.map (snd.map f)).obj
      (((eqToHom w).app x).obj (pt fst x))
    = (eqToHom (lift_map_fiber_pf3 w)).obj
      ((fst.map f).obj (pt fst x)) := by
  have h := Functor.congr_obj
    ((eqToHom w).naturality f).symm (pt fst x)
  simp only [eqToHom_app, Functor.comp_map,
  Cat.comp_obj, PCat.forgetToCat_map] at *
  rw [h]

theorem lift_map_fiber_pf0 :
    (eqToHom (lift_map_fiber_pf3 w)).obj (pt fst y)
    = ((eqToHom w).app y).obj (pt fst y) := by simp

theorem lift_map_fiber_pf1 :
    ((fst.map f).obj (pt fst x) ⟶ pt fst y)
    = ((eqToHom (lift_map_fiber_pf3 w)).obj
      ((fst.map f).obj (pt fst x))
      ⟶ (eqToHom (lift_map_fiber_pf3 w)).obj (pt fst y)) :=
  Cat.eqToHom_hom_aux
    ((fst.map f).obj (pt fst x))
    (pt fst y)
    (lift_map_fiber_pf3 w)

theorem lift_map_fiber' : (lift_map w f).fiber =
    eqToHom (lift_map_fiber_pf2 w f)
    ≫ cast (lift_map_fiber_pf1 w f) (point fst f)
    ≫ eqToHom (lift_map_fiber_pf0 w) := by
  have hy := Functor.congr_hom
    (eqToHom_app w y) (point fst f)
  have hx := eqToHom_app
    ((eqToHom w).naturality f).symm (pt fst x)
  rw [lift_map_fiber, hy, hx, Cat.eqToHom_hom]
  simp

theorem lift_aux {C D : Cat.{v,u}} {X Y : C}
    (pf1 : C = D) (pf2 : X = Y) (pf3 : (eqToHom pf1).obj X = (eqToHom pf1).obj Y) :
    HEq (eqToHom pf2) (eqToHom pf3) := by
  subst pf2
  subst pf1
  simp at *

variable (fst) (snd)

def lift : C ⥤ Grothendieck A where
  obj := lift_obj w
  map := lift_map w
  map_id x := by
    apply Grothendieck.ext
    · have h := @PCat.map_id_point _ _ fst x
      simp only [comp_obj, Functor.comp_map] at h
      simp only [lift_map_fiber', lift_obj, Cat.of_α, comp_obj, lift_map_base, h,
        eqToHom_trans_assoc, id_fiber, eqToHom_comp_iff, eqToHom_trans, comp_eqToHom_iff]
      apply eq_of_heq
      generalize_proofs
      rename_i pf1 pf2 pf3 pf4
      apply HEq.trans $ cast_heq pf2 (eqToHom pf3)
      apply lift_aux pf1 pf3 pf4
    · simp [lift_obj]
  map_comp {x y z} f g := by
    dsimp [Grothendieck.comp]
    apply Grothendieck.ext
    · dsimp
      have h1 := dcongr_arg PointedFunctor.point
        (Functor.map_comp fst f g)
      have h2 : (fst.map f ≫ fst.map g).point =
        ((fst.map g).map (fst.map f).point) ≫ (fst.map g).point := rfl
      have hgNatNatF := (eqToHom ((eqToHom w).naturality g).symm).naturality (fst.map f).point
      have h3 := congr_arg (λ x ↦ x ≫ ((eqToHom w).app z).map (fst.map g).point) hgNatNatF
      dsimp at h3
      simp only [Category.assoc, eqToHom_app ((eqToHom w).naturality g).symm] at h3
      simp only [h1, h2, map_comp, comp_fiber, Category.assoc, lift_map_fiber,
        eqToHom_map (A.map (snd.map g)),
        eqToHom_app ((eqToHom w).naturality f).symm,
        eqToHom_app ((eqToHom w).naturality (f ≫ g)).symm,
        eqToHom_app ((eqToHom w).naturality g).symm, eqToHom_map]
      rw [h3]
      simp
    · simp

@[simp] theorem fac_right : lift fst snd w ⋙ Grothendieck.forget A = snd := by
  apply Functor.ext
  · simp [lift]
  · simp [lift]

@[simp] theorem fac_left : lift fst snd w ⋙ Grothendieck.toPCat A = fst := by
  apply Functor.ext
  · intro x y f
    apply PointedFunctor.ext
    · simp only [lift, lift_obj, lift_map, Cat.of_α, Functor.comp_obj,
        PCat.forgetToCat_obj, toPCat, toPCatMap, toPCatObj_α,
        Functor.comp_map, lift_map_base, comp_obj, PCat.forgetToCat_obj,
        Cat.of_α, Functor.comp_map, Cat.comp_obj, PCat.forgetToCat_map,
        Cat.eqToHom_app, PCat.eqToHom_point, eqToHom_map,
        PCat.comp_point, heq_eqToHom_comp_iff,
        heq_comp_eqToHom_iff, Functor.congr_hom (eqToHom_app w y) (point fst f), PCat.eqToHom_hom (fst.map f).point,
        point, eqToHom_trans_assoc, PCat.comp_toFunctor, toPCatObj_α, Functor.comp_obj]
      simp only [Cat.eqToHom_hom, Cat.of_α, eqToHom_comp_iff, eqToHom_trans_assoc, comp_eqToHom_iff, Category.assoc, eqToHom_trans]
      generalize_proofs
      rw [CategoryTheory.conj_eqToHom_iff_heq]
      · rw [heq_cast_iff_heq, cast_heq_iff_heq]
      · simp [PCat.eqToHom_toFunctor]
    · simp only [lift, lift_obj, Cat.of_α, Functor.comp_obj,
        PCat.forgetToCat_obj, toPCat, toPCatMap, toPCatObj_α,
        Functor.comp_map, lift_map_base]
      have h := Functor.congr_hom w f
      simp only [PCat.forgetToCat_map, Cat.of_α, Functor.comp_obj, Functor.comp_map] at h
      simp [h, PCat.eqToHom_toFunctor, ← Cat.comp_eq_comp]
  · intro x
    simp only [toPCat, toPCatObj, toPCatMap, lift, lift_obj,
      Functor.comp_obj, Cat.eqToHom_app]
    have h := (Functor.congr_obj w x).symm
    simp only [Cat.comp_obj, Functor.comp_obj, PCat.forgetToCat_obj] at h
    congr 1
    · rw [h]
      rfl
    · congr 1
      · rw [h]
        rfl
      · refine heq_of_cast_eq ?_ ?_
        · rw [h]
          rfl
        · simp [eqToHom_app, Cat.eqToHom_obj]
      · rw [h]
        simp only [heq_eq_eq]
        rfl

theorem lift_uniq (m : C ⥤ Grothendieck A)
    (hl : m ⋙ Grothendieck.toPCat A = fst)
    (hr : m ⋙ Grothendieck.forget A = snd) :
    m = lift _ _ w := by
  apply Functor.ext
  · intro x y f
    apply Grothendieck.ext
    · dsimp [lift]
      rw [lift_map_fiber']
      generalize_proofs pf1 pf2 _ _ _ _ _ _ pf3
      have h0 := Functor.congr_hom hl f
      have h1 := PointedFunctor.congr_point h0
      have h2 := @eqToHom_fiber (Cat.of Γ) _ _ (m.obj x) _ pf1
      have h3 := @eqToHom_fiber (Cat.of Γ) _ _ _ _ pf2
      have h4 := congr_arg A.map (eqToHom_base pf2)
      simp only [eqToHom_map] at h4
      have h5 := Functor.congr_hom h4 (cast pf3 (point fst f))
      simp only [toPCat, toPCatObj, toPCatMap, comp_obj, Functor.comp_map,
        PCat.comp_toFunctor, PCat.comp_point] at h1
      simp only [h1, h2, h3, h5, PCat.eqToHom_point, eqToHom_map, eqToHom_trans_assoc, eqToHom_fiber,
        PCat.forgetToCat_obj, Cat.of_α, map_comp, Category.assoc, eqToHom_trans]
      simp only [PCat.eqToHom_hom, Functor.congr_hom (map_eqToHom_base _), Cat.eqToHom_hom, cast_cast,
        Category.assoc, eqToHom_comp_iff,  comp_eqToHom_iff,
        eqToHom_trans, eqToHom_trans_assoc]
      rw [CategoryTheory.conj_eqToHom_iff_heq]
      · rw [heq_cast_iff_heq, cast_heq_iff_heq]
      · simp [← Functor.comp_obj, ← Cat.comp_eq_comp,
        PCat.eqToHom_toFunctor]
    · simp only [comp_base, eqToHom_base, Functor.congr_hom hr f]
      exact Functor.congr_hom hr f
  · intro x
    apply Grothendieck.obj_ext_hEq
    · exact Functor.congr_obj hr x
    · apply toPCatObj_fiber_inj
      have h0 := Functor.congr_obj hl x
      have h1 := Functor.congr_obj (fac_left _ _ w) x
      simp [congr_arg_heq (λ x : PCat ↦ x.str.pt) (h0.trans h1.symm)]

theorem hom_ext {m n : C ⥤ Grothendieck A}
    (hl : m ⋙ Grothendieck.toPCat A = n ⋙ Grothendieck.toPCat A)
    (hr : m ⋙ Grothendieck.forget A = n ⋙ Grothendieck.forget A) :
    m = n := by
  rw [lift_uniq (m ⋙ toPCat A) (m ⋙ forget A) ?_ m rfl rfl,
    lift_uniq (n ⋙ toPCat A) (n ⋙ forget A) ?_ n rfl rfl]
  rw! [hl, hr]
  . show n ⋙ (toPCat A ⋙ PCat.forgetToCat) = _
    rw [toPCat_comp_forgetPoint]
    rfl
  . show m ⋙ (toPCat A ⋙ PCat.forgetToCat) = _
    rw [toPCat_comp_forgetPoint]
    rfl

end IsMegaPullback
end morphism_universe_v₁

/-
In this section we build the lemmas for showing the pullback

  Grothendieck A --- toPCat ----> PCat
        |                           |
        |                           |
 Grothendieck.forget        PCat.forgetToCat
        |                           |
        v                           v
        Γ--------------A---------> Cat
in the appropriately sized category `Cat.{v, max u (v+1)}`;
where `(Γ : Type u) [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v})`.

This particular choice of hom universe level avoids using ULiftHom.
In our applications either `u = v` for a small `Γ`
so that `A : Γ ⥤ Cat.{u,u}`,
or `Γ = Grpd.{v,v}` and `A : Grpd.{v,v} ⥤ Cat.{v,v}` is the inclusion
so that `u = v + 1`.
-/
namespace IsPullback

variable (Γ : Type u) [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v})

open Functor ULift

variable {Γ}

abbrev uLiftGrothendieck : Cat.{v, max u (v+1)} :=
  Cat.ofULift.{max u (v+1)} (Grothendieck A)

abbrev uLiftGrothendieckForget :
    uLiftGrothendieck.{v,u} A ⟶ Cat.ofULift.{v+1} Γ :=
  downFunctor ⋙ Grothendieck.forget A ⋙ upFunctor

abbrev uLiftCat : Cat.{v, max u (v+1)} :=
  Cat.ofULift.{max u (v+1)} Cat.{v,v}

abbrev uLiftPCat : Cat.{v, max u (v+1)} :=
  Cat.ofULift.{max u (v+1)} PCat.{v,v}

abbrev uLiftPCatForgetToCat : uLiftPCat.{v,u} ⟶ uLiftCat.{v,u} :=
  downFunctor ⋙ PCat.forgetToCat ⋙ upFunctor

abbrev uLiftToPCat : uLiftGrothendieck.{v,u} A ⟶ uLiftPCat.{v,u} :=
  ULift.downFunctor ⋙ Grothendieck.toPCat A ⋙ ULift.upFunctor

abbrev uLiftA : Cat.ofULift.{v+1} Γ ⥤ uLiftCat.{v,u} :=
  downFunctor ⋙ A ⋙ upFunctor

variable {A}

theorem comm_sq : uLiftToPCat A ≫ uLiftPCatForgetToCat
    = uLiftGrothendieckForget A ≫ uLiftA A := by
  apply Functor.ext
  · intro X Y f
    rfl
  · intro
    rfl

variable (A)

open Limits PullbackCone

def cone : Limits.PullbackCone uLiftPCatForgetToCat (uLiftA A)
  := Limits.PullbackCone.mk (uLiftToPCat A) (uLiftGrothendieckForget A) comm_sq

variable {A}

abbrev pt' {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)}
    (x : s.pt) := (downFunctor.obj (s.fst.obj x)).str.pt

theorem condition' {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)} :
    s.fst ⋙ downFunctor ⋙ PCat.forgetToCat = s.snd ⋙ downFunctor ⋙ A := by
  rw [← comp_upFunctor_inj.{_,_,_,_,max u (v + 1)}]
  exact s.condition

variable {s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)} {x y : s.pt} {f : x ⟶ y}

def lift (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) :
    s.pt ⥤ Grothendieck A :=
  IsMegaPullback.lift
    (s.fst ⋙ downFunctor)
    (s.snd ⋙ downFunctor)
    condition'

def lift' (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
    s.pt ⟶ uLiftGrothendieck A := (lift s) ⋙ ULift.upFunctor

theorem fac_left (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
    lift s ⋙ Grothendieck.toPCat A ⋙ upFunctor = s.fst := by
  rw [← comp_downFunctor_inj]
  exact IsMegaPullback.fac_left
    (s.fst ⋙ downFunctor)
    (s.snd ⋙ downFunctor)
    condition'

theorem fac_right (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
    lift s ⋙ Grothendieck.forget A ⋙ upFunctor
    = s.snd := by
  rw [← comp_downFunctor_inj]
  exact IsMegaPullback.fac_right
    (s.fst ⋙ downFunctor)
    (s.snd ⋙ downFunctor)
    condition'

theorem lift_uniq (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) (m : s.pt ⥤ Grothendieck A)
    (hl : m ⋙ Grothendieck.toPCat A = s.fst ⋙ downFunctor)
    (hr : m ⋙ Grothendieck.forget A = s.snd ⋙ downFunctor) :
    m = lift s :=
  IsMegaPullback.lift_uniq
    (s.fst ⋙ downFunctor) (s.snd ⋙ downFunctor) condition' m hl hr

theorem lift_uniq' (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) (m : s.pt ⟶ uLiftGrothendieck A)
    (hl : m ≫ uLiftToPCat A = s.fst) (hr : m ≫ uLiftGrothendieckForget A = s.snd) :
    m = lift' s := by
  unfold lift'
  rw [← lift_uniq s (m ⋙ downFunctor) (congr_arg (λ F ↦ F ⋙ downFunctor) hl)
    (by
      simp only [Cat.of_α, Functor.assoc, ← hr, uLiftGrothendieckForget, Cat.comp_eq_comp]
      rfl)]
  aesop_cat

variable (A)

def isLimit : IsLimit (cone A) :=
  IsLimit.mk comm_sq lift' fac_left fac_right lift_uniq'

end IsPullback

open IsPullback

/-
The following square is a pullback

  Grothendieck A --- toPCat ----> PCat
        |                           |
        |                           |
 Grothendieck.forget        PCat.forgetToCat
        |                           |
        v                           v
        Γ--------------A---------> Cat
in the appropriately sized category `Cat.{v, max u (v+1)}`;
where `(Γ : Type u) [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v})`.

This particular choice of hom universe level avoids using ULiftHom.
In our applications either `u = v` for a small `Γ`
so that `A : Γ ⥤ Cat.{u,u}`,
or `Γ = Grpd.{v,v}` and `A : Grpd.{v,v} ⥤ Cat.{v,v}` is the inclusion
so that `u = v + 1`.
-/
theorem isPullback {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v}) :
    IsPullback
      (uLiftToPCat A)
      (uLiftGrothendieckForget A)
      (uLiftPCatForgetToCat)
      (uLiftA A) :=
  IsPullback.of_isLimit (isLimit A)

end Grothendieck

end CategoryTheory
