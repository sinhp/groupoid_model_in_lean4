import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import GroupoidModel.Pointed.Basic
import GroupoidModel.ForMathlib

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace Grothendieck

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
    (h : HEq ((toPCat A).obj x).str.pt ((toPCat A).obj y).str.pt) : HEq x.fiber y.fiber := h

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

def uLiftΓ : Cat.{v, max u (v+1)} :=
  Cat.of $ ULift.{max u (v+1)} Γ

variable {Γ}

abbrev uLiftGrothendieck : Cat.{v, max u (v+1)} :=
  Cat.of (ULift.{max u (v+1), max v u} (Grothendieck A))

abbrev uLiftGrothendieckForget : uLiftGrothendieck.{v,u} A ⟶ uLiftΓ.{v,u} Γ :=
  downFunctor ⋙ Grothendieck.forget A ⋙ upFunctor

abbrev uLiftCat : Cat.{v, max u (v+1)} := Cat.of (ULift.{max u (v+1), v + 1} Cat.{v,v})

abbrev uLiftPCat : Cat.{v, max u (v+1)} := Cat.of (ULift.{max u (v+1), v + 1} PCat.{v,v})

abbrev uLiftPCatForgetToCat : uLiftPCat.{v,u} ⟶ uLiftCat.{v,u} :=
  downFunctor ⋙ PCat.forgetToCat ⋙ upFunctor

abbrev uLiftToPCat : uLiftGrothendieck.{v,u} A ⟶ uLiftPCat.{v,u} :=
  ULift.downFunctor ⋙ Grothendieck.toPCat A ⋙ ULift.upFunctor

abbrev uLiftA : uLiftΓ.{v,u} Γ ⟶ uLiftCat.{v,u} := downFunctor ⋙ A ⋙ upFunctor

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

example : Category Cat := inferInstance

theorem condition' {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)} :
    s.fst ⋙ downFunctor ⋙ PCat.forgetToCat = s.snd ⋙ downFunctor ⋙ A := by
  rw [← comp_upFunctor_inj.{_,_,_,_,max u (v + 1)}]
  exact s.condition

/- This is an explicit natural transformation for the commuting condition for cone s -/
abbrev ε (s : PullbackCone uLiftPCatForgetToCat (uLiftA A))
    : s.fst ⋙ downFunctor ⋙ PCat.forgetToCat ⟶ s.snd ⋙ downFunctor ⋙ A :=
  eqToHom condition'

abbrev εApp
    {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)} (x : s.pt)
    : (s.fst ⋙ uLiftPCatForgetToCat).obj x
    ⟶ (s.snd ⋙ uLiftA A).obj x := (ε s).app x

abbrev εNaturality
    {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)} {x y : s.pt}
    (f : x ⟶ y) := (ε s).naturality f

abbrev point' {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)}
    {x y : s.pt} (f : x ⟶ y) :
    (downFunctor.map (s.fst.map f)).obj (pt' x) ⟶ pt' y :=
  (s.fst.map f).point

@[simp] def lift_obj {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)}
  (x : s.pt) : Grothendieck A :=
  ⟨ (s.snd.obj x).down , (εApp x).obj (pt' x) ⟩

def lift_map {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)}
  {x y : s.pt} (f : x ⟶ y) : lift_obj x ⟶ lift_obj y :=
  ⟨ downFunctor.map (s.snd.map f) ,
    let m1 := (εApp y).map (point' f)
    let m2 := (eqToHom (εNaturality f).symm).app (pt' x)
    m2 ≫ m1 ⟩

@[simp] theorem lift_map_base  {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)}
    {x y : s.pt} (f : x ⟶ y) : (lift_map f).base = downFunctor.map (s.snd.map f) := rfl

theorem lift_map_fiber  {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)}
    {x y : s.pt} (f : x ⟶ y) : (lift_map f).fiber =
    (eqToHom (εNaturality f).symm).app (pt' x) ≫ (εApp y).map (point' f) := rfl

variable {s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)} {x y : s.pt} {f : x ⟶ y}

theorem lift_map_fiber_pf3 : Cat.of (s.fst.obj y).down.α = A.obj (s.snd.obj y).down :=
  Functor.congr_obj condition' y

theorem lift_map_fiber_pf2 : (A.map (downFunctor.map (s.snd.map f))).obj ((εApp x).obj (pt' x))
    = (eqToHom lift_map_fiber_pf3).obj ((downFunctor.map (s.fst.map f)).obj (pt' x)) := by
  have h := Functor.congr_obj (εNaturality f).symm (pt' x)
  simp only [eqToHom_app, Functor.comp_map,
  downFunctor_map, Cat.comp_obj, PCat.forgetToCat_map] at *
  rw [h]

theorem lift_map_fiber_pf0 :
    (eqToHom lift_map_fiber_pf3).obj (pt' y)
    = (εApp y).obj (pt' y) := by simp

theorem lift_map_fiber_pf1 : ((s.fst.map f).obj (pt' x) ⟶ pt' y) =
    ((eqToHom lift_map_fiber_pf3).obj ((s.fst.map f).obj (pt' x))
    ⟶ (eqToHom lift_map_fiber_pf3).obj (pt' y)) :=
  Cat.eqToHom_hom_aux ((s.fst.map f).obj (pt' x)) (pt' y) lift_map_fiber_pf3

theorem lift_map_fiber' : (lift_map f).fiber =
    eqToHom lift_map_fiber_pf2 ≫ cast lift_map_fiber_pf1 (point' f) ≫ eqToHom lift_map_fiber_pf0 := by
  have hy := Functor.congr_hom (eqToHom_app condition' y) (point' f)
  have hx := eqToHom_app (εNaturality f).symm (pt' x)
  rw [lift_map_fiber, hy, hx, Cat.eqToHom_hom]
  simp

theorem lift_aux {C D : Cat.{v,u}} {X Y : C}
    (pf1 : C = D) (pf2 : X = Y) (pf3 : (eqToHom pf1).obj X = (eqToHom pf1).obj Y) :
    HEq (eqToHom pf2) (eqToHom pf3) := by
  subst pf2
  subst pf1
  simp at *

def lift (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) :
  s.pt ⥤ Grothendieck A where
  obj x := lift_obj x
  map {x y} f := lift_map f
  map_id x := by
    apply Grothendieck.ext
    · have h := @PCat.map_id_point _ _ (s.fst ⋙ downFunctor) x
      simp only [comp_obj, downFunctor_obj, Functor.comp_map, downFunctor_map] at h
      simp only [lift_map_fiber', lift_obj, Cat.of_α, comp_obj, lift_map_base, h,
        eqToHom_trans_assoc, id_fiber, eqToHom_comp_iff, eqToHom_trans, comp_eqToHom_iff]
      apply eq_of_heq
      generalize_proofs
      rename_i pf1 pf2 pf3 pf4
      apply HEq.trans $ cast_heq pf2 (eqToHom pf3)
      apply lift_aux pf1 pf3 pf4
    · simp
      rfl  -- TODO fix
  map_comp {x y z} f g := by
    dsimp [Grothendieck.comp]
    apply Grothendieck.ext
    · dsimp
      have h1 := dcongr_arg PointedFunctor.point
        (Functor.map_comp s.fst f g)
      have h2 : (s.fst.map f ≫ s.fst.map g).point =
        ((s.fst.map g).map (s.fst.map f).point) ≫ (s.fst.map g).point := rfl
      have hgNatNatF := (eqToHom (εNaturality g).symm).naturality (s.fst.map f).point
      have h3 := congr_arg (λ x ↦ x ≫ (εApp z).map (s.fst.map g).point) hgNatNatF
      dsimp at h3
      simp only [Category.assoc, eqToHom_app (εNaturality g).symm] at h3
      simp only [h1, h2, map_comp, comp_fiber, Category.assoc, lift_map_fiber,
        eqToHom_map (A.map (s.snd.map g)),
        eqToHom_app (εNaturality f).symm,
        eqToHom_app (εNaturality (f ≫ g)).symm,
        eqToHom_app (εNaturality g).symm, eqToHom_map]
      rw [h3]
      simp
    · simp
      rfl -- TODO fix

def lift' (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
    s.pt ⟶ uLiftGrothendieck A := (lift s) ⋙ ULift.upFunctor

theorem fac_left_aux (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
    lift s ⋙ Grothendieck.toPCat A = s.fst ⋙ downFunctor := by
  apply Functor.ext
  · intro x y f
    simp only [lift, lift_obj, Cat.of_α, comp_obj, downFunctor_obj, PCat.forgetToCat_obj, upFunctor_obj_down,
      toPCat, toPCatMap, toPCatObj_α, Functor.comp_map, lift_map_base, downFunctor_map]
    have h := Functor.congr_hom condition' f
    unfold uLiftPCatForgetToCat PCat.forgetToCat at h
    simp only [Cat.of_α, π_app_left, comp_obj, downFunctor_obj, Functor.comp_map, downFunctor_map,
      π_app_right] at h
    congr 1
    · simp [h, PCat.eqToHom_toFunctor, ← Cat.comp_eq_comp]
    · simp only [lift_map, lift_obj, comp_obj, PCat.forgetToCat_obj, Cat.of_α, downFunctor_obj, ε,
        Functor.comp_map, downFunctor_map, Cat.comp_obj, PCat.forgetToCat_map, Cat.eqToHom_app,
        PCat.eqToHom_point, eqToHom_map, PCat.comp_point, heq_eqToHom_comp_iff,
        heq_comp_eqToHom_iff, eqToHom_comp_heq_iff]
      generalize_proofs
      rename_i h1 h2
      simp only [Functor.congr_hom (eqToHom_app h1 y) (point' f), comp_obj, downFunctor_obj,
        PCat.forgetToCat_obj, Cat.of_α, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      refine heq_of_cast_eq ?_ ?_
      · congr 1 <;> simp [PCat.eqToHom_toFunctor]
      · simp [Cat.eqToHom_hom,PCat.eqToHom_hom]
  · intro x
    simp only [toPCat, toPCatObj, toPCatMap, lift, lift_obj, comp_obj,
      downFunctor_obj, Cat.eqToHom_app, upFunctor_obj_down]
    have h := (Functor.congr_obj condition' x).symm
    simp only [Cat.comp_obj, comp_obj, downFunctor_obj, PCat.forgetToCat_obj] at h
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

theorem fac_left (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
    lift s ⋙ Grothendieck.toPCat A ⋙ upFunctor = s.fst := by
    rw [← comp_downFunctor_inj]
    exact fac_left_aux.{v,u} s

theorem fac_right (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
    lift s ⋙ Grothendieck.forget A ⋙ upFunctor
    = s.snd := by
  apply Functor.ext
  · intro x y f
    simp [lift]
  · intro
    simp [lift, upFunctor]

theorem eqToHom_base' {Γ : Cat.{u,u}}{A : Γ ⥤ Cat.{u,u}} (g1 g2 : Grothendieck A)
  (eq : g1 = g2) : (eqToHom eq).base = (eqToHom (congrArg (Grothendieck.forget A).obj eq)) := by
    cases eq
    simp

/-- This theorem is used to eliminate eqToHom from both sides of an equation-/
theorem eqToHom_comp_self_comp_eqToHom {C : Type u} [Category.{v} C] {x x1 x2 y y1 y2: C} (eqx1 : x = x1)(eqx2 : x = x2)
  (eqy1 : y1 = y)(eqy2 : y2 = y){f : x1 ⟶ y1}{g : x2 ⟶ y2}(heq : HEq f g) : eqToHom eqx1 ≫ f ≫ eqToHom eqy1 = eqToHom eqx2 ≫ g ≫ eqToHom eqy2:= by
    cases eqx1
    cases eqx2
    cases eqy1
    cases eqy2
    simp
    simp at heq
    exact heq

theorem uniq (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) (m : s.pt ⥤ Grothendieck A)
    (hl : m ⋙ Grothendieck.toPCat A = s.fst ⋙ downFunctor)
    (hr : m ⋙ Grothendieck.forget A = s.snd ⋙ downFunctor) :
    m = lift s := by
  apply Functor.ext
  · intro x y f
    apply Grothendieck.ext
    · dsimp [lift]
      rw [lift_map_fiber']
      generalize_proofs pf1 pf2 _ _ _ _ _ _ pf3
      have h0 := Functor.congr_hom hl f
      have h1 := PointedFunctor.congr_point h0
      have h2 := @eqToHom_fiber (Cat.of Γ) A (m.obj x) _ pf1
      have h3 := @eqToHom_fiber (Cat.of Γ) A _ _ pf2
      have h4 := congr_arg A.map (eqToHom_base pf2)
      simp only [eqToHom_map] at h4
      have h5 := Functor.congr_hom h4 (cast pf3 (point' f))
      simp only [toPCat, toPCatObj, toPCatMap, comp_obj, Functor.comp_map,
        PCat.comp_toFunctor, PCat.comp_point] at h1
      simp only [h1, h2, h3, h5, PCat.eqToHom_point, eqToHom_map, eqToHom_trans_assoc, eqToHom_fiber,
        PCat.forgetToCat_obj, Cat.of_α, downFunctor_obj, map_comp, Category.assoc, eqToHom_trans]
      simp only [PCat.eqToHom_hom, Functor.congr_hom (map_eqToHom_base _), Cat.eqToHom_hom, cast_cast,
        Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      refine eqToHom_comp_self_comp_eqToHom _ _ _ _ ?_
      apply @HEq.trans _ _ _ _ (s.fst.map f).point
      · apply cast_heq
      · apply HEq.symm
        apply cast_heq
    · simp only [comp_base, eqToHom_base, Functor.congr_hom hr f]
      exact Functor.congr_hom hr f
  · intro x
    apply Grothendieck.obj_ext_hEq
    · exact Functor.congr_obj hr x
    · apply toPCatObj_fiber_inj
      have h0 := Functor.congr_obj hl x
      have h1 := Functor.congr_obj (fac_left_aux s) x
      simp [congr_arg_heq (λ x : PCat ↦ x.str.pt) (h0.trans h1.symm)]

theorem uniq' (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) (m : s.pt ⟶ uLiftGrothendieck A)
    (hl : m ≫ uLiftToPCat A = s.fst) (hr : m ≫ uLiftGrothendieckForget A = s.snd) :
    m = lift' s := by
  unfold lift'
  rw [← uniq s (m ⋙ downFunctor) (congr_arg (λ F ↦ F ⋙ downFunctor) hl)
    (by
      simp only [Cat.of_α, Functor.assoc, ← hr, uLiftGrothendieckForget, Cat.comp_eq_comp]
      rfl)]
  aesop_cat

variable (A)

def isLimit : IsLimit (cone A) :=
  IsLimit.mk comm_sq lift' fac_left fac_right uniq'

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
