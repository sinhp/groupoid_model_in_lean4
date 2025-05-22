import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import GroupoidModel.Pointed.Basic
import GroupoidModel.ForMathlib
import GroupoidModel.ForMathlib.CategoryTheory.Functor.IsPullback

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace Grothendieck

open Functor

section morphism_universe_v₁


variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Cat.{v₁,u₁}}

@[simps] def toPCatObj (x : Grothendieck A) : PCat.{v₁,u₁} :=
  ⟨ A.obj x.base, x.fiber ⟩

@[simps] def toPCatMap {x y : Grothendieck A} (f : x ⟶ y) :
    toPCatObj x ⟶ toPCatObj y :=
  ⟨ A.map f.base , f.fiber ⟩

variable (A)

-- JH: TODO (maybe) factor through `Grothendieck.functorTo`
@[simps] def toPCat : Grothendieck A ⥤ PCat.{v₁,u₁} where
  obj := toPCatObj
  map := toPCatMap
  map_id x := by
    apply Grothendieck.ext
    · simp
    · simp
  map_comp {x y z} f g := by
    apply Grothendieck.ext
    · simp
    · simp

namespace IsMegaPullback

-- formerly duplicated as `toPCat_comp_forgetPoint`
theorem comm_sq : toPCat A ⋙ PCat.forgetToCat
  = Grothendieck.forget A ⋙ A := rfl

variable {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PCat.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PCat.forgetToCat = snd ⋙ A)

abbrev pt (x : C) := (fst.obj x).fiber

abbrev point {x y : C} (f : x ⟶ y) :
    (fst.map f)⟱.obj (pt fst x) ⟶ pt fst y :=
  (fst.map f).fiber

variable {A} {fst} {snd}

@[simps] def liftObj (x : C) : Grothendieck A :=
  ⟨ snd.obj x , ((eqToHom w).app x).obj (pt fst x) ⟩

variable {x y : C} (f : x ⟶ y)

def liftMap : liftObj w x ⟶ liftObj w y :=
  ⟨ (snd.map f) ,
    let m1 := ((eqToHom w).app y).map (point fst f)
    let m2 := (eqToHom ((eqToHom w).naturality f).symm).app
      (pt fst x)
    m2 ≫ m1 ⟩

@[simp] theorem liftMap_base :
  (liftMap w f).base = (snd.map f) := rfl

theorem liftMap_fiber :
    (liftMap w f).fiber =
      (eqToHom ((eqToHom w).naturality f).symm).app (pt fst x)
        ≫ ((eqToHom w).app y).map (point fst f) :=
  rfl

variable (fst) (snd)

-- TODO JH: (maybe) factor through Grothendieck.functorTo
@[simps] def lift : C ⥤ Grothendieck A where
  obj := liftObj w
  map := liftMap w
  map_id x := by
    apply Grothendieck.ext
    · simp [liftMap_fiber, eqToHom_app, eqToHom_map]
    · simp
  map_comp {x y z} f g := by
    apply Grothendieck.ext
    · have hgNatNatF := (eqToHom ((eqToHom w).naturality g).symm).naturality (fst.map f).fiber
      have h := congr_arg (λ x ↦ x ≫ ((eqToHom w).app z).map (fst.map g).fiber) hgNatNatF
      dsimp at h
      simp only [Category.assoc, eqToHom_app ((eqToHom w).naturality g).symm] at h
      simp [liftMap_fiber, eqToHom_map, h]
    · simp

@[simp] theorem fac_right : lift fst snd w ⋙ Grothendieck.forget A = snd := by
  apply CategoryTheory.Functor.ext
  · simp
  · simp

@[simp] theorem fac_left : lift fst snd w ⋙ Grothendieck.toPCat A = fst := by
  apply CategoryTheory.Functor.ext
  · intro x y f
    apply Grothendieck.ext
    · simp [liftMap, forget_map, eqToHom_map, PCat.eqToHom_base_map,
        Functor.congr_hom (eqToHom_app w y) (point fst f)]
    · have h := Functor.congr_hom w f
      simp only [PCat.forgetToCat_map, Functor.comp_map] at h
      simp [h, ← Cat.comp_eq_comp]
  · intro x
    have h := (Functor.congr_obj w x).symm
    simp only [Cat.comp_obj, Functor.comp_obj, forget_obj] at h
    fapply obj_hext
    · simp [h]
    · simp [h, Cat.eqToHom_obj]

theorem lift_uniq (m : C ⥤ Grothendieck A)
    (hl : m ⋙ Grothendieck.toPCat A = fst)
    (hr : m ⋙ Grothendieck.forget A = snd) :
    m = lift _ _ w := by
  apply Grothendieck.Functor.ext
  · rw [hr, fac_right]
  · intro x
    have h := Functor.congr_obj hl x
    simp only [Functor.comp_obj, toPCat_obj, ← obj_hext_iff, toPCatObj_base,
      toPCatObj_fiber] at h
    simp [Cat.eqToHom_obj, h, pt]
  · intro x y f
    have h := Functor.congr_hom hl f
    rw [← Grothendieck.hext_iff] at h
    simp only [h.2, lift_map, liftMap_fiber]
    aesop

theorem hom_ext {m n : C ⥤ Grothendieck A}
    (hl : m ⋙ Grothendieck.toPCat A = n ⋙ Grothendieck.toPCat A)
    (hr : m ⋙ Grothendieck.forget A = n ⋙ Grothendieck.forget A) :
    m = n := by
  rw [lift_uniq (m ⋙ toPCat A) (m ⋙ forget A) ?_ m rfl rfl,
    lift_uniq (n ⋙ toPCat A) (n ⋙ forget A) ?_ n rfl rfl]
  rw! [hl, hr]
  . show n ⋙ (toPCat A ⋙ PCat.forgetToCat) = _
    rw [comm_sq]
    rfl
  . show m ⋙ (toPCat A ⋙ PCat.forgetToCat) = _
    rw [comm_sq]
    rfl

def lift' : Functor.Pullback
    (Functor.PullbackCone.mk (toPCat A) (Grothendieck.forget _) (comm_sq _))
    (Functor.PullbackCone.mk fst snd w) where
  lift := lift fst snd w
  fac_left := fac_left _ _ _
  fac_right := fac_right _ _ _
  hom_ext _ _ := hom_ext


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
  apply CategoryTheory.Functor.ext
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
    (x : s.pt) := (downFunctor.obj (s.fst.obj x)).fiber

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
