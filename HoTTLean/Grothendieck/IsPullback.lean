import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import HoTTLean.Pointed.Basic
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.CategoryTheory.Functor.IsPullback

universe v u v₁ u₁ v₂ u₂ v₃ u₃

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

namespace Functor.Grothendieck

open Functor.IsPullback

section


variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Cat.{v₁,u₁}}

variable (A)

def toPCat : ∫ A ⥤ PCat.{v₁,u₁} :=
  functorTo (forget _ ⋙ A) (fun x => x.fiber) (fun f => f.fiber)
    (by simp) (by intros; simp)

@[simp] theorem toPCat_obj_base (x) :
    ((toPCat A).obj x).base = A.obj x.base := by
  rfl

@[simp] theorem toPCat_obj_fiber (x) :
    ((toPCat A).obj x).fiber = x.fiber := by
  rfl

@[simp] theorem toPCat_map_base {x y} (f : x ⟶ y) :
    ((toPCat A).map f).base = A.map f.base := by
  rfl

@[simp] theorem toPCat_map_fiber {x y} (f : x ⟶ y) :
    ((toPCat A).map f).fiber = f.fiber := by
  rfl

-- formerly duplicated as `toPCat_comp_forgetPoint` and `comm_sq`
theorem toPCat_forgetToCat : toPCat A ⋙ PCat.forgetToCat
  = Grothendieck.forget A ⋙ A :=
  rfl

namespace IsPullback

variable {C : Type*} [Category C]
  (fst : C ⥤ PCat.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PCat.forgetToCat = snd ⋙ A)

abbrev pt (x : C) := (fst.obj x).fiber

abbrev point {x y : C} (f : x ⟶ y) :
    (fst.map f)⟱.obj (pt fst x) ⟶ pt fst y :=
  (fst.map f).fiber

variable {A} {fst} {snd}

@[simp] def liftObjFiber (x : C) : A.obj (snd.obj x) :=
  ((eqToHom w).app x).toFunctor.obj (pt fst x)

variable {x y : C} (f : x ⟶ y)

@[simp] def liftMapFiber : ((snd ⋙ A).map f).toFunctor.obj (liftObjFiber w x) ⟶ liftObjFiber w y :=
  let m1 := ((eqToHom w).app y).toFunctor.map (point fst f)
  let m2 := (eqToHom ((eqToHom w).naturality f).symm).toNatTrans.app
    (pt fst x)
  m2 ≫ m1

theorem liftMapFiber_id (x : C) : liftMapFiber w (𝟙 x) = eqToHom (by simp) := by
  simp [eqToHom_map]

theorem liftMapFiber_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    liftMapFiber w (f ≫ g) =
    eqToHom (by simp)
    ≫ (A.map (snd.map g)).toFunctor.map (liftMapFiber w f)
    ≫ liftMapFiber w g := by
  have hgNatNatF := (eqToHom ((eqToHom w).naturality g).symm).toNatTrans.naturality (fst.map f).fiber
  have h := congr_arg (λ x ↦ x ≫ ((eqToHom w).app z).toFunctor.map (fst.map g).fiber) hgNatNatF
  dsimp at h
  simp only [Category.assoc, Cat.eqToHom_app _ _ ((eqToHom w).naturality g).symm] at h
  simp [eqToHom_map, h]

variable (fst) (snd)

def lift : C ⥤ Grothendieck A := functorTo snd
    (liftObjFiber w)
    (liftMapFiber w)
    (liftMapFiber_id w)
    (liftMapFiber_comp w)

@[simp] theorem lift_obj_base (x) :
    ((lift fst snd w).obj x).base = snd.obj x := by
  simp [lift]

@[simp] theorem lift_obj_fiber (x) :
    ((lift fst snd w).obj x).fiber = liftObjFiber w x := by
  simp [lift]

@[simp] theorem lift_map_base {x y} (f : x ⟶ y) :
    ((lift fst snd w).map f).base = snd.map f := by
  simp [lift]

@[simp] theorem lift_map_fiber {x y} (f : x ⟶ y) :
    ((lift fst snd w).map f).fiber = liftMapFiber w f := by
  simp [lift]

@[simp] theorem fac_right : lift fst snd w ⋙ Grothendieck.forget A = snd := by
  apply CategoryTheory.Functor.ext
  · simp
  · simp

@[simp] theorem fac_left : lift fst snd w ⋙ Grothendieck.toPCat A = fst := by
  apply Grothendieck.FunctorTo.hext
  · rw [Functor.assoc, toPCat_forgetToCat, ← Functor.assoc, fac_right]
    exact w.symm
  · intro x
    simp [lift, toPCat, Cat.eqToHom_obj]
  · intro x y f
    simp [lift, toPCat, liftMapFiber, point]
    refine (eqToHom_comp_heq (((eqToHom w).app y).toFunctor.map (fst.map f).fiber) _).trans ?_
    have hw : (eqToHom w).app y = eqToHom (Functor.congr_obj w y) := eqToHom_app w y
    rw [hw]
    exact Cat.eqToHom_map_heq (Functor.congr_obj w y) (fst.map f).fiber

theorem lift_uniq (m : C ⥤ Grothendieck A)
    (hl : m ⋙ Grothendieck.toPCat A = fst)
    (hr : m ⋙ Grothendieck.forget A = snd) :
    m = lift _ _ w := by
  apply Grothendieck.FunctorTo.hext
  · rw [hr, fac_right]
  · aesop
  · aesop

theorem hom_ext {m n : C ⥤ Grothendieck A}
    (hl : m ⋙ Grothendieck.toPCat A = n ⋙ Grothendieck.toPCat A)
    (hr : m ⋙ Grothendieck.forget A = n ⋙ Grothendieck.forget A) :
    m = n := by
  have hm : (m ⋙ toPCat A) ⋙ PCat.forgetToCat = (m ⋙ forget A) ⋙ A := by
    rw [Functor.assoc, toPCat_forgetToCat, ← Functor.assoc]
  have hn : (n ⋙ toPCat A) ⋙ PCat.forgetToCat = (n ⋙ forget A) ⋙ A := by
    rw [Functor.assoc, toPCat_forgetToCat, ← Functor.assoc]
  rw [lift_uniq (m ⋙ toPCat A) (m ⋙ forget A) hm m rfl rfl,
    lift_uniq (n ⋙ toPCat A) (n ⋙ forget A) hn n rfl rfl]
  rw! [hl, hr]
  congr 1

def aux {C : Type*} [inst : Category C] (Cn : C ⥤ PCat) (Cw : C ⥤ Γ)
    (hC : Cn ⋙ forget (𝟭 Cat) = Cw ⋙ A) :
    (lift : C ⥤ Grothendieck A) ×'
    lift ⋙ toPCat A = Cn ∧
    lift ⋙ forget A = Cw ∧
    ∀ {l0 l1 : C ⥤ Grothendieck A}, l0 ⋙ toPCat A = l1 ⋙ toPCat A →
    l0 ⋙ forget A = l1 ⋙ forget A → l0 = l1 :=
  ⟨ lift Cn Cw hC, fac_left _ _ _, fac_right _ _ _, hom_ext ⟩

end IsPullback

open IsPullback

/--
The following square is a (meta-theoretic) pullback of functors
  Grothendieck A --- toPCat ----> PCat
        |                           |
        |                           |
 Grothendieck.forget        PCat.forgetToCat
        |                           |
        v                           v
        Γ--------------A---------> Cat
-/
def isPullback : Functor.IsPullback (toPCat A) (forget _) (forget _) A :=
  ofUniversal (toPCat A) (forget _) (forget _) A (toPCat_forgetToCat _)
  (fun Cn Cw hC => aux Cn Cw hC)
  (fun Cn Cw hC => aux Cn Cw hC)

end

-- TODO verify that the rest of this file is no longer needed
-- /-
-- In this section we build the lemmas for showing the pullback

--   Grothendieck A --- toPCat ----> PCat
--         |                           |
--         |                           |
--  Grothendieck.forget        PCat.forgetToCat
--         |                           |
--         v                           v
--         Γ--------------A---------> Cat
-- in the appropriately sized category `Cat.{v, max u (v+1)}`;
-- where `(Γ : Type u) [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v})`.

-- This particular choice of hom universe level avoids using ULiftHom.
-- In our applications either `u = v` for a small `Γ`
-- so that `A : Γ ⥤ Cat.{u,u}`,
-- or `Γ = Grpd.{v,v}` and `A : Grpd.{v,v} ⥤ Cat.{v,v}` is the inclusion
-- so that `u = v + 1`.
-- -/
-- namespace IsPullback

-- variable (Γ : Type u) [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v})

-- open Functor ULift

-- variable {Γ}

-- abbrev uLiftGrothendieck : Cat.{v, max u (v+1)} :=
--   Cat.ofULift.{max u (v+1)} (Grothendieck A)

-- abbrev uLiftGrothendieckForget :
--     uLiftGrothendieck.{v,u} A ⟶ Cat.ofULift.{v+1} Γ :=
--   downFunctor ⋙ Grothendieck.forget A ⋙ upFunctor

-- abbrev uLiftCat : Cat.{v, max u (v+1)} :=
--   Cat.ofULift.{max u (v+1)} Cat.{v,v}

-- abbrev uLiftPCat : Cat.{v, max u (v+1)} :=
--   Cat.ofULift.{max u (v+1)} PCat.{v,v}

-- abbrev uLiftPCatForgetToCat : uLiftPCat.{v,u} ⟶ uLiftCat.{v,u} :=
--   downFunctor ⋙ PCat.forgetToCat ⋙ upFunctor

-- abbrev uLiftToPCat : uLiftGrothendieck.{v,u} A ⟶ uLiftPCat.{v,u} :=
--   ULift.downFunctor ⋙ Grothendieck.toPCat A ⋙ ULift.upFunctor

-- abbrev uLiftA : Cat.ofULift.{v+1} Γ ⥤ uLiftCat.{v,u} :=
--   downFunctor ⋙ A ⋙ upFunctor

-- variable {A}

-- theorem comm_sq : uLiftToPCat A ≫ uLiftPCatForgetToCat
--     = uLiftGrothendieckForget A ≫ uLiftA A := by
--   apply CategoryTheory.Functor.ext
--   · intro X Y f
--     rfl
--   · intro
--     rfl

-- variable (A)

-- open Limits PullbackCone

-- def cone : Limits.PullbackCone uLiftPCatForgetToCat (uLiftA A)
--   := Limits.PullbackCone.mk (uLiftToPCat A) (uLiftGrothendieckForget A) comm_sq

-- variable {A}

-- abbrev pt' {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)}
--     (x : s.pt) := (downFunctor.obj (s.fst.obj x)).fiber

-- theorem condition' {s : PullbackCone uLiftPCatForgetToCat (uLiftA A)} :
--     s.fst ⋙ downFunctor ⋙ PCat.forgetToCat = s.snd ⋙ downFunctor ⋙ A := by
--   rw [← comp_upFunctor_inj.{_,_,_,_,max u (v + 1)}]
--   exact s.condition

-- variable {s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)} {x y : s.pt} {f : x ⟶ y}

-- def lift (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) :
--     s.pt ⥤ Grothendieck A :=
--   IsMegaPullback.lift
--     (s.fst ⋙ downFunctor)
--     (s.snd ⋙ downFunctor)
--     condition'

-- def lift' (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
--     s.pt ⟶ uLiftGrothendieck A := (lift s) ⋙ ULift.upFunctor

-- theorem fac_left (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
--     lift s ⋙ Grothendieck.toPCat A ⋙ upFunctor = s.fst := by
--   rw [← comp_downFunctor_inj]
--   exact IsMegaPullback.fac_left
--     (s.fst ⋙ downFunctor)
--     (s.snd ⋙ downFunctor)
--     condition'

-- theorem fac_right (s : PullbackCone uLiftPCatForgetToCat (uLiftA A)) :
--     lift s ⋙ Grothendieck.forget A ⋙ upFunctor
--     = s.snd := by
--   rw [← comp_downFunctor_inj]
--   exact IsMegaPullback.fac_right
--     (s.fst ⋙ downFunctor)
--     (s.snd ⋙ downFunctor)
--     condition'

-- theorem lift_uniq (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) (m : s.pt ⥤ Grothendieck A)
--     (hl : m ⋙ Grothendieck.toPCat A = s.fst ⋙ downFunctor)
--     (hr : m ⋙ Grothendieck.forget A = s.snd ⋙ downFunctor) :
--     m = lift s :=
--   IsMegaPullback.lift_uniq
--     (s.fst ⋙ downFunctor) (s.snd ⋙ downFunctor) condition' m hl hr

-- theorem lift_uniq' (s : PullbackCone uLiftPCatForgetToCat.{v,u} (uLiftA.{v,u} A)) (m : s.pt ⟶ uLiftGrothendieck A)
--     (hl : m ≫ uLiftToPCat A = s.fst) (hr : m ≫ uLiftGrothendieckForget A = s.snd) :
--     m = lift' s := by
--   unfold lift'
--   rw [← lift_uniq s (m ⋙ downFunctor) (congr_arg (λ F ↦ F ⋙ downFunctor) hl)
--     (by
--       simp only [Cat.of_α, Functor.assoc, ← hr, uLiftGrothendieckForget, Cat.comp_eq_comp]
--       rfl)]
--   aesop_cat

-- variable (A)

-- def isLimit : IsLimit (cone A) :=
--   IsLimit.mk comm_sq lift' fac_left fac_right lift_uniq'

-- end IsPullback

-- open IsPullback

-- /-
-- The following square is a pullback

--   Grothendieck A --- toPCat ----> PCat
--         |                           |
--         |                           |
--  Grothendieck.forget        PCat.forgetToCat
--         |                           |
--         v                           v
--         Γ--------------A---------> Cat
-- in the appropriately sized category `Cat.{v, max u (v+1)}`;
-- where `(Γ : Type u) [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v})`.

-- This particular choice of hom universe level avoids using ULiftHom.
-- In our applications either `u = v` for a small `Γ`
-- so that `A : Γ ⥤ Cat.{u,u}`,
-- or `Γ = Grpd.{v,v}` and `A : Grpd.{v,v} ⥤ Cat.{v,v}` is the inclusion
-- so that `u = v + 1`.
-- -/
-- theorem isPullback {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Cat.{v,v}) :
--     IsPullback
--       (uLiftToPCat A)
--       (uLiftGrothendieckForget A)
--       (uLiftPCatForgetToCat)
--       (uLiftA A) :=
--   IsPullback.of_isLimit (isLimit A)

end Functor.Grothendieck

end CategoryTheory
