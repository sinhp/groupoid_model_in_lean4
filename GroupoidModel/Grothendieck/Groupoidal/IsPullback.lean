import GroupoidModel.Pointed.IsPullback
import GroupoidModel.Grothendieck.Groupoidal.Basic

import SEq.Tactic.DepRewrite

/-!
# The Groupidal Grothendieck construction

       ∫(A) ------- toPGrpd ---------> PGrpd
        |                                 |
        |                                 |
     forget                     PGrpd.forgetToGrpd
        |                                 |
        v                                 v
        Γ--------------A---------------> Grpd
-/

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace Grothendieck

namespace Groupoidal

section

variable {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Grpd.{v₁,u₁})

/--
`toPGrpd` is the lift induced by the pullback property of `PGrpd`
       ∫(A) ------- toPGrpd ---------> PGrpd --------> PCat
        |                                 |              |
        |                                 |              |
     forget                     PGrpd.forgetToGrpd      PCat.forgetToCat
        |                                 |              |
        |                                 |              |
        v                                 v              v
        Γ--------------A---------------> Grpd --------> Cat
-/
def toPGrpd : ∫(A) ⥤ PGrpd.{v₁,u₁} := Functor.Pullback.ofRight'Lift
  (Grothendieck.IsMegaPullback.comm_sq (A ⋙ Grpd.forgetToCat))
  PGrpd.forgetToPCat_forgetToCat PGrpd.pullback

theorem toPGrpd_forgetToGrpd :
    toPGrpd A ⋙ PGrpd.forgetToGrpd = forget ⋙ A :=
  Functor.Pullback.ofRight'CommSq _ _ _

def pullback' {C : Type u₂} [Category.{v₂} C]
    (cone : Functor.PullbackCone C (PCat.forgetToCat) (A ⋙ Grpd.forgetToCat)) :
    Functor.Pullback
    (Functor.PullbackCone.mk (toPCat _) (Grothendieck.forget _) (Grothendieck.IsMegaPullback.comm_sq _))
    cone := Grothendieck.pullback.{_,_,_,_,v₂,u₂} (A ⋙ Grpd.forgetToCat) cone

/--
The left square is a pullback since the right square and outer square are.
       ∫(A) ------- toPGrpd ---------> PGrpd --------> PCat
        |                                 |              |
        |                                 |              |
     forget                     PGrpd.forgetToGrpd      PCat.forgetToCat
        |                                 |              |
        |                                 |              |
        v                                 v              v
        Γ--------------A---------------> Grpd --------> Cat
-/
def pullback {C : Type u₂} [Category.{v₂} C]
    (cone : Functor.PullbackCone C (PGrpd.forgetToGrpd) A) :
    Functor.Pullback (Functor.PullbackCone.mk (toPGrpd A)
      (Grothendieck.forget _)
      (toPGrpd_forgetToGrpd A))
    cone := by
  -- have h := @Functor.Pullback.ofRight'.{v₂,u₂} PGrpd PCat Grpd Cat _ _ _ _ ∫(A) Γ _ _
  --   (Grothendieck.toPCat (A ⋙ Grpd.forgetToCat)) PGrpd.forgetToPCat forget
  --   PGrpd.forgetToGrpd PCat.forgetToCat A Grpd.forgetToCat
  --   (Grothendieck.IsMegaPullback.comm_sq (A ⋙ Grpd.forgetToCat))
  --   PGrpd.forgetToPCat_forgetToCat
  --   PGrpd.pullback
  --   (pullback' A)
  --   C
    -- _ _
    -- cone
    -- (toPGrpd_forgetToGrpd A)

  -- apply h
  -- (Grothendieck.IsMegaPullback.comm_sq (A ⋙ Grpd.forgetToCat)) (toPGrpd_forgetToGrpd A) (fun cone' => PGrpd.pullback.{_,_,v₂,u₂} cone') (fun cone' => Grothendieck.pullback.{_,_,_,_,v₂,u₂} (A ⋙ Grpd.forgetToCat) cone') cone
  sorry

-- def pullback {C : Type*} [Category C]
--     (cone : Functor.PullbackCone C (PGrpd.forgetToGrpd) A) :=
--   Functor.Pullback.ofRight' _ _ PGrpd.pullback (pullback' A) cone

end
#exit
section

variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}

variable (A) in
def toPGrpd : ∫(A) ⥤ PGrpd.{v₁,u₁} :=
  IsMegaPullback.lift (toPCat (A ⋙ Grpd.forgetToCat)) (forget ⋙ A) rfl

theorem toPGrpd_forgetToPCat :
    toPGrpd A ⋙ PGrpd.forgetToPCat = toPCat (A ⋙ Grpd.forgetToCat) :=
  IsMegaPullback.fac_left _ _ _

-- This is probably a better name
-- theorem toPGrpd_forget :
--     toPGrpd A ⋙ PGrpd.forgetToGrpd = Grothendieck.forget _ ⋙ A :=
--   IsMegaPullback.fac_right _ _ _

namespace IsMegaPullback

theorem comm_sq : toPGrpd A ⋙ PGrpd.forgetToGrpd = forget ⋙ A :=
  IsMegaPullback.fac_right _ _ _

variable {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PGrpd.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PGrpd.forgetToGrpd = snd ⋙ A)

def lift : C ⥤ Groupoidal A :=
  Grothendieck.IsMegaPullback.lift
    (fst ⋙ PGrpd.forgetToPCat) snd (by
      simp only [← Functor.assoc, ← w]
      rfl)

@[simp] theorem fac_left : lift fst snd w ⋙ toPGrpd _ = fst := by
  apply Grothendieck.IsMegaPullback.hom_ext
  · calc lift _ _ _ ⋙ toPGrpd _ ⋙ toPCat _
      _ = lift _ _ _ ⋙ toPCat _ := by
        rw [← toPGrpd_forgetToPCat]; rfl
      _ = fst ⋙ PGrpd.forgetToPCat :=
        (@Grothendieck.IsMegaPullback.fac_left _ _ (A ⋙ Grpd.forgetToCat) _ _
        (fst ⋙ PGrpd.forgetToPCat) snd (by rw [← Functor.assoc, ← w]; rfl))
  · calc lift _ _ _ ⋙ toPGrpd _ ⋙ Grothendieck.forget _
      _ = snd ⋙ A := by
        conv => right; rw [← @Grothendieck.IsMegaPullback.fac_right _ _
          (A ⋙ Grpd.forgetToCat) _ _ (fst ⋙ PGrpd.forgetToPCat) snd
          (by rw [← Functor.assoc, ← w]; rfl)]
        rfl
      _ = fst ⋙ Grothendieck.forget _ := by
        rw [w]

@[simp] theorem fac_right :
    lift fst snd w ⋙ Groupoidal.forget
    = snd :=
  Grothendieck.IsMegaPullback.fac_right
    (fst ⋙ PGrpd.forgetToPCat) snd (
      calc fst ⋙ (PGrpd.forgetToPCat ⋙ PCat.forgetToCat)
       _ = (fst ⋙ Grothendieck.forget _) ⋙ Grpd.forgetToCat := by
         rw [PGrpd.forgetToPCat_forgetToCat]; rfl
       _ = snd ⋙ A ⋙ Grpd.forgetToCat := by rw [w, Functor.assoc])

theorem lift_uniq (m : C ⥤ Groupoidal A)
    (hl : m ⋙ toPGrpd _ = fst)
    (hr : m ⋙ Groupoidal.forget = snd) :
    m = lift _ _ w := by
  apply Grothendieck.IsMegaPullback.lift_uniq
  · rw [← toPGrpd_forgetToPCat, ← hl, Functor.assoc]
  · exact hr

theorem hom_ext {m n : C ⥤ Groupoidal A}
    (hl : m ⋙ toPGrpd _ = n ⋙ toPGrpd _)
    (hr : m ⋙ Groupoidal.forget = n ⋙ Groupoidal.forget) :
    m = n := by
  rw [lift_uniq (m ⋙ toPGrpd _) (m ⋙ forget) rfl m rfl rfl,
    lift_uniq (n ⋙ toPGrpd _) (n ⋙ forget) rfl n rfl rfl]
  rw! [hl, hr]

end IsMegaPullback

namespace IsPullback

open Grothendieck.IsPullback ULift

variable {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

abbrev uLiftGrpd : Cat.{u, max u (u+1)} :=
  Cat.ofULift.{max u (u+1)} Grpd.{u}

abbrev uLiftA : Cat.ofULift.{u+1} Γ ⟶ uLiftGrpd.{u} :=
  downFunctor ⋙ A ⋙ upFunctor

abbrev uLiftPGrpd : Cat.{u, max u (u+1)} :=
  Cat.ofULift.{max u (u+1)} PGrpd.{u,u}

abbrev uLiftPGrpdForgetToGrpd : uLiftPGrpd.{u} ⟶ uLiftGrpd.{u} :=
  downFunctor ⋙ PGrpd.forgetToGrpd ⋙ upFunctor

/--
The universal lift
`var' : ∫(A) ⟶ Grothendieck(Grpd.forgetToCat)`
given by pullback pasting in the following pasting diagram.

      ∫(A)  .-.-.-.-.-.-.-> ↑GrothendieckForgetToCat -----> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
noncomputable def var' :
    IsPullback.uLiftGrothendieck (A ⋙ Grpd.forgetToCat)
    ⟶ IsPullback.uLiftGrothendieck Grpd.forgetToCat.{u,u} :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift
    (IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat))
    ((IsPullback.uLiftGrothendieckForget
      (A ⋙ Grpd.forgetToCat)) ≫ uLiftA A)
      (Grothendieck.isPullback
        (A ⋙ Grpd.forgetToCat)).cone.condition_one

theorem var'_uLiftToPCat :
    var' A ≫ (uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = uLiftToPCat (A ⋙ Grpd.forgetToCat) :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_fst
    (IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat))
    ((IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat)) ≫ uLiftA A)
    (Grothendieck.isPullback (A ⋙ Grpd.forgetToCat)).cone.condition_one

theorem var'_forget :
    var' A ≫ (uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    = uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat) ≫ uLiftA A :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_snd
    (IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat)) ((IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat)) ≫ uLiftA A)
    (Grothendieck.isPullback (A ⋙ Grpd.forgetToCat)).cone.condition_one


/--
The following square is a pullback
  ↑Grothendieck (Groupoid.compForgetToCat A) ------- var' -------> ↑Grothendieck Grpd.forgetToCat
        |                                                    |
        |                                                    |
↑ Grothendieck.forget                           ↑Grothendieck.forget
        |                                                    |
        v                                                    v
        ↑Γ--------------↑A----------------------------> ↑Grpd.{u,u}

by pullback pasting

  ↑Grothendieck (Groupoid.compForgetToCat A) --> ↑Grothendieck Grpd.forgetToCat ---> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
theorem
  isPullback_uLiftGrothendieckForget_Groupoid.compForgetToCat_uLiftGrothendieckForget_grpdForgetToCat :
    IsPullback
    (Cat.homOf (var' A))
    (IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat))
    (IsPullback.uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    (uLiftA A) :=
  IsPullback.of_right'
    (Grothendieck.isPullback (A ⋙ Grpd.forgetToCat))
    (Grothendieck.isPullback (Grpd.forgetToCat.{u,u}))

theorem isPullback_aux:
    IsPullback
      (Cat.homOf (var' A) ≫ Cat.ULift_iso_self.hom)
      (IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (uLiftA A ≫ Cat.ULift_iso_self.hom) :=
  IsPullback.paste_horiz
    (isPullback_uLiftGrothendieckForget_Groupoid.compForgetToCat_uLiftGrothendieckForget_grpdForgetToCat.{u} A)
    (PGrpd.IsPullback.isPullback_uLiftGrothendieckForget_forgetToGrpd.{u})

open ULift

variable {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

theorem toPGrpd_forgetToPCat_eq_var'_forgetToPCat :
    downFunctor ⋙ toPGrpd A ⋙ PGrpd.forgetToPCat
      = var' A ⋙ downFunctor ⋙ PGrpd.forgetToPCat := by
  have h : var' A ⋙ (IsPullback.uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat) := var'_uLiftToPCat A
  dsimp only [IsPullback.uLiftToPCat] at h
  simp only [Cat.ofULift, Cat.of_α, ← Functor.assoc,
    ← toPGrpd_forgetToPCat, comp_upFunctor_inj] at h
  simp only [Functor.assoc] at h
  rw [← h]
  rfl

theorem toPGrpd_forgetToGrpd_eq_var'_forgetToGrpd :
    downFunctor ⋙ toPGrpd A ⋙ PGrpd.forgetToGrpd
      = var' A ⋙ downFunctor ⋙ PGrpd.forgetToGrpd := by
  have h : downFunctor
      ⋙ PGrpd.forgetToGrpd.{u,u} =
      IsPullback.uLiftGrothendieckForget Grpd.forgetToCat.{u,u} ⋙ downFunctor :=
      PGrpd.IsPullback.isPullback_forgetToGrpd_uLiftGrothendieckForget_commSq.horiz_inv.{u,u}.w
  simp only [← toPGrpd_forgetToPCat, Functor.assoc] at h
  have h1 : var' A ⋙ IsPullback.uLiftGrothendieckForget Grpd.forgetToCat.{u}
      = IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat) ⋙ uLiftA A :=
    var'_forget A
  simp only [Cat.of_α, IsPullback.uLiftGrothendieckForget, ← Functor.assoc,
    uLiftA] at h1
  rw [comp_upFunctor_inj] at h1
  erw [h, ← Functor.assoc, h1]
  rfl

theorem toPGrpd_eq_var'' :
    Cat.homOf (downFunctor ⋙ toPGrpd A)
      = Cat.homOf (var' A ⋙ downFunctor)
      :=
  PGrpd.isPullback_forgetToGrpd_forgetToCat.{u}.hom_ext
    (toPGrpd_forgetToPCat_eq_var'_forgetToPCat _)
    (toPGrpd_forgetToGrpd_eq_var'_forgetToGrpd _)

theorem toPGrpd_eq_var' :
    downFunctor ⋙ toPGrpd A = var' A ⋙ downFunctor :=
  toPGrpd_eq_var'' _

end IsPullback

open Grothendieck
open IsPullback

/-
The following square is a pullback

       ∫(A)               -- toPGrpd -->                    PGrpd
        |                                                     |
        |                                                     |
↑ Grothendieck.forget                                PGrpd.forgetToGrpd
        |                                                     |
        |                                                     |
        v                                                     v
        ↑Γ-----------------------A-----------------------> Grpd
in the appropriately sized category `Grpd.{v, max u (v+1)}`;
where `(Γ : Type u) [Grpdegory.{v} Γ] (A : Γ ⥤ Grpd.{v,v})`.
-/
theorem isPullback {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u,u}) :
    IsPullback
      (Cat.homOf (ULift.downFunctor ⋙ toPGrpd A))
      (IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (Cat.homOf (ULift.downFunctor.{u,u} ⋙ A)) := by
  have h := isPullback_aux.{u} A
  simp at h
  convert h
  apply toPGrpd_eq_var'

end

section

variable {Γ : Type u} [Category.{v} Γ]
variable (A : Γ ⥤ Grpd.{v₁,u₁}) (α : Γ ⥤ PGrpd.{v₁,u₁}) (h : α ⋙ PGrpd.forgetToGrpd = A)

/-- `sec` is the universal lift in the following diagram,
  which is a section of `Groupoidal.forget`
             α
  ===== Γ -------α--------------¬
 ‖      ↓ sec                   V
 ‖   M.ext A ⋯ -------------> PGrpd
 ‖      |                        |
 ‖      |                        |
 ‖   forget                  forgetToGrpd
 ‖      |                        |
 ‖      V                        V
  ===== Γ --α ≫ forgetToGrpd--> Grpd
-/
def sec : Γ ⥤ ∫(A) :=
  IsMegaPullback.lift α (𝟭 _) (by simp [h, Functor.id_comp])

@[simp] def sec_toPGrpd : sec A α h ⋙ toPGrpd _ = α := by
  simp [sec]

@[simp] def sec_forget : sec A α h ⋙ forget = 𝟭 _ :=
  rfl

section naturality
variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

@[simp]
theorem pre_toPGrpd (A : Γ ⥤ Grpd) : pre A σ ⋙ toPGrpd _ = toPGrpd _ := by
  rfl

theorem sec_naturality : σ ⋙ sec A α h = sec (σ ⋙ A) (σ ⋙ α) (by rw [← h]; rfl) ⋙ pre A σ := by
  apply Groupoidal.IsMegaPullback.hom_ext
  . simp [Functor.assoc, Functor.comp_id]
  . conv_rhs => rw [Functor.assoc, pre_forget, ← Functor.assoc, sec_forget]
    simp [Functor.assoc, Functor.comp_id, Functor.id_comp]

end naturality

-- @[simp] lemma sec_obj_base (x) : ((sec A α h).obj x).base = x := by
--   rfl

-- @[simp] lemma sec_obj_fiber (x) :
--     ((sec A α h).obj x).fiber = PGrpd.objFiber' h x := by
--   simp [Grothendieck.Groupoidal.sec, PGrpd.objFiber',
--     Grothendieck.Groupoidal.IsMegaPullback.lift_obj_fiber]

-- @[simp] lemma sec_map_base {x y} {f : x ⟶ y} :
--     ((sec A α h).map f).base = f := by
--   simp [sec, IsMegaPullback.lift, Grothendieck.IsMegaPullback.lift]

-- -- TODO likely will also need the non-trivially forded case, in which case rename this
-- -- to `sec_map_fiber_rfl`
-- @[simp] lemma sec_map_fiber {x y} {f : x ⟶ y} :
--     ((sec (α ⋙ PGrpd.forgetToGrpd) α rfl).map f).fiber = (α.map f).point := by
--   simp [sec, Grothendieck.Groupoidal.IsMegaPullback.lift,
--     Grothendieck.IsMegaPullback.lift, Grothendieck.IsMegaPullback.point,
--     Grothendieck.IsMegaPullback.lift_map_fiber]

end



end Groupoidal
end Grothendieck
end CategoryTheory
