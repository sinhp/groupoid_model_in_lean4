import GroupoidModel.Pointed.IsPullback
import GroupoidModel.Grothendieck.Groupoidal.Basic

import SEq.Tactic.DepRewrite



namespace IsMegaPullback

theorem comm_sq : Groupoidal.toPGrpd A ⋙ PGrpd.forgetToGrpd = Groupoidal.forget ⋙ A := rfl

variable {A} {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PGrpd.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PGrpd.forgetToGrpd = snd ⋙ A)

theorem toPGrpd_eq_lift :
    toPGrpd A =
    PGrpd.IsMegaPullback.lift
      (toPCat (A ⋙ Grpd.forgetToCat))
      (Groupoidal.forget ⋙ A) rfl :=
  PGrpd.IsMegaPullback.lift_uniq
    (toPCat (A ⋙ Grpd.forgetToCat))
    (Groupoidal.forget ⋙ A)
    rfl _ rfl rfl

def lift : C ⥤ Groupoidal A :=
  Grothendieck.IsMegaPullback.lift
    (fst ⋙ PGrpd.forgetToPCat) snd (by
      simp only [← Functor.assoc, ← w]
      rfl)

@[simp] theorem lift_obj_base (x : C) :
    ((lift fst snd w).obj x).base = snd.obj x :=
  Grothendieck.IsMegaPullback.lift_obj_base _ _

theorem lift_obj_fiber (x : C) : ((lift fst snd w).obj x).fiber =
    ((eqToHom w).app x).obj (PGrpd.objPt fst x) := by
  erw [Grothendieck.IsMegaPullback.lift_obj_fiber]
  simp only [Grpd.forgetToCat, Functor.comp_obj,
  eqToHom_app, IsMegaPullback.pt, PGrpd.objPt, Cat.eqToHom_obj,
  Grpd.eqToHom_obj, cast_inj]
  rfl

@[simp] theorem lift_map_base {x y : C} (f : x ⟶ y) :
    ((lift fst snd w).map f).base = (snd.map f) :=
  rfl

include w in
theorem lift_map_fiber_aux (y : C) :
    Grpd.of (fst.obj y) = (A.obj (snd.obj y)) :=
  Functor.congr_obj w y

-- theorem lift_map_fiber {x y : C} (f : x ⟶ y) :
--     ((lift fst snd w).map f).fiber =
--       eqToHom sorry
--       ≫ (eqToHom (lift_map_fiber_aux fst snd w y)).map (fst.map f).point
--       ≫ eqToHom sorry := by
--   dsimp [lift, Grothendieck.IsMegaPullback.lift]
--   generalize_proofs h
--   simp only [Grothendieck.IsMegaPullback.lift_map_fiber, Cat.eqToHom_app]
--   have h1 : (eqToHom h).app y = eqToHom (by
--     have h2 := Functor.congr_obj w y
--     simp only [Functor.comp_obj, PGrpd.forgetToGrpd_obj, PGrpd.forgetToPCat_obj, PCat.forgetToCat_obj] at *
--     rw [← h2]
--     rfl) := by
--     rw [Grpd.eqToHom_app]
--   rw [Functor.congr_hom h1]
--   simp only [Functor.comp_obj, Cat.of_α, PGrpd.forgetToPCat_obj,
--     PCat.forgetToCat_obj, Functor.comp_map, id_eq,
--     Cat.comp_obj, PGrpd.forgetToPCat_map, PCat.forgetToCat_map,
--     PGrpd.forgetToGrpd_obj, Grpd.coe_of, eq_mpr_eq_cast,
--     IsMegaPullback.point, eqToHom_trans_assoc, eqToHom_comp_iff, eqToHom_refl,
--     Category.id_comp, comp_eqToHom_iff,
--     Category.assoc, eqToHom_trans, Category.comp_id]
--   rfl

theorem fac_left' : (lift fst snd w ⋙ toPGrpd A) ⋙ PGrpd.forgetToPCat
    = fst ⋙ PGrpd.forgetToPCat := by
  rw [toPGrpd_eq_lift, Functor.assoc,
    PGrpd.IsMegaPullback.fac_left,
    ← PGrpd.IsMegaPullback.fac_left
      (fst ⋙ PGrpd.forgetToPCat) (snd ⋙ A) (by rw [← w]; rfl)]
  rfl

@[simp] theorem fac_left : lift fst snd w ⋙ Groupoidal.toPGrpd _ = fst :=
   calc lift fst snd w ⋙ Groupoidal.toPGrpd _
    _ = PGrpd.IsMegaPullback.lift
      (fst ⋙ PGrpd.forgetToPCat)
      (snd ⋙ A)
      (by rw [Functor.assoc, PGrpd.IsMegaPullback.comm_sq, ← w]; rfl) :=
    PGrpd.IsMegaPullback.lift_uniq
      (fst ⋙ PGrpd.forgetToPCat)
      (snd ⋙ A) _ _
      (fac_left' _ _ _)
      (by rw [Functor.assoc, comm_sq]; rfl)
    _ = fst :=
    symm $ PGrpd.IsMegaPullback.lift_uniq _ _ _ _ rfl w

@[simp] theorem fac_right :
    lift fst snd w ⋙ Groupoidal.forget
    = snd :=
  Grothendieck.IsMegaPullback.fac_right
    (fst ⋙ PGrpd.forgetToPCat) snd (by
    rw [Functor.assoc, PGrpd.IsMegaPullback.comm_sq,
      ← Functor.assoc, w, Functor.assoc])

theorem lift_uniq (m : C ⥤ Groupoidal A)
    (hl : m ⋙ toPGrpd _ = fst)
    (hr : m ⋙ Groupoidal.forget = snd) :
    m = lift _ _ w := by
  apply Grothendieck.IsMegaPullback.lift_uniq
  · rw [← toPGrpd_comp_forgetToPCat, ← hl, Functor.assoc]
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
      (Cat.homOf (var' A)
        ≫ (Cat.ULift_iso_self ≪≫ PGrpd.isoGrothendieckForgetToCat.{u,u}.symm).hom)
      (IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (uLiftA A ≫ Cat.ULift_iso_self.hom) :=
  IsPullback.paste_horiz
    (isPullback_uLiftGrothendieckForget_Groupoid.compForgetToCat_uLiftGrothendieckForget_grpdForgetToCat.{u} A)
    (PGrpd.IsPullback.isPullback_uLiftGrothendieckForget_forgetToGrpd.{u})

open ULift

variable {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

theorem toPGrpd_comp_forgetToPCat_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToPCat :
    downFunctor ⋙ toPGrpd A ⋙ PGrpd.forgetToPCat
      = var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv ⋙ PGrpd.forgetToPCat := by
  have h : var' A ⋙ (IsPullback.uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = IsPullback.uLiftToPCat (A ⋙ Grpd.forgetToCat) := var'_uLiftToPCat A
  dsimp only [IsPullback.uLiftToPCat] at h
  simp only [Cat.ofULift, Cat.of_α, ← Functor.assoc,
    ← toPGrpd_comp_forgetToPCat, comp_upFunctor_inj] at h
  simp only [Functor.assoc] at h
  rw [← h]
  rfl

theorem toPGrpd_comp_forgetToGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToGrpd :
    downFunctor ⋙ toPGrpd A ⋙ PGrpd.forgetToGrpd
      = var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv ⋙ PGrpd.forgetToGrpd := by
  have h : (downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv.{u,u})
      ⋙ PGrpd.forgetToGrpd.{u,u} =
      IsPullback.uLiftGrothendieckForget Grpd.forgetToCat.{u,u} ⋙ downFunctor :=
    PGrpd.IsPullback.isPullback_forgetToGrpd_uLiftGrothendieckForget_commSq.horiz_inv.{u,u}.w
  simp only [← toPGrpd_comp_forgetToPCat, Functor.assoc] at h
  have h1 : var' A ⋙ IsPullback.uLiftGrothendieckForget Grpd.forgetToCat.{u}
      = IsPullback.uLiftGrothendieckForget (A ⋙ Grpd.forgetToCat) ⋙ uLiftA A :=
    var'_forget A
  simp only [Cat.of_α, IsPullback.uLiftGrothendieckForget, ← Functor.assoc,
    uLiftA] at h1
  rw [comp_upFunctor_inj] at h1
  simp only [h, ← Functor.assoc, h1]
  rfl

theorem toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv' :
    Cat.homOf (downFunctor ⋙ toPGrpd A)
      = Cat.homOf (var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv)
      :=
  PGrpd.isPullback_forgetToGrpd_forgetToCat.{u}.hom_ext
    (toPGrpd_comp_forgetToPCat_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToPCat _)
    (toPGrpd_comp_forgetToGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToGrpd _)

theorem toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv :
    downFunctor ⋙ toPGrpd A
      = var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv :=
  toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv' _

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
  apply toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv

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

@[simp] lemma sec_obj_base (x) : ((sec A α h).obj x).base = x := by
  rfl

@[simp] lemma sec_obj_fiber (x) :
    ((sec A α h).obj x).fiber = PGrpd.objPt' h x := by
  simp [Grothendieck.Groupoidal.sec, PGrpd.objPt',
    Grothendieck.Groupoidal.IsMegaPullback.lift_obj_fiber]

@[simp] lemma sec_map_base {x y} {f : x ⟶ y} :
    ((sec A α h).map f).base = f := by
  simp [sec, IsMegaPullback.lift, Grothendieck.IsMegaPullback.lift]

-- TODO likely will also need the non-trivially forded case, in which case rename this
-- to `sec_map_fiber_rfl`
@[simp] lemma sec_map_fiber {x y} {f : x ⟶ y} :
    ((sec (α ⋙ PGrpd.forgetToGrpd) α rfl).map f).fiber = (α.map f).point := by
  simp [sec, Grothendieck.Groupoidal.IsMegaPullback.lift,
    Grothendieck.IsMegaPullback.lift, Grothendieck.IsMegaPullback.point,
    Grothendieck.IsMegaPullback.lift_map_fiber]

end



end Groupoidal
end Grothendieck
end CategoryTheory
