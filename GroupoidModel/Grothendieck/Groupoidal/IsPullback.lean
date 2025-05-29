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
def toPGrpd : ∫(A) ⥤ PGrpd.{v₁,u₁} :=
  PGrpd.isPullback.lift (Grothendieck.toPCat (A ⋙ Grpd.forgetToCat)) (forget ⋙ A) (by
    rw [toPCat_forgetToCat]
    rfl)

theorem toPGrpd_forgetToGrpd : toPGrpd A ⋙ PGrpd.forgetToGrpd = forget ⋙ A :=
  PGrpd.isPullback.fac_right (Grothendieck.toPCat (A ⋙ Grpd.forgetToCat)) (forget ⋙ A) (by
    rw [toPCat_forgetToCat]
    rfl)

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
def isPullback : Functor.IsPullback (toPGrpd A) forget PGrpd.forgetToGrpd A :=
  Functor.IsPullback.Paste.ofRight'
    (Grothendieck.toPCat_forgetToCat _)
    (Grothendieck.isPullback _)
    PGrpd.forgetToPCat_forgetToCat
    PGrpd.isPullback

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
  (isPullback A).lift α (𝟭 _) (by simp [h, Functor.id_comp])

@[simp] def sec_toPGrpd : sec A α h ⋙ toPGrpd _ = α := by
  simp [sec, (isPullback A).fac_left]

@[simp] def sec_forget : sec A α h ⋙ forget = 𝟭 _ :=
  (isPullback A).fac_right _ _ _

section naturality
variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

@[simp]
theorem pre_toPGrpd (A : Γ ⥤ Grpd) : pre A σ ⋙ toPGrpd _ = toPGrpd _ := by
  rfl

theorem sec_naturality : σ ⋙ sec A α h = sec (σ ⋙ A) (σ ⋙ α) (by rw [← h]; rfl) ⋙ pre A σ := by
  apply (isPullback A).hom_ext
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
