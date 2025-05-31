import GroupoidModel.Pointed.IsPullback
import GroupoidModel.Grothendieck.Groupoidal.Basic

import SEq.Tactic.DepRewrite

/-!
# The Grothendieck construction as a pullback of categories

The following square is a (meta-theoretic) pullback

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
  PGrpd.isPullback.fac_right _ _ _

theorem toPGrpd_forgetToPCat : toPGrpd A ⋙ PGrpd.forgetToPCat = (Grothendieck.toPCat _) :=
  PGrpd.isPullback.fac_left _ _ _

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

/--
We also provide an elementary definition of `toPGrpd` which we can
use for computation.
We avoid using this version and doing direct computations if possible.
-/
def toPGrpd' : ∫(A) ⥤ PGrpd.{v₁,u₁} :=
  PGrpd.functorTo (forget ⋙ A) (fun x => x.fiber) (fun f => f.fiber)
    (by simp) (by simp [Grpd.forgetToCat, forget])

@[simp] theorem toPGrpd'_obj_base (x) :
    ((toPGrpd A).obj x).base = A.obj x.base := by
  rfl

@[simp] theorem toPGrpd'_obj_fiber (x) :
    ((toPGrpd' A).obj x).fiber = x.fiber := by
  rfl

@[simp] theorem toPGrpd'_map_base {x y} (f : x ⟶ y) :
    ((toPGrpd' A).map f).base = A.map f.base := by
  rfl

@[simp] theorem toPGrpd'_map_fiber {x y} (f : x ⟶ y) :
    ((toPGrpd' A).map f).fiber = f.fiber := by
  rfl

theorem toPGrpd_eq_toPGrpd' : toPGrpd A = toPGrpd' A := by
  symm
  apply PGrpd.isPullback.lift_uniq
  · rfl
  · rfl

theorem toPGrpd_obj_base (x) : ((toPGrpd A).obj x).base = A.obj x.base :=
  rfl

theorem toPGrpd_obj_fiber (x) : HEq ((toPGrpd A).obj x).fiber x.fiber := by
  rw [toPGrpd_eq_toPGrpd']
  rfl

theorem toPGrpd_map_base {x y} (f : x ⟶ y) :
    ((toPGrpd A).map f).base = A.map f.base := by
  rfl

theorem toPGrpd_map_fiber {x y} (f : x ⟶ y) :
    HEq ((toPGrpd A).map f).fiber f.fiber := by
  rw [toPGrpd_eq_toPGrpd']
  rfl
end

section

variable {Γ : Type u} [Category.{v} Γ]
variable (A : Γ ⥤ Grpd.{v₁,u₁}) (α : Γ ⥤ PGrpd.{v₁,u₁}) (h : α ⋙ PGrpd.forgetToGrpd = A)

/-- `sec` is the universal lift in the following diagram,
  which is a section of `Groupoidal.forget`
             α
  ===== Γ -------α--------------¬
 ‖      ↓ sec                   V
 ‖     ∫(A) ----------------> PGrpd
 ‖      |                        |
 ‖      |                        |
 ‖   forget                  forgetToGrpd
 ‖      |                        |
 ‖      V                        V
  ===== Γ --α ≫ forgetToGrpd--> Grpd
-/
def sec : Γ ⥤ ∫(A) :=
  Groupoidal.functorTo (𝟭 _) (fun x => PGrpd.objFiber' h x) (fun f => PGrpd.mapFiber' h f)
  (fun x => by simp) (fun f g => by subst h; simp [PGrpd.mapFiber'])

@[simp] lemma sec_obj_base (x) : ((sec A α h).obj x).base = x :=
  rfl

@[simp] lemma sec_obj_fiber (x) :
    ((sec A α h).obj x).fiber = PGrpd.objFiber' h x :=
  rfl

@[simp] lemma sec_map_base {x y} {f : x ⟶ y} : ((sec A α h).map f).base = f :=
  rfl

@[simp] lemma sec_map_fiber {x y} {f : x ⟶ y} :
    ((sec A α h).map f).fiber = PGrpd.mapFiber' h f :=
  rfl

@[simp] def sec_toPGrpd : sec A α h ⋙ toPGrpd _ = α := by
  apply Grothendieck.Functor.hext
  · rw [Functor.assoc, toPGrpd_forgetToGrpd, sec, ← Functor.assoc, h]
    rfl
  · intro x
    apply (toPGrpd_obj_fiber _ _).trans
    simp
  · intro x y f
    apply (toPGrpd_map_fiber _ _).trans
    exact PGrpd.mapFiber'_heq _ _

@[simp] def sec_forget : sec A α h ⋙ forget = 𝟭 _ :=
  rfl

theorem sec_eq_lift : sec A α h = (isPullback A).lift α (𝟭 _) (by simp [h, Functor.id_comp]) := by
  apply (Grothendieck.Groupoidal.isPullback _).lift_uniq
  · simp
  · simp

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

end

section ι

variable {C : Type u} [Category.{v} C] (F : C ⥤ Grpd.{v₁,u₁})

theorem ι_eq_lift (c : C) : ι F c =
    (Grothendieck.Groupoidal.isPullback F).lift
    (ι F c ⋙ toPGrpd F)
    (ι F c ⋙ forget) rfl := by
  apply (Grothendieck.Groupoidal.isPullback F).lift_uniq
  · simp
  · simp

end ι


end Groupoidal
end Grothendieck
end CategoryTheory
