import HoTTLean.Pointed.IsPullback
import HoTTLean.Grothendieck.Groupoidal.Basic

/-!
# The Grothendieck construction as a pullback of categories

* `CategoryTheory.Grothendieck.Groupoidal.isPullback`
  shows that `Grothendieck.forget A` is classified by `PGrpd.forgetToGrpd`
  as the (meta-theoretic) pullback of `A`.
  This uses the proof of the similar fact
  `CategoryTheory.Grothendieck.isPullback`,
  as well as the proof `CategoryTheory.isPullback_forgetToGrpd_forgetToCat`
  that `PGrpd` is the pullback of `PCat`

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

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp

namespace Functor

namespace Groupoidal

section

variable {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Grpd.{v₁,u₁})

-- TODO maybe revert this to the direct definition `toPGrpd'`
-- so that the style is consistent with `sec` and `ι`
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
  PGrpd.functorTo (forget ⋙ A) (fun x => x.fiber) (fun f => f.fiber)
    (fun x => by
      change Hom.fiber (𝟙 x) = eqToHom _
      exact id_fiber x)
    (fun f g => by
      change Hom.fiber (f ≫ g) = eqToHom _ ≫ (A.map g.base).map f.fiber ≫ g.fiber
      exact comp_fiber f g)

@[simp] theorem toPGrpd_obj_base (x) :
    ((toPGrpd A).obj x).base = A.obj x.base := rfl

@[simp] theorem toPGrpd_obj_fiber (x) :
    ((toPGrpd A).obj x).fiber = x.fiber := rfl

@[simp] theorem toPGrpd_map_base {x y} (f : x ⟶ y) :
    ((toPGrpd A).map f).base = A.map f.base := rfl

@[simp] theorem toPGrpd_map_fiber {x y} (f : x ⟶ y) :
    ((toPGrpd A).map f).fiber = f.fiber := rfl

theorem toPGrpd_forgetToGrpd : toPGrpd A ⋙ PGrpd.forgetToGrpd = forget ⋙ A :=
  rfl

theorem toPGrpd_forgetToPCat : toPGrpd A ⋙ PGrpd.forgetToPCat = (Grothendieck.toPCat _) :=
  rfl

/--
We also provide a definition of `toPGrpd` as the universal lift
of the pullback `PGrpd`.
-/
def toPGrpd' : ∫(A) ⥤ PGrpd.{v₁,u₁} :=
  PGrpd.isPullback.lift (Grothendieck.toPCat (A ⋙ Grpd.forgetToCat)) (forget ⋙ A) (by
    change Grothendieck.toPCat (A ⋙ Grpd.forgetToCat) ⋙ PCat.forgetToCat =
      Grothendieck.forget (A ⋙ Grpd.forgetToCat) ⋙ (A ⋙ Grpd.forgetToCat)
    exact Grothendieck.toPCat_forgetToCat (A ⋙ Grpd.forgetToCat))

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
def isPullback' : Functor.IsPullback (toPGrpd' A) forget PGrpd.forgetToGrpd A :=
  Functor.IsPullback.Paste.ofRight'
    (Grothendieck.toPCat_forgetToCat _)
    (Grothendieck.isPullback _)
    PGrpd.forgetToPCat_forgetToCat
    PGrpd.isPullback
    _
    rfl

theorem toPGrpd_eq_toPGrpd' : toPGrpd A = toPGrpd' A := by
  apply PGrpd.isPullback.lift_uniq
  · rfl
  · rfl

def isPullback : Functor.IsPullback (toPGrpd A) forget PGrpd.forgetToGrpd A :=
  cast (by rw [toPGrpd_eq_toPGrpd']) (isPullback' A)

/--
The left square is a pullback since the right square and outer square are.
    ∫(σ ⋙ A) ------------ pre ---------> ∫(A)
        |                                  |
        |                                  |
     forget                              forget
        |                                  |
        |                                  |
        v                                  v
        Δ -------------- σ ---------------> Γ
-/
def pre_isPullback {C : Type u} [Groupoid.{v, u} C] {D : Type u₁}
    [Groupoid.{v₁, u₁} D] (F : C ⥤ Grpd) (G : D ⥤ C) :
    Functor.IsPullback (pre F G) (forget (F := G ⋙ F)) (forget (F := F)) G :=
  Functor.IsPullback.Paste.ofRight
  (no := pre F G) (rth := toPGrpd F) (west := forget (F := G ⋙ F)) (sah := forget (F := F))
  (east := PGrpd.forgetToGrpd) (uth := F)
  (by simp [Functor.Groupoidal.pre_comp_forget])
  (by simp [Functor.Groupoidal.toPGrpd_forgetToGrpd])
  (by apply Functor.Groupoidal.isPullback)
  (by apply Functor.Groupoidal.isPullback)

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
  (fun x => by
    change PGrpd.mapFiber' h (𝟙 x) = eqToHom (by simp)
    exact PGrpd.mapFiber'_id (h := h))
  (fun f g => by
    change PGrpd.mapFiber' h (f ≫ g) =
      eqToHom (by simp) ≫ (A.map g).map (PGrpd.mapFiber' h f) ≫ PGrpd.mapFiber' h g
    exact PGrpd.mapFiber'_comp' h f g)

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
  apply Grothendieck.FunctorTo.hext
  · rw [Functor.assoc, toPGrpd_forgetToGrpd, sec, ← Functor.assoc, h]
    rfl
  · intro x
    change HEq (PGrpd.objFiber' h x) (α.obj x).fiber
    exact PGrpd.objFiber'_heq (h := h)
  · intro x y f
    change HEq (PGrpd.mapFiber' h f) (α.map f).fiber
    exact PGrpd.mapFiber'_heq (h := h) f

@[simp] def sec_forget : sec A α h ⋙ forget = 𝟭 _ :=
  rfl

theorem sec_eq_lift : sec A α h = (isPullback A).lift α (𝟭 _) (by simp [h, Functor.id_comp]) := by
  apply (Groupoidal.isPullback _).lift_uniq
  · simp
  · simp

section naturality
variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

@[simp]
theorem pre_toPGrpd (A : Γ ⥤ Grpd) : pre A σ ⋙ toPGrpd _ = toPGrpd _ := rfl

theorem sec_naturality : σ ⋙ sec A α h = sec (σ ⋙ A) (σ ⋙ α) (by rw [← h]; rfl) ⋙ pre A σ := by
  apply (isPullback A).hom_ext
  . simp [Functor.assoc]
  . conv_rhs => rw [Functor.assoc, pre_comp_forget, ← Functor.assoc, sec_forget]
    simp [Functor.assoc, Functor.comp_id, Functor.id_comp]

end naturality

end

section ι

variable {C : Type u} [Category.{v} C] (F : C ⥤ Grpd.{v₁,u₁})

theorem ι_eq_lift (c : C) : ι F c =
    (Groupoidal.isPullback F).lift
    (ι F c ⋙ toPGrpd F)
    (ι F c ⋙ forget) rfl := by
  apply (Groupoidal.isPullback F).lift_uniq
  · simp
  · simp

end ι

section
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  (F : C ⥤ Grpd) {G H : D ⥤ C} (α : G ≅ H)

@[simp]
theorem map_eqToHom_toPGrpd {Γ : Type*} [Category Γ] (A A' : Γ ⥤ Grpd) (h : A = A'):
    map (eqToHom h) ⋙ toPGrpd A' = toPGrpd A := by
  subst h
  simp [map_id_eq, Functor.id_comp]

end

end Groupoidal
end Functor
end CategoryTheory
