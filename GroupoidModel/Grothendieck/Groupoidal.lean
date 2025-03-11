import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Category.Grpd
import GroupoidModel.Pointed.IsPullback

/-!
# The Groupidal Grothendieck construction

  ↑Grothendieck (toCat A) -- toPGrpd --> PGrpd
        |                                 |
        |                                 |
↑ Grothendieck.forget        PGrpd.forgetToGrpd
        |                                 |
        v                                 v
        ↑Γ--------------A---------------> Grpd

## Main definitions
* `CategoryTheory.Grothendieck.Groupoidal`
  takes a functor from a groupoid into `Grpd` the category of groupoids,
  composes it with the forgetful functor into `Cat` the category of categories,
  then applies `CategoryTheory.Grothendieck`.
  This is a groupoid.

## Main statements

* `CategoryTheory.Grothendieck.Groupoidal.groupoid`
  is an instance of a groupoid structure on the groupidal
  Grothendieck construction.
* `CategoryTheory.Grothendieck.Groupoidal.isPullback`
  shows that `Grothendieck.forget A` is classified by `PGrpd.forgetToGrpd`
  as the pullback of `A`.
  This uses the proof of the similar fact
  `CategoryTheory.Grothendieck.isPullback`,
  as well as the proof `CategoryTheory.isPullback_forgetToGrpd_forgetToCat`
  that `PGrpd` is the pullback of `PCat`.

- TODO Probably the proof of `Groupoidal.IsPullback` can be shortened
  significantly by providing a direct proof of pullback
  using the `IsMegaPullback` defintions
-/

universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {Γ : Type u} [Category.{v} Γ]
  (A : Γ ⥤ Grpd.{v₁,u₁})

abbrev Groupoid.compForgetToCat : Γ ⥤ Cat.{v₁,u₁} := A ⋙ Grpd.forgetToCat

namespace Grothendieck

/--
  In Mathlib.CategoryTheory.Grothendieck we find the Grothendieck construction
  for the functors `F : C ⥤ Cat`. Given a functor `F : G ⥤ Grpd`, we show that
  the Grothendieck construction of the composite `F ⋙ Grpd.forgetToCat`, where
  `forgetToCat : Grpd ⥤ Cat` is the embedding of groupoids into categories, is a groupoid.
-/
abbrev Groupoidal {C : Type u₁} [Category.{v₁,u₁} C] (F : C ⥤ Grpd.{v₂,u₂}) :=
  Grothendieck (Groupoid.compForgetToCat F)

namespace Groupoidal

section

instance {C : Type u₁} [Category.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}} :
    Category (Groupoidal F) :=
  inferInstanceAs (Category (Grothendieck _))

variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

instance
    (X : C) : Groupoid (Groupoid.compForgetToCat F |>.obj X) where
  inv f := ((F.obj X).str').inv f

def isoMk {X Y : Grothendieck.Groupoidal F} (f : X ⟶ Y) : X ≅ Y := by
  fapply Grothendieck.mkIso
  · exact (Groupoid.isoEquivHom _ _).2 f.base
  · apply (Groupoid.isoEquivHom _ _).2 f.fiber

def inv {X Y : Grothendieck.Groupoidal F} (f : X ⟶ Y) : Y ⟶ X  :=
  isoMk f |>.inv

instance groupoid : Groupoid (Grothendieck.Groupoidal F) where
  inv f :=  inv f
  inv_comp f := (isoMk f).inv_hom_id
  comp_inv f := (isoMk f).hom_inv_id

end

section FunctorFrom

variable {C : Type u} [Groupoid.{v} C]
    (F : C ⥤ Grpd.{v₁,u₁})

/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its
groupoidal Grothendieck construction.-/
def ι (c : C) : F.obj c ⥤ Groupoidal F :=
  Grothendieck.ι (F ⋙ Grpd.forgetToCat) c

end FunctorFrom

section
variable {C : Type u} [Groupoid.{v} C]
    {F G : C ⥤ Grpd.{v₂,u₂}}
/-- The groupoidal Grothendieck construction is functorial:
a natural transformation `α : F ⟶ G` induces
a functor `Groupoidal.map : Groupoidal F ⥤ Groupoidal G`.
-/
@[simp] def map (α : F ⟶ G) : Groupoidal F ⥤ Groupoidal G :=
  Grothendieck.map (whiskerRight α _)

theorem map_obj {α : F ⟶ G} (X : Groupoidal F) :
    (Groupoidal.map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl

end

/-- Applying a functor `G : D ⥤ C` to the base of the groupoidal Grothendieck
  construction induces a functor
  `Groupoidal (G ⋙ F) ⥤ Groupoidal F`. -/
def pre {C : Type u} [Groupoid.{v} C] {D : Type u₁} [Groupoid.{v₁} D]
    (F : D ⥤ Grpd.{v₂,u₂}) (G : C ⥤ D) :
    Groupoidal (G ⋙ F) ⥤ Groupoidal F :=
  Grothendieck.pre (F ⋙ Grpd.forgetToCat) G

-- TODO this should be replaced with Groupoidal.pre
def functorial {C D : Grpd.{v₁,u₁}} (F : C ⟶ D) (G : D ⥤ Grpd.{v₂,u₂}) :
  Grothendieck (Groupoid.compForgetToCat (F ⋙ G))
  ⥤ Grothendieck (Groupoid.compForgetToCat G) where
  obj X := ⟨F.obj X.base, X.fiber⟩
  map {X Y} f := ⟨F.map f.base, f.fiber⟩
  map_id X := by
    fapply Grothendieck.ext
    · exact F.map_id X.base
    · simp only [Grothendieck.id_fiber, eqToHom_trans]
  map_comp {X Y Z} f g := by
    simp only [Grothendieck.comp]
    fapply Grothendieck.ext
    · exact F.map_comp f.base g.base
    · erw [Grothendieck.comp_fiber (F:= Groupoid.compForgetToCat (F ⋙ G)) f g]
      simp [eqToHom_trans]

-- TODO docstring
def Map (Δ Γ: Grpd) (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd) (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : Grothendieck.Groupoidal (σ ⋙ A) ⥤ Grpd where
  obj x := by
    rcases x with ⟨x, a⟩
    dsimp at a
    let X : Grothendieck.Groupoidal A := by
      fconstructor
      . exact σ.obj x
      . exact a
    exact B.obj X
  map f := by
    rename_i X Y
    rcases X with ⟨x, xa⟩
    rcases Y with ⟨y, ya⟩
    let X : Grothendieck.Groupoidal A := by
      fconstructor
      . exact σ.obj x
      . exact xa
    let Y : Grothendieck.Groupoidal A := by
      fconstructor
      . exact σ.obj y
      . exact ya
    let F : X ⟶ Y := by
      fconstructor
      . exact σ.map f.base
      . exact f.fiber
    exact B.map F
  map_comp := by
    sorry
  map_id x := by
    sorry

instance toPCatObjGroupoid
    (x : Grothendieck (Groupoid.compForgetToCat.{v,u,v₁,u₁} A)) :
    Groupoid x.toPCatObj := by
  dsimp [Grpd.forgetToCat]
  infer_instance

instance toPCatObjPointed (x : Grothendieck (Groupoid.compForgetToCat A)) :
    PointedGroupoid x.toPCatObj :=
  PointedGroupoid.of x.toPCatObj PointedCategory.pt

def toPGrpd : Grothendieck (Groupoid.compForgetToCat A) ⥤ PGrpd.{v₁,u₁} where
  obj x := PGrpd.of x.toPCatObj
  map := Grothendieck.toPCatMap
  map_id := (Grothendieck.toPCat (Groupoid.compForgetToCat A)).map_id
  map_comp := (Grothendieck.toPCat (Groupoid.compForgetToCat A)).map_comp

theorem toPGrpd_comp_forgetToPCat :
    toPGrpd A ⋙ PGrpd.forgetToPCat = toPCat (Groupoid.compForgetToCat A) :=
  rfl

namespace IsMegaPullback

theorem comm_sq : Groupoidal.toPGrpd A ⋙ PGrpd.forgetToGrpd
    = Grothendieck.forget _ ⋙ A := rfl

variable {A} {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PGrpd.{v₁, u₁})
  (snd : C ⥤ Γ)
  (w : fst ⋙ PGrpd.forgetToGrpd = snd ⋙ A)

theorem toPGrpd_eq_lift :
    toPGrpd A =
    PGrpd.IsMegaPullback.lift
      (toPCat (Groupoid.compForgetToCat A))
      (Grothendieck.forget _ ⋙ A) rfl :=
  PGrpd.IsMegaPullback.lift_uniq
    (toPCat (Groupoid.compForgetToCat A))
    (Grothendieck.forget _ ⋙ A)
    rfl _ rfl rfl

def lift : C ⥤ Groupoidal A :=
  Grothendieck.IsMegaPullback.lift
    (fst ⋙ PGrpd.forgetToPCat) snd (by
      simp only [Groupoid.compForgetToCat, ← Functor.assoc, ← w]
      rfl)

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
    lift fst snd w ⋙ Grothendieck.forget _
    = snd :=
  Grothendieck.IsMegaPullback.fac_right
    (fst ⋙ PGrpd.forgetToPCat) snd (by
    rw [Functor.assoc, PGrpd.IsMegaPullback.comm_sq,
      ← Functor.assoc, w, Functor.assoc])

theorem lift_uniq (m : C ⥤ Groupoidal A)
    (hl : m ⋙ toPGrpd _ = fst)
    (hr : m ⋙ Grothendieck.forget _ = snd) :
    m = lift _ _ w := by
  apply Grothendieck.IsMegaPullback.lift_uniq
  · rw [← toPGrpd_comp_forgetToPCat, ← hl, Functor.assoc]
  · exact hr

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
`var' : Grothendieck(Groupoid.compForgetToCat A) ⟶ Grothendieck(Grpd.forgetToCat)`
given by pullback pasting in the following pasting diagram.

  ↑Grothendieck (Groupoid.compForgetToCat A) .-.-.-.-> ↑GrothendieckForgetToCat -----> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
noncomputable def var' :
    IsPullback.uLiftGrothendieck (Groupoid.compForgetToCat.{u} A)
    ⟶ IsPullback.uLiftGrothendieck Grpd.forgetToCat.{u,u} :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift
    (IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A))
    ((IsPullback.uLiftGrothendieckForget
      (Groupoid.compForgetToCat.{u} A)) ≫ uLiftA A)
      (Grothendieck.isPullback
        (Groupoid.compForgetToCat.{u} A)).cone.condition_one

theorem var'_uLiftToPCat :
    var' A ≫ (uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = uLiftToPCat (Groupoid.compForgetToCat.{u} A) :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_fst
    (IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A))
    ((IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A)) ≫ uLiftA A)
    (Grothendieck.isPullback (Groupoid.compForgetToCat.{u} A)).cone.condition_one

theorem var'_forget :
    var' A ≫ (uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    = uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A) ≫ uLiftA A := 
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_snd
    (IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A)) ((IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A)) ≫ uLiftA A)
    (Grothendieck.isPullback (Groupoid.compForgetToCat.{u} A)).cone.condition_one


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
    (IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A))
    (IsPullback.uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    (uLiftA A) :=
  IsPullback.of_right'
    (Grothendieck.isPullback (Groupoid.compForgetToCat.{u} A))
    (Grothendieck.isPullback (Grpd.forgetToCat.{u,u}))

theorem isPullback_aux:
    IsPullback
      (Cat.homOf (var' A)
        ≫ (Cat.ULift_iso_self ≪≫ PGrpd.isoGrothendieckForgetToCat.{u,u}.symm).hom)
      (IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A))
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
    = IsPullback.uLiftToPCat (Groupoid.compForgetToCat.{u} A) := var'_uLiftToPCat A
  dsimp [IsPullback.uLiftToPCat] at h
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
      = IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat A) ⋙ uLiftA A :=
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

↑Grothendieck (Groupoid.compForgetToCat A) -- toPGrpd --> PGrpd
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
      (IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat.{u} A))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (Cat.homOf (ULift.downFunctor.{u,u} ⋙ A)) := by
  have h := isPullback_aux.{u} A
  simp at h
  convert h
  apply toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv

end Groupoidal
end Grothendieck
end CategoryTheory
