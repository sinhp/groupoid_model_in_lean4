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

-/

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory

@[simps!] def Grpd.compForgetToCat
    {C : Type u₁} [Category.{v₁,u₁} C] (G : C ⥤ Grpd) :
    C ⥤ Cat :=
  G ⋙ Grpd.forgetToCat

namespace Grothendieck
/--
  In Mathlib.CategoryTheory.Grothendieck we find the Grothendieck construction
  for the functors `F : C ⥤ Cat`. Given a functor `F : G ⥤ Grpd`, we show that
  the Grothendieck construction of the composite `F ⋙ Grpd.forgetToCat`, where
  `forgetToCat : Grpd ⥤ Cat` is the embedding of groupoids into categories, is a groupoid.
-/
abbrev Groupoidal {C : Type u₁} [Groupoid.{v₁,u₁} C] (F : C ⥤ Grpd.{v₂,u₂}) :=
  Grothendieck (Grpd.compForgetToCat F)

namespace Groupoidal

section
variable {C : Type u₁} [Groupoid.{v₁,u₁} C] {F : C ⥤ Grpd.{v₂,u₂}}

instance : Category (Groupoidal F) :=
  inferInstanceAs (Category (Grothendieck _))

instance (X : C) : Groupoid (Grpd.compForgetToCat F |>.obj X) where
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

-- def ToGrpd : Grothendieck.Groupoidal F ⥤ Grpd.{v₂,u₂} :=
--   Grothendieck.forget _ ⋙ F

-- def functorial {C D : Grpd.{v₁,u₁}} (F : C ⟶ D) (G : D ⥤ Grpd.{v₂,u₂}) :
--   Grothendieck (Grpd.compForgetToCat (F ⋙ G))
--   ⥤ Grothendieck (Grpd.compForgetToCat G) where
--   obj X := ⟨F.obj X.base, X.fiber⟩
--   map {X Y} f := ⟨F.map f.base, f.fiber⟩
--   map_id X := by
--     fapply Grothendieck.ext
--     · exact F.map_id X.base
--     · simp only [Grothendieck.id_fiber, eqToHom_trans]
--   map_comp {X Y Z} f g := by
--     simp only [Grothendieck.comp]
--     fapply Grothendieck.ext
--     · exact F.map_comp f.base g.base
--     · erw [Grothendieck.comp_fiber (F:= Grpd.compForgetToCat (F ⋙ G)) f g]
--       simp [eqToHom_trans]

-- def Map (Δ Γ: Grpd) (σ : Δ ⥤ Γ) (A : Γ ⥤ Grpd) (B : (Grothendieck.Groupoidal A) ⥤ Grpd) : Grothendieck.Groupoidal (σ ⋙ A) ⥤ Grpd where
--   obj x := by
--     rcases x with ⟨x, a⟩
--     dsimp at a
--     let X : Grothendieck.Groupoidal A := by
--       fconstructor
--       . exact σ.obj x
--       . exact a
--     exact B.obj X
--   map f := by
--     rename_i X Y
--     rcases X with ⟨x, xa⟩
--     rcases Y with ⟨y, ya⟩
--     let X : Grothendieck.Groupoidal A := by
--       fconstructor
--       . exact σ.obj x
--       . exact xa
--     let Y : Grothendieck.Groupoidal A := by
--       fconstructor
--       . exact σ.obj y
--       . exact ya
--     let F : X ⟶ Y := by
--       fconstructor
--       . exact σ.map f.base
--       . exact f.fiber
--     exact B.map F
--   map_comp := by
--     sorry
--   map_id x := by
--     sorry

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

abbrev toCat : Γ ⥤ Cat.{u,u} := A ⋙ Grpd.forgetToCat.{u,u}

instance toPCatObjGroupoid (x : Grothendieck (toCat.{u} A)) :
    Groupoid x.toPCatObj := by
  dsimp [Grpd.forgetToCat]
  infer_instance

instance toPCatObjPointed (x : Grothendieck (toCat.{u} A)) :
    PointedGroupoid x.toPCatObj :=
  PointedGroupoid.of x.toPCatObj PointedCategory.pt

def toPGrpd : Grothendieck (toCat.{u} A) ⥤ PGrpd.{u,u} where
  obj x := PGrpd.of x.toPCatObj
  map := Grothendieck.toPCatMap
  map_id := (Grothendieck.toPCat (toCat.{u} A)).map_id
  map_comp := (Grothendieck.toPCat (toCat.{u} A)).map_comp

theorem toPGrpd_comp_forgetToPCat :
    toPGrpd A ⋙ PGrpd.forgetToPCat = toPCat (toCat.{u} A) :=
  rfl

end

namespace IsPullback

open Grothendieck.IsPullback ULift

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

abbrev uLiftGrpd : Cat.{u, max u (u+1)} :=
  Cat.of (ULift.{max u (u+1), u + 1} Grpd.{u})

abbrev uLiftA : uLiftΓ.{u,u} Γ ⟶ uLiftGrpd.{u} := downFunctor ⋙ A ⋙ upFunctor

abbrev uLiftPGrpd : Cat.{u, max u (u+1)} :=
  Cat.of (ULift.{max u (u+1), u + 1} PGrpd.{u,u})

abbrev uLiftPGrpdForgetToGrpd : uLiftPGrpd.{u} ⟶ uLiftGrpd.{u} :=
  downFunctor ⋙ PGrpd.forgetToGrpd ⋙ upFunctor

/--
The universal lift
`var' : Grothendieck(toCat A) ⟶ Grothendieck(Grpd.forgetToCat)`
given by pullback pasting in the following pasting diagram.

  ↑Grothendieck (toCat A) .-.-.-.-> ↑GrothendieckForgetToCat -----> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
noncomputable def var' :
    IsPullback.uLiftGrothendieck (toCat.{u} A)
    ⟶ IsPullback.uLiftGrothendieck Grpd.forgetToCat.{u,u} :=
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift
    (IsPullback.uLiftToPCat (toCat.{u} A))
    ((IsPullback.uLiftGrothendieckForget (toCat.{u} A)) ≫ uLiftA A)
    (Grothendieck.isPullback (toCat.{u} A)).cone.condition_one

theorem var'_uLiftToPCat :
    var' A ≫ (uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = uLiftToPCat (toCat.{u} A) := 
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_fst
    (IsPullback.uLiftToPCat (toCat.{u} A))
    ((IsPullback.uLiftGrothendieckForget (toCat.{u} A)) ≫ uLiftA A)
    (Grothendieck.isPullback (toCat.{u} A)).cone.condition_one


theorem var'_forget :
    var' A ≫ (uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    = uLiftGrothendieckForget (toCat.{u} A) ≫ uLiftA A := 
  (Grothendieck.isPullback (Grpd.forgetToCat.{u,u})).lift_snd
    (IsPullback.uLiftToPCat (toCat.{u} A))
    ((IsPullback.uLiftGrothendieckForget (toCat.{u} A)) ≫ uLiftA A)
    (Grothendieck.isPullback (toCat.{u} A)).cone.condition_one


/--
The following square is a pullback
  ↑Grothendieck (toCat A) ------- var' -------> ↑Grothendieck Grpd.forgetToCat
        |                                                    |
        |                                                    |
↑ Grothendieck.forget                           ↑Grothendieck.forget
        |                                                    |
        v                                                    v
        ↑Γ--------------↑A----------------------------> ↑Grpd.{u,u}

by pullback pasting

  ↑Grothendieck (toCat A) --> ↑Grothendieck Grpd.forgetToCat ---> ↑PCat.{u,u}
        |                          |                                  |
        |                          |                                  |
↑ Grothendieck.forget        ↑Grothendieck.forget         ↑PCat.forgetToCat
        |                          |                                  |
        v                          v                                  v
        ↑Γ----------------------> ↑Grpd.{u,u} ----------------> ↑Cat.{u,u}
-/
theorem
  isPullback_uLiftGrothendieckForget_toCat_uLiftGrothendieckForget_grpdForgetToCat : 
    IsPullback
    (Cat.homOf (var' A))
    (IsPullback.uLiftGrothendieckForget (toCat.{u} A))
    (IsPullback.uLiftGrothendieckForget (Grpd.forgetToCat.{u,u}))
    (uLiftA A) :=
  IsPullback.of_right'
    (Grothendieck.isPullback (toCat.{u} A))
    (Grothendieck.isPullback (Grpd.forgetToCat.{u,u}))

theorem isPullback_aux:
    IsPullback
      (Cat.homOf (var' A)
        ≫ (Cat.ULift_iso_self ≪≫ PGrpd.isoGrothendieckForgetToCat.{u,u}.symm).hom)
      (IsPullback.uLiftGrothendieckForget (toCat.{u} A))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (uLiftA A ≫ Cat.ULift_iso_self.hom) := 
  IsPullback.paste_horiz
    (isPullback_uLiftGrothendieckForget_toCat_uLiftGrothendieckForget_grpdForgetToCat.{u} A)
    (PGrpd.IsPullback.isPullback_uLiftGrothendieckForget_forgetToGrpd.{u})

open ULift 

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

theorem toPGrpd_comp_forgetToPCat_eq_var'_comp_isoGrothendieckForgetToCatInv_comp_forgetToPCat :
    downFunctor ⋙ toPGrpd A ⋙ PGrpd.forgetToPCat
      = var' A ⋙ downFunctor ⋙ PGrpd.isoGrothendieckForgetToCatInv ⋙ PGrpd.forgetToPCat := by
  have h : var' A ⋙ (IsPullback.uLiftToPCat (Grpd.forgetToCat.{u,u}))
    = IsPullback.uLiftToPCat (toCat.{u} A) := var'_uLiftToPCat A
  dsimp [IsPullback.uLiftToPCat] at h
  simp only [← toPGrpd_comp_forgetToPCat, ← Functor.assoc, comp_upFunctor_inj] at h
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
      = IsPullback.uLiftGrothendieckForget (toCat A) ⋙ uLiftA A :=
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

  ↑Grothendieck (toCat A) -- toPGrpd --> PGrpd
        |                                 |
        |                                 |
↑ Grothendieck.forget        PGrpd.forgetToGrpd
        |                                 |
        v                                 v
        ↑Γ--------------A---------------> Grpd
in the appropriately sized category `Grpd.{v, max u (v+1)}`;
where `(Γ : Type u) [Grpdegory.{v} Γ] (A : Γ ⥤ Grpd.{v,v})`.
-/
theorem isPullback {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u,u}) : 
    IsPullback
      (Cat.homOf (ULift.downFunctor ⋙ toPGrpd A))
      (IsPullback.uLiftGrothendieckForget (toCat.{u} A))
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (Cat.homOf (ULift.downFunctor.{u,u} ⋙ A)) := by
  have h := isPullback_aux.{u} A
  simp at h
  convert h
  apply toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv

end Groupoidal
end Grothendieck
end CategoryTheory
