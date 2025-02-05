import GroupoidModel.Pointed.Pullback
/-!
# GroupoidalGrothendieck as a pullback


  ↑Grothendieck (toCat A) -- toPGrpd --> PGrpd
        |                                 |
        |                                 |
↑ Grothendieck.forget        PGrpd.forgetToGrpd
        |                                 |
        v                                 v
        ↑Γ--------------A---------------> Grpd

## Main statements

* `CategoryTheory.Grothendieck.Groupoidal.isPullback`
  shows that `Grothendieck.forget A` is classified by `PGrpd.forgetToGrpd`
  as the pullback of `A`.
  This uses the proof of the similar fact 
  `CategoryTheory.Grothendieck.isPullback`,
  as well as the proof `CategoryTheory.isPullback_forgetToGrpd_forgetToCat`
  that `PGrpd` is the pullback of `PCat`.

-/
universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory
namespace Grothendieck
namespace Groupoidal
namespace IsPullback

open Grothendieck.IsPullback ULift

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
      (Cat.homOf (ULift.downFunctor ⋙ A)) := by
  have h := isPullback_aux.{u} A
  simp at h
  convert h
  apply toPGrpd_eq_var'_comp_isoGrothendieckForgetToCatInv

end Groupoidal
end Grothendieck
end CategoryTheory
