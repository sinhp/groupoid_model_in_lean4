import GroupoidModel.Grothendieck.IsPullback
/-!
# Pointed groupoids as the pullback of pointed categories

This file shows that `PGrpd.forgetToGrpd` is the pullback
along `Grpd.forgetToCat` of `PCat.forgetToCat`.

## Main statements

* `CategoryTheory.PGrpd.isPullback_forgetToGrpd_forgetToCat` -
  the functor `PGrpd.forgetToGrpd` is the pullback
  along `Grpd.forgetToCat` of `PCat.forgetToCat`.

- TODO Probably the latter half of this file can be shortened
  significantly by providing a direct proof of pullback
  using the `IsMegaPullback` definitions
-/


universe v u v₁ u₁ v₂ u₂

/-
-/
namespace CategoryTheory

namespace PGrpd

@[simps] def isoGrothendieckForgetToCatHom :
    PGrpd.{v,u} ⥤ Grothendieck Grpd.forgetToCat.{v,u} where
  obj x := ⟨ Grpd.of x , x.str.pt ⟩
  map f := ⟨ f.toFunctor , f.point ⟩
  map_comp {x y z} f g := by
    apply Grothendieck.ext
    · rfl
    · rfl

def isoGrothendieckForgetToCatInv :
    Grothendieck Grpd.forgetToCat.{v,u} ⥤ PGrpd.{v,u} where
  obj x := ⟨ x.base , PointedGroupoid.of x.base x.fiber ⟩
  map f := ⟨ f.base , f.fiber ⟩

@[simps] def isoGrothendieckForgetToCat : Cat.of PGrpd.{v,u} ≅
    Cat.of (Grothendieck Grpd.forgetToCat.{v,u}) where
  hom := isoGrothendieckForgetToCatHom.{v,u}
  inv := isoGrothendieckForgetToCatInv.{v,u}

namespace IsMegaPullback

def comm_sq : PGrpd.forgetToPCat.{v,u} ⋙ PCat.forgetToCat.{v,u} =
    PGrpd.forgetToGrpd.{v,u} ⋙ Grpd.forgetToCat.{v,u} := rfl

variable {C : Type u₂} [Category.{v₂} C]
  (fst : C ⥤ PCat.{v₁,u₁})
  (snd : C ⥤ Grpd.{v₁,u₁})
  (w : fst ⋙ PCat.forgetToCat = snd ⋙ Grpd.forgetToCat)

def lift : C ⥤ PGrpd.{v₁,u₁} :=
  Grothendieck.IsMegaPullback.lift fst snd w
  ⋙ isoGrothendieckForgetToCatInv

@[simp] theorem fac_left : lift fst snd w ⋙ PGrpd.forgetToPCat = fst :=
  Grothendieck.IsMegaPullback.fac_left fst snd w

@[simp] theorem fac_right : lift fst snd w ⋙ PGrpd.forgetToGrpd = snd :=
  Grothendieck.IsMegaPullback.fac_right fst snd w

theorem uniq (m : C ⥤ PGrpd.{v₁,u₁})
    (hl : m ⋙ PGrpd.forgetToPCat = fst)
    (hr : m ⋙ PGrpd.forgetToGrpd = snd) :
    m = lift _ _ w := by
  convert_to (m ⋙ isoGrothendieckForgetToCatHom)
    ⋙ isoGrothendieckForgetToCatInv = lift fst snd w
  rw [Grothendieck.IsMegaPullback.uniq
    fst snd w (m ⋙ isoGrothendieckForgetToCatHom) hl hr]
  rfl

end IsMegaPullback

namespace IsPullback

/-
In this section we prove that the following square is a pullback

      PGrpd ------ toPCat ------> PCat
        |                           |
        |                           |
    PGrpd.forgetToGrpd        PCat.forgetToCat
        |                           |
        v                           v
      Grpd------forgetToCat------->Cat
-/
open Grothendieck

def Cat.homOf {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := F

theorem isPullback_forgetToGrpd_uLiftGrothendieckForget_commSq :
    CommSq
      (isoGrothendieckForgetToCat ≪≫ Cat.ULift_iso_self.symm).hom
      (Cat.homOf forgetToGrpd)
      (IsPullback.uLiftGrothendieckForget Grpd.forgetToCat)
      Cat.ULift_iso_self.symm.hom := by
  constructor
  apply Functor.ext
  · intro x y f
    cases f
    simp [Cat.homOf]
  · intro x
    cases x
    simp [Cat.homOf]

/--
Here we show the following pullback square in `Cat.{u,u+1}`,
where `↑` denotes some kind of `ULift` operation into `Cat.{u,u+1}`.
Note that these `ULift`s "do nothing" since the categories are already
at the target universe level.
      PGrpd.{u,u} -----≅--->↑Grothendieck Grpd.forgetToCat.{u,u}
        |                           |
        |                           |
    PGrpd.forgetToGrpd         ↑ Grothendieck.forget
        |                           |
        v                           v
      Grpd.{u,u}------≅---->↑Grpd.{u,u}
-/
theorem isPullback_forgetToGrpd_uLiftGrothendieckForget :
    IsPullback
      ((isoGrothendieckForgetToCat.{u,u} ≪≫ Cat.ULift_iso_self.symm).hom)
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (IsPullback.uLiftGrothendieckForget.{u,u+1} Grpd.forgetToCat.{u,u})
      Cat.ULift_iso_self.{u}.inv :=
  IsPullback.of_horiz_isIso
    isPullback_forgetToGrpd_uLiftGrothendieckForget_commSq.{u}

/-
This is the inverted version of isPullback_forgetToGrpd_uLiftGrothendieckForget
The following square is a pullback

↑Grothendieck Groupoid.forgetToCat ---≅-----> PGrpd
        |                                         |
        |                                         |
↑ Grothendieck.forget                      PGrpd.forgetToGrpd
        |                                         |
        v                                         v
    ↑Grpd--------------------≅---------------> Grpd
-/

theorem isPullback_uLiftGrothendieckForget_forgetToGrpd :
    IsPullback
    ((Cat.ULift_iso_self ≪≫ PGrpd.isoGrothendieckForgetToCat.{u,u}.symm).hom)
    (IsPullback.uLiftGrothendieckForget.{u,u+1} Grpd.forgetToCat.{u,u})
    (Cat.homOf PGrpd.forgetToGrpd.{u,u})
    (Cat.ULift_iso_self.hom) :=
  IsPullback.of_horiz_isIso (CommSq.horiz_inv
      PGrpd.IsPullback.isPullback_forgetToGrpd_uLiftGrothendieckForget_commSq.{u,u})

/-
Using the result from `GrothendieckPullback` we obtain
the following pullback square in `Cat.{u,u+1}`,
where `↑` denotes some kind of `ULift` operation into `Cat.{u,u+1}`.
Note that these `ULift`s "do nothing" since the categories are already
at the target universe level.

↑Grothendieck Grpd.forgetToCat.{u,u} --Grothendieck.toPCat----> ↑PCat
        |                                                           |
        |                                                           |
↑Grothendieck.forget                                    ↑PCat.forgetToCat
        |                                                           |
        v                                                           v
    ↑Grpd.{u,u} -------------↑forgetToCat------------------>↑Cat.{u,u}
-/
theorem isPullback_grothendieckForget_forgetToCat :
    IsPullback
      (IsPullback.uLiftToPCat.{u,u+1} Grpd.forgetToCat.{u,u})
      (IsPullback.uLiftGrothendieckForget.{u,u+1} Grpd.forgetToCat.{u,u})
      (IsPullback.uLiftPCatForgetToCat.{u,u+1})
      (IsPullback.uLiftA.{u,u+1} Grpd.forgetToCat.{u,u}) :=
  CategoryTheory.Grothendieck.isPullback _

/--
Here we (roughly) show the following pullback square in `Cat.{u,u+1}`,
where `↑` denotes some kind of `ULift` operation into `Cat.{u,u+1}`
      ↑PCat ---------≅------->  PCat
        |                          |
        |                          |
    ↑PCat.forgetToCat         PCat.forgetToCat
        |                          |
        v                          v
      ↑Cat-----------≅---------->Cat
-/
theorem isPullback_uLiftPCatForgetToCat_forgetToCat :
    IsPullback
      Cat.ULift_iso_self.{u}.hom
      (IsPullback.uLiftPCatForgetToCat.{u,u})
      (Cat.homOf PCat.forgetToCat.{u,u})
      Cat.ULift_iso_self.{u}.hom := by
  apply IsPullback.of_horiz_isIso
  constructor
  apply Functor.ext
  · intro x y f
    cases f
    simp [Cat.homOf]
  · intro x
    cases x
    simp [Cat.homOf]

-- theorem isPullback_forgetToGrpd_forgetToCat_aux : IsPullback
--     (((isoGrothendieckForgetToCat.{u,u} ≪≫ Cat.ULift_iso_self.symm).hom)
--       ≫ (IsPullback.uLiftToPCat.{u,u+1} Grpd.forgetToCat.{u,u})
--       ≫ Cat.ULift_iso_self.{u}.hom)
--     (Cat.homOf PGrpd.forgetToGrpd.{u,u})
--     (Cat.homOf PCat.forgetToCat.{u,u})
--     (Cat.ULift_iso_self.{u}.inv
--     ≫ IsPullback.uLiftA.{u,u+1} Grpd.forgetToCat.{u,u}
--     ≫ Cat.ULift_iso_self.{u}.hom) :=
--   IsPullback.paste_horiz isPullback_forgetToGrpd_uLiftGrothendieckForget
--   (IsPullback.paste_horiz isPullback_grothendieckForget_forgetToCat
--   isPullback_uLiftPCatForgetToCat_forgetToCat)

end IsPullback

open IsPullback

/--
The following square is a pullback

      PGrpd ------ toPCat ------> PCat
        |                           |
        |                           |
 PGrpd.forgetToGrpd          PCat.forgetToCat
        |                           |
        v                           v
      Grpd------forgetToCat------->Cat
-/
theorem isPullback_forgetToGrpd_forgetToCat :
    IsPullback
      (Cat.homOf PGrpd.forgetToPCat.{u,u})
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (Cat.homOf PCat.forgetToCat.{u,u})
      (Cat.homOf Grpd.forgetToCat.{u,u}) :=
  IsPullback.paste_horiz
    isPullback_forgetToGrpd_uLiftGrothendieckForget
    (IsPullback.paste_horiz
      isPullback_grothendieckForget_forgetToCat
      isPullback_uLiftPCatForgetToCat_forgetToCat)


end PGrpd
end CategoryTheory
