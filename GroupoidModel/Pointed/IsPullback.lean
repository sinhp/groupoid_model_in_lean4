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

lemma forgetToPCat_forgetToCat :
    PGrpd.forgetToPCat.{v,u} ⋙ PCat.forgetToCat.{v,u} =
    PGrpd.forgetToGrpd.{v,u} ⋙ Grpd.forgetToCat.{v,u} := rfl

/--
The following square is a (meta-theoretic) pullback

      PGrpd ------ toPCat ------> PCat
        |                           |
        |                           |
    PGrpd.forgetToGrpd        PCat.forgetToCat
        |                           |
        v                           v
      Grpd------forgetToCat------->Cat
-/
def isPullback :
    Functor.IsPullback forgetToPCat.{v,u} forgetToGrpd.{v,u} PCat.forgetToCat Grpd.forgetToCat :=
  Functor.Grothendieck.isPullback _

/--
The following square is a pullback in `Cat`

      PGrpd ------ toPCat ------> PCat
        |                           |
        |                           |
 PGrpd.forgetToGrpd          PCat.forgetToCat
        |                           |
        v                           v
      Grpd------forgetToCat------->Cat
-/
theorem isPullback' :
    IsPullback
      (Cat.homOf PGrpd.forgetToPCat.{u,u})
      (Cat.homOf PGrpd.forgetToGrpd.{u,u})
      (Cat.homOf PCat.forgetToCat.{u,u})
      (Cat.homOf Grpd.forgetToCat.{u,u}) := Cat.isPullback isPullback rfl


end PGrpd
end CategoryTheory
