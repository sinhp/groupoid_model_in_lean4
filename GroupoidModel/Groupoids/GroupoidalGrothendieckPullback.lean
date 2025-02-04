import GroupoidModel.Groupoids.GrothendieckPullback

universe v u v₁ u₁ v₂ u₂

/-
  First we show that the category of pointed groupoids
  `PGrpd` can be constructed by making the
  Grothendieck construction on the inclusion `Grpd ⥤ Cat`
-/



namespace CategoryTheory
namespace PGrpd

-- set_option pp.universes true

def isoGrothendieckToCatHom : Grothendieck Grpd.forgetToCat.{v,u} ⥤ PGrpd.{v,u} where
  obj x := ⟨ x.base , PointedGroupoid.of x.base x.fiber ⟩
  map f := ⟨ f.base , f.fiber ⟩

def isoGrothendieckToCatInv : PGrpd.{v,u} ⥤ Grothendieck Grpd.forgetToCat.{v,u} where
  obj x := ⟨ Grpd.of x , x.str.pt ⟩
  map f := ⟨ f.toFunctor , f.point ⟩
  map_comp {x y z} f g := by
    apply Grothendieck.ext
    · rfl
    · rfl

-- def isoGrothendieckToCatHom' : Grothendieck Grpd.forgetToCat.{v,u} ⟶ PGrpd.{v,u} :=
--   _ ⋙ isoGrothendieckToCatHom ⋙ _

-- THIS IS NOT IN THE CATEGORY WE WANT 
def isoGrothendieckToCat : Cat.of (Grothendieck Grpd.forgetToCat.{v,u}) ≅ Cat.of PGrpd.{v,u} where
  hom := isoGrothendieckToCatHom.{v,u}
  inv := isoGrothendieckToCatInv.{v,u}

namespace Pullback
/-
In this section we prove that the following square is a pullback

      PGrpd ------ toPCat ------> PCat
        |                           |
        |                           |
    PGrpd.forgetPoint        PCat.forgetPoint
        |                           |
        v                           v
      Grpd------forgetToCat------->Cat
-/

/-
This particular choice of hom universe level avoids using ULiftHom.
In our applications either `u = v` for a small `Γ`
so that `A : Γ ⥤ Cat.{u,u}`,
or `Γ = Grpd.{v,v}` and `A : Grpd.{v,v} ⥤ Cat.{v,v}` is the inclusion
so that `u = v + 1`.
-/

def Cat.homOf {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := F

abbrev pGrpdForgetToPCat : Cat.of PGrpd.{v,u} ⟶ Cat.of PCat.{v,u} :=
  PGrpd.forgetToPCat

abbrev pGrpdForgetToGrpd : Cat.of PGrpd.{v,u} ⟶ Cat.of Grpd.{v,u} :=
  PGrpd.forgetToGrpd

set_option pp.universes true

#check Cat.of PGrpd.{v,u}

theorem is_pullback :
    @IsPullback Cat.{max v u, max v u + 1} _ _ _ _ _
      (Cat.homOf PGrpd.forgetToPCat.{v,u})
      (Cat.homOf PGrpd.forgetToGrpd.{v,u})
      (Cat.homOf PCat.forgetToCat.{v,u})
      (Cat.homOf Grpd.forgetToCat.{v,u})
       :=
    sorry

end Pullback
end PGrpd
end CategoryTheory
