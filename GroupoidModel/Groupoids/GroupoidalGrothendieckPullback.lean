import GroupoidModel.Groupoids.GrothendieckPullback

universe v u v₁ u₁ v₂ u₂

/-
  First we show that the category of pointed groupoids
  `PGrpd` can be constructed by making the
  Grothendieck construction on the inclusion `Grpd ⥤ Cat`
-/



namespace CategoryTheory
namespace PGrpd

set_option pp.universes true

def isoGrothendieckToCatHom : Grothendieck Grpd.forgetToCat.{v,u} ⥤ PGrpd.{v,u} where
  obj x := sorry
  map := sorry

-- def isoGrothendieckToCatHom' : Grothendieck Grpd.forgetToCat.{v,u} ⟶ PGrpd.{v,u} :=
--   _ ⋙ isoGrothendieckToCatHom ⋙ _

-- THIS IS NOT IN THE CATEGORY WE WANT 
def isoGrothendieckToCat : Cat.of (Grothendieck Grpd.forgetToCat.{v,u}) ≅ Cat.of PGrpd.{v,u} where
  hom := isoGrothendieckToCatHom.{v,u}
  inv := sorry

end PGrpd
end CategoryTheory
