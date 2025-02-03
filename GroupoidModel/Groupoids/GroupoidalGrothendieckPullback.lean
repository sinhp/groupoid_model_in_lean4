import GroupoidModel.Groupoids.GrothendieckPullback

universe v u v₁ u₁ v₂ u₂

/-
  First we show that the category of pointed groupoids
  `PGrpd` can be constructed by making the
  Grothendieck construction on the inclusion `Grpd ⥤ Cat`
-/



namespace CategoryTheory
namespace PGrpd

def isoGrothendieckToCatHom : Grothendieck Grpd.forgetToCat.{v,u} ⥤ PGrpd.{v,u} :=
  sorry

def isoGrothendieckToCat : Grothendieck Grpd.forgetToCat.{v,u} ≅ PGrpd.{v,u} where
  hom := isoGrothendieckToCatHom.{v,u}
  inv := sorry

end PGrpd
end CategoryTheory
