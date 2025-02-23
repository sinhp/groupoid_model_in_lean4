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

universe v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace CategoryTheory
namespace Mega

section
variable {P : Type u₁} [Category.{v₁} P]
  {X : Type u} [Category.{v} X]
  {Y : Type u} [Category.{v} Y]
  {Z : Type u} [Category.{v} Z]
  (fst : P ⥤ X)
  (snd : P ⥤ Y)
  (F : X ⥤ Z)
  (G : Y ⥤ Z)

structure CommSq : Prop where
  /-- The square commutes. -/
  w : fst ⋙ F = snd ⋙ G

end

section

variable {P : Type u} [Category.{v} P]
  {X : Type u} [Category.{v} X]
  {Y : Type u} [Category.{v} Y]
  {Z : Type u} [Category.{v} Z]
  (fst : P ⥤ X)
  (snd : P ⥤ Y)
  (F : X ⥤ Z)
  (G : Y ⥤ Z)

structure Pullback extends
  CommSq fst snd F G where
  lift {Q : Type u₁} [Category.{v₁} Q]
    (q1 : Q ⥤ X) (q2 : Q ⥤ Y) (comm : CommSq q1 q2 F G) : Q ⥤ P
  fac_left {Q : Type u₁} [Category.{v₁} Q]
    (q1 : Q ⥤ X) (q2 : Q ⥤ Y) (comm : CommSq q1 q2 F G) :
    lift q1 q2 comm ⋙ fst = q1
  fac_right {Q : Type u₁} [Category.{v₁} Q]
    (q1 : Q ⥤ X) (q2 : Q ⥤ Y) (comm : CommSq q1 q2 F G) :
    lift q1 q2 comm ⋙ snd = q2
  uniq {Q : Type u₁} [Category.{v₁} Q]
    (q1 : Q ⥤ X) (q2 : Q ⥤ Y) (comm : CommSq q1 q2 F G)
    (m : Q ⥤ P) (fm1 : m ⋙ fst = q1) (fm2 : m ⋙ snd = q2) :
    m = lift q1 q2 comm

open IsPullback Limits

theorem Pullback.isPullback (H : Pullback fst snd F G) :
    IsPullback
      (Cat.homOf fst)
      (Cat.homOf snd)
      (Cat.homOf F)
      (Cat.homOf G) :=
  -- IsPullback.of_isLimit $
    -- PullbackCone.IsLimit.mk
    --   (by simp [H.toCommSq.w, Cat.comp_eq_comp] :
    --     (Cat.homOf fst) ≫ (Cat.homOf F) = (Cat.homOf snd) ≫ (Cat.homOf G))
    --   (λ s => by
    --     -- have := H.lift (s.fst : s.pt ⥤ X) (s.snd : s.pt ⥤ Y) ⟨
        --   by
        --     sorry --have 
          -- ⟩
      --   sorry)
      --   sorry
      -- sorry
      -- sorry
      sorry
end


end Mega
end CategoryTheory
