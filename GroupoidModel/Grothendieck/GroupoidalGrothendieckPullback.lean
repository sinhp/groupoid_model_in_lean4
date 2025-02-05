import GroupoidModel.Pointed.Pullback
/-!
# GroupoidalGrothendieck as a pullback

TODO

This file 

## Main statements

TODO

-/
universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory
namespace Grothendieck
namespace Groupoidal
namespace IsPullback

open Grothendieck.IsPullback ULift

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u,u})

abbrev toCat : Γ ⥤ Cat.{u,u} := A ⋙ Grpd.forgetToCat.{u,u}

def toPGrpd : Grothendieck (toCat.{u} A) ⥤ PGrpd.{v₁,u₁} where
  obj x := sorry -- PGrpd.of ((Grothendieck.toPCat (toCat.{u} A)).obj x)
  map f := sorry
  map_id x :=  sorry
  map_comp {x y z} f g := sorry

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
  
  sorry

end Groupoidal
end Grothendieck
end CategoryTheory
