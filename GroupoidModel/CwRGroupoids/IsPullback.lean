import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Category.Cat.Limit

import GroupoidModel.Grothendieck.Groupoidal.IsPullback
import GroupoidModel.CwRGroupoids.Basic

/-!
Here we construct universes for the groupoid natural model.

-- TODO: flip all the diagrams in this file
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory ULift Functor.Groupoidal
  Limits GroupoidModel.Ctx GroupoidModel.U PGrpd

namespace GroupoidModel
namespace IsPullback

def liftTy' : AsSmall.{max u (v+2)} Grpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} Grpd.{v+1,v+1} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def liftTm' : AsSmall.{max u (v+2)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} PGrpd.{v+1,v+1} :=
  AsSmall.down ⋙ PGrpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def tp' : AsSmall.{max u (v+1)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+1)} Grpd.{v,v} :=
  AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up

theorem liftTm'_tp' : Cat.homOf liftTm'.{v,u} ≫ Cat.homOf tp'.{v+1, max u (v+2)} =
  Cat.homOf tp'.{v, max u (v+2)} ≫ Cat.homOf liftTy'.{v,u} := rfl

/--
The following square is a meta-theoretic pullback

PGrpd.{v} ------- asSmallFunctor ------> PGrpd.{v+1}
    |                                     |
    |                                     |
forgetToGrpd                        forgetToGrpd
    |                                     |
    |                                     |
    v                                     v
Grpd.{v}  ------- asSmallFunctor ----->  Grpd.{v+1}

-/
def isPullback_forgetToGrpd_forgetToGrpd :
  Functor.IsPullback
    PGrpd.asSmallFunctor.{v+1}
    PGrpd.forgetToGrpd.{v}
    PGrpd.forgetToGrpd.{v+1}
    Grpd.asSmallFunctor.{v+1} :=
  Functor.IsPullback.ofIso (toPGrpd _) forget PGrpd.forgetToGrpd.{v+1}
  Grpd.asSmallFunctor.{v+1} (isPullback _)
  PGrpd.pGrpdToGroupoidalAsSmallFunctor
  PGrpd.groupoidalAsSmallFunctorToPGrpd
  PGrpd.groupoidalAsSmallFunctorToPGrpd_pGrpdToGroupoidalAsSmallFunctor
  PGrpd.pGrpdToGroupoidalAsSmallFunctor_groupoidalAsSmallFunctorToPGrpd

/--
The following square is a pullback

 AsSmall PGrpd.{v} ------- liftTm' ------> AsSmall PGrpd.{v+1}
        |                                     |
        |                                     |
        tp'                                   tp'
        |                                     |
        |                                     |
        v                                     v
 AsSmall Grpd.{v}  ------- liftTy' -----> AsSmall Grpd.{v+1}

in the category `Cat.{max u (v+2), max u (v+2)}`.
Note that these `AsSmall`s are bringing two different sized
categories into the same category.
-/
def isPullback_liftTm' : Functor.IsPullback
    liftTm'.{v,max u (v+2)}
    tp'.{_,max u (v+2)}
    tp'.{v+1,max u (v+2)}
    liftTy'.{v,max u (v+2)} :=
  Functor.IsPullback.ofIso' PGrpd.asSmallFunctor.{v+1} PGrpd.forgetToGrpd.{v}
    PGrpd.forgetToGrpd.{v+1} Grpd.asSmallFunctor.{v+1} isPullback_forgetToGrpd_forgetToGrpd
    liftTm'.{v,max u (v+2)} tp'.{_,max u (v+2)} tp'.{v+1,max u (v+2)} liftTy'.{v,max u (v+2)}
    AsSmall.downIso AsSmall.downIso AsSmall.downIso AsSmall.downIso rfl rfl rfl rfl

theorem isPullback_liftTm'_in_Cat : IsPullback
    (Cat.homOf liftTm'.{v,max u (v+2)})
    tp'.{_,max u (v+2)}
    tp'.{v+1,max u (v+2)}
    (Cat.homOf liftTy'.{v,max u (v+2)}) :=
  Cat.isPullback isPullback_liftTm'

/--
The small universes form pullbacks
      Tm.{v} ------------ liftTm ---------> Tm.{v+1}
        |                                     |
        |                                     |
      tp.{v}                                tp.{v+1}
        |                                     |
        v                                     v
      Ty.{v} ------------ liftTy ---------> Ty.{v+1}
-/
theorem liftTm_isPullback : IsPullback U.tp.{v, max u (v+2)} liftTm.{v,max u (v+2)}
    liftTy.{v,max u (v+2)} U.tp.{v+1, max u (v+2)} := by
  apply IsPullback.flip
  convert Functor.map_isPullback Core.map isPullback_liftTm'_in_Cat.{v,u}

variable {Γ : Ctx} (A : Γ ⥤ Grpd)

/--
∫ toCor...iv A ----> PGrpd
     |                  |
     |                  |
     |                  |
     V                  V
     Γ ------------> Grpd
-/
def isPullbackClassifier :
    Functor.IsPullback (toPGrpd A) Functor.Groupoidal.forget
    forgetToGrpd A :=
  Functor.Groupoidal.isPullback A

/--
  AsSmall PGrpd ----> PGrpd
     |                  |
     |                  |
     |                  |
     V                  V
  AsSmall Grpd ------> Grpd
-/
def isPullbackAsSmall :
    Functor.IsPullback AsSmall.down (AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up)
    PGrpd.forgetToGrpd AsSmall.down :=
  CategoryTheory.AsSmall.isPullback _

/--
∫ toCore...iv A ----> AsSmall PGrpd
     |                  |
     |                  |
     |                  |
     V                  V
     Γ ------------> AsSmall Grpd
-/
def isPullbackClassifierOfAsSmall :
    Functor.IsPullback (functorToAsSmallEquiv.symm (toPGrpd A))
    Functor.Groupoidal.forget (AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up)
    (functorToAsSmallEquiv.symm A) :=
  Functor.IsPullback.Paste.ofRight
    (by simp [functorToAsSmallEquiv, ← Functor.assoc, ← toPGrpd_forgetToGrpd]; rfl)
    (by rfl) isPullbackAsSmall
    (isPullbackClassifier A)

/--
coreAsSmall PGrpd ----> AsSmall PGrpd
     |                   |
     |                   |
     |                   |
     V                   V
coreAsSmall Grpd -----> AsSmall Grpd
-/

def isPullbackCoreAsSmall :
    Functor.IsPullback (Core.inclusion _) (Ctx.coreAsSmallFunctor PGrpd.forgetToGrpd)
    (AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up) (Core.inclusion _) :=
  Core.isPullback_map'_self _

/--
∫ toCo...iv A ----> coreAsSmall PGrpd
     |                  |
     |                  |
     |                  |
     V                  V
     Γ ------------> coreAsSmall Grpd
-/
def isPullbackClassifierOfCoreAsSmall (A : Γ ⟶ Ty) :
    Functor.IsPullback (var A) forget tp (toCoreAsSmallEquiv.symm (toCoreAsSmallEquiv A)) :=
  Functor.IsPullback.Paste.ofRight' (so := toCoreAsSmallEquiv.symm (toCoreAsSmallEquiv A))
  (by
    dsimp [functorToAsSmallEquiv]
    convert_to (toPGrpd (toCoreAsSmallEquiv A) ⋙ forgetToGrpd) ⋙ AsSmall.up = _
    erw [toPGrpd_forgetToGrpd, Core.functorToCoreEquiv_apply, Core.functorToCore_comp_inclusion,
      Functor.assoc])
  (isPullbackClassifierOfAsSmall (toCoreAsSmallEquiv A))
  (by
    dsimp [Ctx.coreAsSmallFunctor, Grpd.homOf]
    rw [Core.core_comp_inclusion])
  isPullbackCoreAsSmall (var A)
  (by
    apply (isPullbackCoreAsSmall).lift_uniq
    · simp only [U.var, toCoreAsSmallEquiv, Equiv.symm_trans_apply, Equiv.symm_symm]
      erw [Core.functorToCoreEquiv_apply, Core.functorToCore_comp_inclusion]
      rfl
    · rw [U.var, ← toCoreAsSmallEquiv_symm_apply_comp_left,
        ← toCoreAsSmallEquiv_symm_apply_comp_right, toPGrpd_forgetToGrpd])

/--
  The following square is a pullback in `Ctx`
  Ty.ext A --- Ty.var A ---> Tm
     |                     |
     |                     |
     |                     |
  Ty.disp A                 tp
     |                     |
     |                     |
     V                     V
     Γ --------- A ------> Ty
-/
theorem disp_pullback (A : Γ ⟶ Ty) : IsPullback (var A) forget tp A := by
  convert Grpd.isPullback (isPullbackClassifierOfCoreAsSmall A)
  simp

end IsPullback
end GroupoidModel
