import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Category.Cat.Limit

import GroupoidModel.Syntax.NaturalModel
import GroupoidModel.Grothendieck.Groupoidal.IsPullback
import GroupoidModel.Groupoids.Basic

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory ULift Functor.Groupoidal
  Limits NaturalModelBase

namespace GroupoidModel
namespace IsPullback

namespace SmallUHom

variable {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v})

def toU'' : AsSmall.{max u (v+2)} Grpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} Grpd.{v+1,v+1} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def toE'' : AsSmall.{max u (v+2)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} PGrpd.{v+1,v+1} :=
  AsSmall.down ⋙ PGrpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def π'' : AsSmall.{max u (v+1)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+1)} Grpd.{v,v} :=
  AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up

theorem toE''_π'' : Cat.homOf toE''.{v,u} ≫ Cat.homOf π''.{v+1, max u (v+2)} =
  Cat.homOf π''.{v, max u (v+2)} ≫ Cat.homOf toU''.{v,u} := rfl

-- TODO remove
-- def toE''' : AsSmall.{v+1} PGrpd.{v,v}
--     ⥤ PGrpd.{v+1,v+1} :=
--   AsSmall.down ⋙ PGrpd.asSmallFunctor.{v+1}

-- def toU''' : AsSmall.{v+1} Grpd.{v,v}
--     ⥤ Grpd.{v+1,v+1} :=
--   AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1}

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

 AsSmall PGrpd.{v} ------- toE'' ------> AsSmall PGrpd.{v+1}
        |                                     |
        |                                     |
        π''                                   π''
        |                                     |
        |                                     |
        v                                     v
 AsSmall Grpd.{v}  ------- toU'' -----> AsSmall Grpd.{v+1}

in the category `Cat.{max u (v+2), max u (v+2)}`.
Note that these `AsSmall`s are bringing two different sized
categories into the same category.
-/
theorem isPullback_π''_π'' :
    IsPullback
      (Cat.homOf toE''.{v,max u (v+2)})
      (Cat.homOf π''.{_,max u (v+2)})
      (Cat.homOf π''.{v+1,max u (v+2)})
      (Cat.homOf toU''.{v,max u (v+2)}) :=
  Cat.isPullback rfl $
  Functor.IsPullback.ofIso' PGrpd.asSmallFunctor.{v+1} PGrpd.forgetToGrpd.{v}
    PGrpd.forgetToGrpd.{v+1} Grpd.asSmallFunctor.{v+1} isPullback_forgetToGrpd_forgetToGrpd
    toE''.{v,max u (v+2)} π''.{_,max u (v+2)} π''.{v+1,max u (v+2)} toU''.{v,max u (v+2)}
    AsSmall.downIso AsSmall.downIso AsSmall.downIso AsSmall.downIso rfl rfl rfl rfl

open U

/--
The small universes form pullbacks
      y(E.{v}) ------------ toE ---------> y(E.{v+1})
        |                                     |
        |                                     |
      y(π.{v})                              y(π.{v+1})
        |                                     |
        v                                     v
      y(U.{v}) ------------ toU ---------> y(U.{v+1})
-/
theorem isPullback_yπ_yπ :
    IsPullback ym(toE.{v,max u (v+2)}) ym(π.{v, max u (v+2)})
      ym(π.{v+1,max u (v+2)}) ym(toU.{v,max u (v+2)}) :=
  Functor.map_isPullback yoneda
    (Functor.map_isPullback Ctx.ofGrpd
      (Functor.map_isPullback Core.map
    isPullback_π''_π''))

end SmallUHom

namespace SmallU

open U PGrpd

abbrev coreΓ (Γ : Ctx.{max u (v+1)}) : Grpd.{max u (v+1), max u (v+1)} :=
  Core.map.obj (Cat.of (Ctx.toGrpd.obj Γ))

section
variable {Γ : Ctx.{max u (v+1)}} (A : Γ ⟶ U.{v})

abbrev ext' : Grpd.{max u (v+1), max u (v+1)}:=
  Grpd.of (∫ classifier A)

abbrev disp' : ext' A ⟶ Ctx.toGrpd.obj Γ :=
  forget

abbrev coreExt' : Grpd.{max u (v+1), max u (v+1)}:=
  Core.map.obj (Cat.of (∫ classifier A))

abbrev coreDisp' : coreExt' A ⟶ coreΓ.{v,u} Γ :=
  Core.map.map $ Cat.homOf $ forget

abbrev coreVar' : coreExt' A ⟶
    Core.map.obj.{max u (v+1), max u (v+1)}
      (Cat.asSmallFunctor.obj.{max u (v+1),v,v+1} (Cat.of PGrpd.{v,v})) :=
  Core.map.map $ Cat.homOf (toPGrpd (classifier A) ⋙ AsSmall.up)

abbrev coreA : coreΓ.{v,max u (v+1)} Γ ⟶ Core.map.obj.{max u (v+1), max u (v+1)}
      (Cat.asSmallFunctor.obj.{u,v,v+1} (Cat.of Grpd.{v,v})) :=
  Core.map.map (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd.{v,v})))

def isPullback_disp'_asSmallForgetToGrpd_comm_sq :
    Cat.homOf (toPGrpd (classifier A) ⋙ AsSmall.up)
    ≫ Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd))
    = Cat.homOf (Functor.Grothendieck.forget (classifier A ⋙ Grpd.forgetToCat))
    ≫ Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)) := rfl
end

variable {Γ : Ctx.{max u (v+1)}} (A : Γ ⟶ U.{v, max u (v+1)})

-- section IsPullback

-- variable {C : Type*} [Category C] (Cn : C ⥤ AsSmall PGrpd)
--   (Cw : C ⥤ ↑(Ctx.toGrpd.obj Γ))
--   (hC : Cn ⋙ AsSmall.down ⋙ forgetToGrpd ⋙ AsSmall.up
--     = Cw ⋙ Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd))

-- TODO remove
-- include hC in
-- theorem isPullback_disp'_asSmallForgetToGrpd.universal_aux :
--     (Cn ⋙ AsSmall.down) ⋙ forgetToGrpd = Cw ⋙ classifier A := by
--   erw [← congrArg (fun x => Functor.comp x AsSmall.down) hC]
--   rfl

-- def isPullback_disp'_asSmallForgetToGrpd.universal : (lift : C ⥤ ∫(classifier A)) ×'
--     lift ⋙ toPGrpd (classifier A) ⋙ AsSmall.up = Cn ∧
--     lift ⋙ Grothendieck.forget (classifier A ⋙ Grpd.forgetToCat) = Cw ∧
--     ∀ {l0 l1 : C ⥤ ∫(classifier A)},
--     l0 ⋙ toPGrpd (classifier A) ⋙ AsSmall.up = l1 ⋙ toPGrpd (classifier A) ⋙ AsSmall.up
--     → l0 ⋙ Grothendieck.forget (classifier A ⋙ Grpd.forgetToCat)
--     = l1 ⋙ Grothendieck.forget (classifier A ⋙ Grpd.forgetToCat)
--     → l0 = l1 :=
--   ⟨ (Grothendieck.Groupoidal.isPullback (classifier A)).lift (Cn ⋙ AsSmall.down)
--     Cw (universal_aux A Cn Cw hC),
--     by rw [← Functor.assoc, (Grothendieck.Groupoidal.isPullback _).fac_left]; rfl,
--     (Grothendieck.Groupoidal.isPullback _).fac_right _ _ _,
--     fun hn hw => (Grothendieck.Groupoidal.isPullback _).hom_ext
--       (congrArg (fun x => Functor.comp x AsSmall.down) hn) hw
--     ⟩

theorem isPullback_disp'_asSmallForgetToGrpd :
    IsPullback
      (Cat.homOf (toPGrpd (classifier A) ⋙ AsSmall.up))
      (Cat.homOf (Functor.Grothendieck.forget
        (classifier A ⋙ Grpd.forgetToCat)))
      (Cat.homOf $ AsSmall.down ⋙ forgetToGrpd ⋙ AsSmall.up)
      (Cat.homOf (Ctx.toGrpd.map A ⋙
        Core.inclusion (AsSmall Grpd))) :=
  Cat.isPullback rfl $ Functor.IsPullback.ofIso'
    (toPGrpd (classifier A))
    (Functor.Grothendieck.forget (classifier A ⋙ Grpd.forgetToCat))
    forgetToGrpd
    (classifier A)
    (Functor.Groupoidal.isPullback (classifier A))
    (toPGrpd (classifier A) ⋙ AsSmall.up)
    (Functor.Grothendieck.forget (classifier A ⋙ Grpd.forgetToCat))
    (AsSmall.down ⋙ forgetToGrpd ⋙ AsSmall.up)
    (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd))
    (Functor.Iso.refl _)
    AsSmall.downIso
    (Functor.Iso.refl _)
    AsSmall.downIso
    rfl
    rfl
    rfl
    rfl

open SmallUHom

/--
  The following square is a pullback in `Grpd`
Core(U.ext' A) -- U.coreVar' A ---> U'
     |                              |
     |                              |
     |                              |
     |                              |
Core(U.disp' A)                     π'
     |                              |
     |                              |
     V                              V
Core(Ctx.toGrpd.obj Γ) - coreA A -> E'
-/
theorem isPullback_coreDisp'_π' :
  IsPullback
    (coreVar' A)
    (coreDisp' A)
    (Grpd.homOf π''.core)
    (coreA A) :=
  Functor.map_isPullback
    Core.map (isPullback_disp'_asSmallForgetToGrpd A)

/--
  The following square is a pullback in `Grpd`
 U.ext' A ------- functorToCore ---> Core(U.ext' A)
     |                                     |
     |                                     |
     |                                     |
     π'                              Core(U.disp' A)
     |                                     |
     |                                     |
     V                                     V
 Ctx.toGrpd.obj Γ - functorToCore -> Core(Ctx.toGrpd.obj Γ)
-/
theorem isPullback_disp'_coreDisp' :
  IsPullback
    (Grpd.homOf (Core.functorToCore (Functor.id _)))
    (disp' A)
    (coreDisp' A)
    (Grpd.homOf (Core.functorToCore (Functor.id _))) :=
  IsPullback.of_horiz_isIso ⟨ rfl ⟩

/--
  The following square is a pullback in `Grpd`
  U.ext' A -- U.var' A ---> U'
     |                      |
     |                      |
     |                      |
  U.disp' A                 π'
     |                      |
     |                      |
     V                      V
Ctx.toGrpd.obj Γ ---------> E'
           Ctx.toGrpd.map A
-/
theorem isPullback_disp'_π' :
  IsPullback
    (Grpd.homOf (Core.functorToCore (toPGrpd (classifier A) ⋙ AsSmall.up)))
    (disp' A)
    (Grpd.homOf π''.core)
    (Ctx.toGrpd.map A) := by
  convert IsPullback.paste_horiz
    (isPullback_disp'_coreDisp' A) (isPullback_coreDisp'_π' A)
  convert_to Ctx.toGrpd.map A =
    Grpd.homOf (Core.functorToCore (𝟭 Γ.1)) ≫
      Core.map.map (Cat.homOf (Ctx.toGrpd.map A))
      ≫ Core.map.map (Cat.homOf (Core.inclusion (AsSmall Grpd)))
  have h := Core.adjunction.unit.naturality (Ctx.toGrpd.map A)
  simp only [AsSmall.down_obj, Grpd.forgetToCat, Ctx.equivalence,
    Core.adjunction, Functor.comp_map, id_eq, ← Category.assoc, Ctx.toGrpd] at *
  rw [← h]
  rfl

/--
  The following square is a pullback in `Ctx`
  U.ext A --- U.var A ---> E
     |                     |
     |                     |
     |                     |
  U.disp A                 π
     |                     |
     |                     |
     V                     V
     Γ --------- A ------> U
-/
theorem isPullback_disp_π :
  IsPullback
    (U.var A)
    (U.disp A)
    π
    A :=
  Functor.map_isPullback Ctx.ofGrpd (isPullback_disp'_π' A)

/--
  The following square is a pullback in `Psh Ctx`
  y(U.ext A) --- ym(U.var A) ---> y(E)
     |                              |
     |                              |
     |                              |
  ym(U.disp A)                   ym(π)
     |                              |
     |                              |
     V                              V
   y(Γ) ------------- ym(A) ----> y(U)
-/
theorem isPullback_yonedaDisp_yonedaπ :
  IsPullback
    ym(U.var A)
    ym(U.disp A)
    ym(π)
    ym(A) :=
  Functor.map_isPullback yoneda (isPullback_disp_π A)

end SmallU

end IsPullback
end GroupoidModel
