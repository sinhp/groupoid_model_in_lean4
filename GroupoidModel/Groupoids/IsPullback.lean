import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat

import GroupoidModel.Russell_PER_MS.NaturalModel
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal
import GroupoidModel.Groupoids.Basic

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory ULift Grothendieck.Groupoidal
  Limits NaturalModelBase CategoryTheory.Functor

namespace GroupoidModel
namespace IsPullback

def groupoidalAsSmallFunctorToPGrpd :
    ∫(Grpd.asSmallFunctor.{max w (v+1), v, v}) ⥤ PGrpd.{v,v} where
  obj x := PGrpd.fromGrpd x.base
    (AsSmall.down.obj.{v, v, max w (v + 1)} x.fiber)
  map f := {
    toFunctor := f.base
    point := AsSmall.down.map f.fiber}
  map_comp f g := by
    simp only [comp_fiber, eqToHom_refl, Category.id_comp]
    rfl

def pGrpdToGroupoidalAsSmallFunctor : PGrpd.{v, v} ⥤
    ∫(Grpd.asSmallFunctor.{max w (v+1), v, v}) where
  obj x := {
    base := Grpd.of x
    fiber := AsSmall.up.obj.{v, v, max w (v + 1)} x.str.pt}
  map f := {
    base := f.toFunctor
    fiber := AsSmall.up.map f.point}
  map_comp f g := by
    apply Grothendieck.Groupoidal.ext
    · simp [Grpd.asSmallFunctor]
    · rfl

namespace PGrpd.IsMegaPullback'

variable {C : Type u₂} [Category.{v₁} C]
  {fst : C ⥤ PGrpd.{max w (v+1),max w (v+1)}}
  {snd : C ⥤ Grpd.{v,v}}
  (condition : fst ⋙ PGrpd.forgetToGrpd.{max w (v+1),max w (v+1)}
    = snd ⋙ Grpd.asSmallFunctor.{max w (v+1), v, v})

variable (fst) (snd)

def lift : C ⥤ PGrpd.{v,v} :=
  IsMegaPullback.lift fst snd condition
  ⋙ groupoidalAsSmallFunctorToPGrpd.{w,v}

def fac_left : lift fst snd condition
    ⋙ PGrpd.asSmallFunctor.{max w (v+1)} = fst :=
  IsMegaPullback.fac_left fst snd condition

def fac_right : lift fst snd condition
    ⋙ PGrpd.forgetToGrpd.{v} = snd :=
  IsMegaPullback.fac_right fst snd condition

def lift_uniq (m : C ⥤ PGrpd.{v,v})
    (hl : m ⋙ PGrpd.asSmallFunctor.{max w (v+1)} = fst)
    (hr : m ⋙ PGrpd.forgetToGrpd.{v} = snd) :
    m = lift fst snd condition := by
  unfold lift
  convert_to (m ⋙ pGrpdToGroupoidalAsSmallFunctor.{max w (v+1)})
    ⋙ groupoidalAsSmallFunctorToPGrpd = _
  rw [IsMegaPullback.lift_uniq fst snd condition
    (m ⋙ pGrpdToGroupoidalAsSmallFunctor.{max w (v+1)}) hl hr]

end PGrpd.IsMegaPullback'

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

theorem comm_sq : Cat.homOf toE''.{v,u} ≫ Cat.homOf π''.{v+1, max u (v+2)} =
  Cat.homOf π''.{v, max u (v+2)} ≫ Cat.homOf toU''.{v,u} := rfl

def toE''' : AsSmall.{v+1} PGrpd.{v,v}
    ⥤ PGrpd.{v+1,v+1} :=
  AsSmall.down ⋙ PGrpd.asSmallFunctor.{v+1}

def toU''' : AsSmall.{v+1} Grpd.{v,v}
    ⥤ Grpd.{v+1,v+1} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1}

theorem isPullback_uLiftGrothendieckForget_forgetToGrpd :
    IsPullback
      (Cat.homOf (ULift.downFunctor ⋙ toPGrpd toU'''.{v}))
      (Grothendieck.IsPullback.uLiftGrothendieckForget (toU''' ⋙ Grpd.forgetToCat))
      (Cat.homOf PGrpd.forgetToGrpd.{v+1,v+1})
      (Cat.homOf (ULift.downFunctor.{v+1,v+1} ⋙ toU'''.{v})) :=
  isPullback _

section IsPullbackInCat

variable (s : PullbackCone
    (Cat.homOf (π''.{v+1,max u (v+2)}))
    (Cat.homOf (toU''.{v,max u (v+2)})))

def fst' : s.pt ⥤ PGrpd.{v+1,v+1} := s.fst ⋙ AsSmall.down

def snd' : s.pt ⥤ Grpd.{v,v} := s.snd ⋙ AsSmall.down

theorem condition' : fst' s ⋙ PGrpd.forgetToGrpd.{v+1,v+1}
    = snd' s ⋙ Grpd.asSmallFunctor.{v+1, v, v} :=
  AsSmall.comp_up_inj s.condition

open PGrpd.IsMegaPullback'

def lift' : s.pt ⟶
    Cat.of (AsSmall.{max u (v+2)} PGrpd.{v,v}) :=
  Cat.homOf
    (lift.{v+1} (fst' s) (snd' s) (condition' s) ⋙ AsSmall.up)

theorem fac_left' : lift' s ≫ Cat.homOf toE'' = s.fst :=
  AsSmall.comp_down_inj (fac_left.{v+1} _ _ (condition' s))

theorem fac_right' : lift' s ≫ Cat.homOf π''.{_,max u (v+2)} = s.snd :=
  AsSmall.comp_down_inj (fac_right.{v+1} _ _ (condition' s))

theorem lift_uniq' (m : s.pt ⟶ Cat.of (AsSmall PGrpd))
    (hl : m ≫ Cat.homOf toE'' = s.fst)
    (hr : m ≫ Cat.homOf π''.{_,max u (v+2)} = s.snd) :
    m = lift' s := by
  have hl' : (m ⋙ AsSmall.down) ⋙ PGrpd.asSmallFunctor.{v+1}
    = s.fst ⋙ AsSmall.down := by rw [← hl]; rfl
  have hr' : (m ⋙ AsSmall.down) ⋙ PGrpd.forgetToGrpd.{v}
    = snd' s := by dsimp [snd']; rw [← hr]; rfl
  apply AsSmall.comp_down_inj
  exact lift_uniq.{v+1} _ _ (condition' s) _ hl' hr'

end IsPullbackInCat

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
We prove this is pullback by using the fact that this `IsMegaPullback`,
i.e. it is universal among categories of all sizes.
-/
theorem isPullback_π''_π'' :
    IsPullback
      (Cat.homOf toE''.{v,max u (v+2)})
      (Cat.homOf π''.{_,max u (v+2)})
      (Cat.homOf π''.{v+1,max u (v+2)})
      (Cat.homOf toU''.{v,max u (v+2)}) :=
  IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk
      comm_sq lift' fac_left' fac_right' lift_uniq')

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
    IsPullback
      ym(toE.{v,max u (v+2)})
      ym(π.{v, max u (v+2)})
      ym(π.{v+1,max u (v+2)})
      ym(toU.{v,max u (v+2)}) :=
  Functor.map_isPullback yoneda
    (Functor.map_isPullback Ctx.ofGrpd
      (Functor.map_isPullback Core.map
    isPullback_π''_π''))

end SmallUHom

namespace SmallBase

open U PGrpd

abbrev coreΓ (Γ : Ctx.{max u (v+1)}) : Grpd.{max u (v+1), max u (v+1)} :=
  Core.map.obj (Cat.of (Ctx.toGrpd.obj Γ))

section
variable {Γ : Ctx.{max u (v+1)}} (A : Γ ⟶ U.{v})

abbrev ext' : Grpd.{max u (v+1), max u (v+1)}:=
  Grpd.of ∫(classifier A)

abbrev disp' : ext' A ⟶ Ctx.toGrpd.obj Γ :=
  forget

abbrev coreExt' : Grpd.{max u (v+1), max u (v+1)}:=
  Core.map.obj (Cat.of ∫(classifier A))

abbrev coreDisp' : coreExt' A ⟶ coreΓ.{v,u} Γ :=
  Core.map.map $ Cat.homOf $ Grothendieck.forget _

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
    = Cat.homOf (Grothendieck.forget (classifier A ⋙ Grpd.forgetToCat))
    ≫ Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)) := rfl
end

variable {Γ : Ctx.{max u (v+1)}} (A : Γ ⟶ U.{v, max u (v+1)})

section IsPullback

variable {A}
  (s : PullbackCone
    (Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd)))
    (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd))))

def comm_sq : s.fst ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd
    = s.snd ⋙ classifier A := by
  convert_to s.fst ⋙ AsSmall.down ⋙ forgetToGrpd
    ⋙ AsSmall.up ⋙ AsSmall.down.{v, v + 1, max u (v + 1)} = _
  have := s.condition
  simp only [Cat.asSmallFunctor_obj, Cat.asSmallFunctor_map,
    ← Functor.assoc, Cat.comp_eq_comp, classifier] at *
  rw [← this]

def lift : s.pt ⟶ Cat.of (∫(classifier A)) :=
  IsMegaPullback.lift
    (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)

@[simp] theorem fac_left : lift s
    ≫ Cat.homOf (toPGrpd (classifier A) ⋙ AsSmall.up)
    = s.fst := by
  convert_to _ = s.fst ⋙ AsSmall.down
    ⋙ AsSmall.up
  simp only [← Functor.assoc]
  rw [← IsMegaPullback.fac_left
    (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)]
  rfl

@[simp] theorem fac_right : lift s
    ≫ Cat.homOf (Grothendieck.forget
      (classifier A ⋙ Grpd.forgetToCat))
    = s.snd :=
  IsMegaPullback.fac_right
    (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)

theorem lift_uniq
    (m : s.pt ⟶ Cat.of (Grothendieck
      (classifier A ⋙ Grpd.forgetToCat)))
    (hl : m ≫ Cat.homOf (toPGrpd
      (classifier A) ⋙ AsSmall.up)
      = s.fst)
    (hr : m ≫ Cat.homOf (Grothendieck.forget
      (classifier A ⋙ Grpd.forgetToCat))
      = s.snd) : m = lift s := by
  apply Grothendieck.Groupoidal.IsMegaPullback.lift_uniq
  · rw [← hl] ; rfl
  · rw [← hr] ; rfl

theorem isPullback_disp'_asSmallForgetToGrpd :
    IsPullback
      (Cat.homOf (toPGrpd (classifier A) ⋙ AsSmall.up))
      (Cat.homOf (Grothendieck.forget
        (classifier A ⋙ Grpd.forgetToCat)))
      (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd))
      (Cat.homOf (Ctx.toGrpd.map A ⋙
        Core.inclusion (AsSmall Grpd))) :=
  IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk
      (isPullback_disp'_asSmallForgetToGrpd_comm_sq A)
      lift fac_left fac_right lift_uniq)

end IsPullback

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
    (Grpd.homOf (Core.map' π''))
    (coreA A) :=
  Functor.map_isPullback
    Core.map isPullback_disp'_asSmallForgetToGrpd

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
    (Grpd.homOf (Core.map' π''))
    (Ctx.toGrpd.map A) := by
  convert IsPullback.paste_horiz
    (isPullback_disp'_coreDisp' A) (isPullback_coreDisp'_π' A)
  convert_to Ctx.toGrpd.map A =
    Grpd.homOf (Core.functorToCore (𝟭 ↑Γ.1)) ≫
      Core.map.map (Cat.homOf (Ctx.toGrpd.map A))
      ≫ Core.map.map (Cat.homOf (Core.inclusion (AsSmall Grpd)))
  have h := Core.adjunction.unit.naturality (Ctx.toGrpd.map A)
  simp only [AsSmall.down_obj, Grpd.forgetToCat, Ctx.equivalence_inverse,
    Core.adjunction, Functor.comp_map, id_eq, ← Category.assoc] at *
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

end SmallBase

end IsPullback
end GroupoidModel
