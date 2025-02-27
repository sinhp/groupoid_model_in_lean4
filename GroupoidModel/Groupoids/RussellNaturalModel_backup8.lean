import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat

import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory ULift Grothendieck
  Limits NaturalModelBase CategoryTheory.Functor

namespace CategoryTheory

namespace ULift
namespace Core

variable {C : Type u} [Category.{v} C]

-- FIXME could be generalized?
def isoCoreULift :
    Cat.of (ULift.{w} (Core C)) ≅
      Cat.of (Core (ULift.{w} C)) where
  hom := Cat.homOf (downFunctor ⋙ Core.functor' upFunctor)
  inv := Cat.homOf (Core.functor' downFunctor ⋙ upFunctor)

end Core
end ULift

abbrev groupoidalAsSmallFunctor : Type (max w (v+1)) :=
  Groupoidal $
    Grpd.asSmallFunctor.{max w (v+1), v, v}

def groupoidalAsSmallFunctorToPGrpd :
    groupoidalAsSmallFunctor.{w,v} ⥤ PGrpd.{v,v} where
  obj x := PGrpd.fromGrpd x.base
    (AsSmall.down.obj.{v, v, max w (v + 1)} x.fiber)
  map f := {
    toFunctor := f.base
    point := AsSmall.down.map f.fiber}

def pGrpdToGroupoidalAsSmallFunctor :
    PGrpd.{v, v} ⥤ groupoidalAsSmallFunctor.{w,v} where
  obj x := {
    base := Grpd.of x
    fiber := AsSmall.up.obj.{v, v, max w (v + 1)} x.str.pt}
  map f := {
    base := f.toFunctor
    fiber := AsSmall.up.map f.point}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [Grpd.forgetToCat, Grpd.asSmallFunctor]
    · rfl

namespace PGrpd.IsMegaPullback'

variable {C : Type u₂} [Category.{v₁} C]
  {fst : C ⥤ PGrpd.{max w (v+1),max w (v+1)}}
  {snd : C ⥤ Grpd.{v,v}}
  (condition : fst ⋙ PGrpd.forgetToGrpd.{max w (v+1),max w (v+1)}
    = snd ⋙ Grpd.asSmallFunctor.{max w (v+1), v, v})

variable (fst) (snd)

def lift : C ⥤ PGrpd.{v,v} :=
  Groupoidal.IsMegaPullback.lift fst snd condition
  ⋙ groupoidalAsSmallFunctorToPGrpd.{w,v}

def fac_left : lift fst snd condition
    ⋙ PGrpd.asSmallFunctor.{max w (v+1)} = fst :=
  Groupoidal.IsMegaPullback.fac_left fst snd condition

def fac_right : lift fst snd condition
    ⋙ PGrpd.forgetToGrpd.{v} = snd :=
  Groupoidal.IsMegaPullback.fac_right fst snd condition

def uniq (m : C ⥤ PGrpd.{v,v})
    (hl : m ⋙ PGrpd.asSmallFunctor.{max w (v+1)} = fst)
    (hr : m ⋙ PGrpd.forgetToGrpd.{v} = snd) :
    m = lift fst snd condition := by
  unfold lift
  convert_to (m ⋙ pGrpdToGroupoidalAsSmallFunctor.{max w (v+1)})
    ⋙ groupoidalAsSmallFunctorToPGrpd = _
  rw [Groupoidal.IsMegaPullback.uniq fst snd condition
    (m ⋙ pGrpdToGroupoidalAsSmallFunctor.{max w (v+1)}) hl hr]
  rfl

end PGrpd.IsMegaPullback'

namespace LargeUniverse

open PGrpd PGrpd.IsPullback

def CAT : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (Cat.{max u (v+1), max u (v+1)})
def PCAT : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (PCat.{max u (v+1), max u (v+1)})
def GRPD : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (Grpd.{max u (v+1), max u (v+1)})
def PGRPD : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (PGrpd.{max u (v+1), max u (v+1)})
def grpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} Grpd.{v,v})
def pgrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} PGrpd.{v,v})
def coregrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of $ Core $ IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} Grpd.{v,v})
def corepgrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of $ Core $ IsPullback.uLiftΓ.{max u (v+1)} (AsSmall.{u} PGrpd.{v,v})

def GROTH : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of (ULift.{max u (v+1) + 1, max u (v+1)}
        groupoidalAsSmallFunctor.{u,v})

def PCATFORGETTOCAT : PCAT.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf PCat.forgetToCat.{max u (v+1), max u (v+1)}
def PGRPDFORGETTOGRPD : PGRPD.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf PGrpd.forgetToGrpd.{max u (v+1), max u (v+1)}
def GRPDFORGETTOCAT : GRPD.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf Grpd.forgetToCat.{max u (v+1), max u (v+1)}
def PGRPDFORGETTOPCAT : PGRPD.{v,u} ⟶ PCAT.{v,u} :=
  Cat.homOf PGrpd.forgetToPCat.{max u (v+1), max u (v+1)}

def pgrpdforgettogrpd : pgrpd.{v,u} ⟶ grpd.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor)
def grpdassmallfunctor : grpd.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ Grpd.asSmallFunctor.{max u (v+1)})
def pgrpdassmallfunctor : pgrpd.{v,u} ⟶ PGRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.asSmallFunctor.{max u (v+1)})
def corepgrpdforgettogrpd : corepgrpd.{v,u} ⟶ coregrpd.{v,u} :=
  Cat.homOf $ Core.functor' $
    downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor

def coreFunctorPGrpdForgetToGrpd : corepgrpd.{v,u} ⟶ coregrpd.{v,u} :=
  Cat.homOf (Core.functor.map pgrpdforgettogrpd)

def inclusionGrpdCompAsSmallFunctor : coregrpd.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf (
    Core.inclusion _
    ⋙ downFunctor
    ⋙ AsSmall.down
    ⋙ Grpd.asSmallFunctor.{max u (v+1)})

def inclusionPGrpdCompAsSmallFunctor : corepgrpd.{v,u} ⟶ PGRPD.{v,u} :=
  Cat.homOf (
    Core.inclusion _
    ⋙ downFunctor
    ⋙ AsSmall.down
    ⋙ PGrpd.asSmallFunctor.{max u (v+1)})

def asSmallFunctorCompForgetToCat' :
    AsSmall.{u} Grpd.{v,v} ⥤ Cat.{max u (v+1), max u (v+1)} :=
  AsSmall.down
    ⋙ Grpd.asSmallFunctor.{max u (v+1), v, v}
    ⋙ Grpd.forgetToCat.{max u (v+1)}


def groupoidalAsSmallFunctorToGrothendieckAsSmallFunctor' :
    groupoidalAsSmallFunctor.{u,v}
    ⥤ Grothendieck asSmallFunctorCompForgetToCat'.{v,u} where
  obj x := {
    base := AsSmall.up.obj x.base
    fiber := x.fiber}
  map f := {
    base := AsSmall.up.map f.base
    fiber := f.fiber
    }
  map_comp f g := by
    apply Grothendieck.ext
    · simp [asSmallFunctorCompForgetToCat']
    · rfl

def groupoidalAsSmallFunctorToGrothendieckAsSmallFunctor :
    Grothendieck asSmallFunctorCompForgetToCat'.{v,u}
    ⥤ groupoidalAsSmallFunctor.{u,v} where
  obj x := {
    base :=  AsSmall.down.obj x.base
    fiber := x.fiber}
  map f := {
    base := AsSmall.down.map f.base
    fiber := f.fiber}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [asSmallFunctorCompForgetToCat']
    · rfl

def pGrpd_iso_GrothendieckAsSmallFunctor :
    pgrpd.{v,u}
      ≅ Cat.of (ULift.{max u (v+1) + 1, max u (v+1)}
        groupoidalAsSmallFunctor.{u,v}) where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGroupoidalAsSmallFunctor
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ groupoidalAsSmallFunctorToPGrpd
    ⋙ AsSmall.up
    ⋙ ULift.upFunctor

def pGrpdIsoULiftGrothendieck :
    pgrpd.{v,u}
      ≅ IsPullback.uLiftGrothendieck
        asSmallFunctorCompForgetToCat'.{v,u} where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGroupoidalAsSmallFunctor
    ⋙ groupoidalAsSmallFunctorToGrothendieckAsSmallFunctor'
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ groupoidalAsSmallFunctorToGrothendieckAsSmallFunctor
    ⋙ groupoidalAsSmallFunctorToPGrpd
    ⋙ AsSmall.up
    ⋙ ULift.upFunctor

/--
The following square is a pullback

Grothendieck (asSmallFunctor...) -- toPGrpd --> PCat.{max v u, max v u}
        |                                     |
        |                                     |
    forget                               PCat.forgetToCat
        |                                     |
        v                                     v
 Grpd.{v,v}--asSmallFunctor ⋙ forgetToCat-->Cat.{max v u, max v u}
-/
theorem isPullback_uLiftGrothendieckForgetAsSmallFunctorCompForgetToCat'_PCATFORGETTOCAT
    : IsPullback
      (IsPullback.uLiftToPCat asSmallFunctorCompForgetToCat'.{v,u}
        ⋙ Cat.ULift_iso_self.hom)
      (IsPullback.uLiftGrothendieckForget asSmallFunctorCompForgetToCat')
      PCATFORGETTOCAT.{v,u}
      (IsPullback.uLiftA asSmallFunctorCompForgetToCat'
        ⋙ Cat.ULift_iso_self.hom)
      :=
  IsPullback.paste_horiz
    (Grothendieck.isPullback.{max u (v+1)} (asSmallFunctorCompForgetToCat'.{v,u}))
    (IsPullback.of_horiz_isIso ⟨rfl⟩)

/--
The following square is a pullback

   PGrpd.{v,v} -- PGrpd.asSmallFunctor ⋙ PGrpd.forgetToPCat --> PCat.{max v u, max v u}
        |                                                           |
        |                                                           |
    PGrpd.forgetToGrpd                                          PCat.forgetToCat
        |                                                           |
        |                                                           |
        v                                                           v
   Grpd.{v,v}  -- Grpd.asSmallFunctor ⋙ Grpd.forgetToCat --> Cat.{max v u, max v u}
-/
theorem isPullback_pgrpdforgettogrpd_PCATFORGETTOCAT :
  IsPullback
    (pgrpdassmallfunctor ≫ PGRPDFORGETTOPCAT.{v,u})
    pgrpdforgettogrpd.{v,u}
    PCATFORGETTOCAT.{v,u}
    (grpdassmallfunctor ≫ GRPDFORGETTOCAT.{v,u}) :=
  IsPullback.of_iso_isPullback
    isPullback_uLiftGrothendieckForgetAsSmallFunctorCompForgetToCat'_PCATFORGETTOCAT
    pGrpdIsoULiftGrothendieck

/--
The following square is a pullback

   PGrpd.{v,v} -- PGrpd.asSmallFunctor --> PGrpd.{max v u, max v u}
        |                                     |
        |                                     |
    PGrpd.forgetToGrpd                    PGrpd.forgetToGrpd
        |                                     |
        v                                     v
   Grpd.{v,v}  -- Grpd.asSmallFunctor --> Grpd.{max v u, max v u}
-/
theorem isPullback_pgrpdforgettogrpd_PGRPDFORGETTOGRPD :
    IsPullback
      pgrpdassmallfunctor.{v,u}
      pgrpdforgettogrpd.{v,u}
      PGRPDFORGETTOGRPD.{v,u}
      grpdassmallfunctor.{v,u} :=
  IsPullback.of_right
    isPullback_pgrpdforgettogrpd_PCATFORGETTOCAT.{v,u}
    rfl
    isPullback_forgetToGrpd_forgetToCat

theorem isPullback_forgetToGrpd_forgetToGrpd_comm_sq :
    pgrpdassmallfunctor.{v,u}
    ≫ PGRPDFORGETTOGRPD.{v,u}
    = pgrpdforgettogrpd.{v,u}
    ≫ grpdassmallfunctor.{v,u} :=
  rfl

namespace IsPullback
variable (s : PullbackCone PGRPDFORGETTOGRPD.{v,u} grpdassmallfunctor.{v,u})

-- def fst : s.pt ⥤ PGrpd.{max u (v+1),max u (v+1)} := s.fst

def snd : s.pt ⥤ Grpd.{v,v} := s.snd ⋙ ULift.downFunctor ⋙ AsSmall.down

def condition : s.fst ⋙ PGrpd.forgetToGrpd
    = snd s ⋙ Grpd.asSmallFunctor.{max u (v+1),v} :=
  s.condition

def lift : s.pt ⟶ pgrpd.{v} :=
  Cat.homOf $
    IsMegaPullback'.lift s.fst (snd s) (condition s)
    ⋙ AsSmall.up ⋙ ULift.upFunctor

end IsPullback

open IsPullback

/--
The following square is a pullback

   PGrpd.{v,v} -- PGrpd.asSmallFunctor --> PGrpd.{max v u, max v u}
        |                                     |
        |                                     |
    PGrpd.forgetToGrpd                    PGrpd.forgetToGrpd
        |                                     |
        v                                     v
   Grpd.{v,v}  -- Grpd.asSmallFunctor --> Grpd.{max v u, max v u}
-/
theorem isPullback_forgetToGrpd_forgetToGrpd :
    IsPullback
      pgrpdassmallfunctor.{v,u}
      pgrpdforgettogrpd.{v,u}
      PGRPDFORGETTOGRPD.{v,u}
      grpdassmallfunctor.{v,u} :=
  IsPullback.of_isLimit $
  PullbackCone.IsLimit.mk
    isPullback_forgetToGrpd_forgetToGrpd_comm_sq
    IsPullback.lift
    (by
      intro s
      exact IsMegaPullback'.fac_left s.fst (snd s) (condition s))
    (by
      intro s
      convert_to (IsMegaPullback'.lift _ _ _ ⋙ forgetToGrpd) ⋙ AsSmall.up ⋙ upFunctor = s.snd
      rw [IsMegaPullback'.fac_right s.fst (snd s) (condition s)]
      rfl)
    (by
      intro s m hl hr
      convert_to (m ⋙ downFunctor ⋙ AsSmall.down) ⋙ AsSmall.up ⋙ upFunctor = _
      rw [IsMegaPullback'.uniq s.fst (snd s) (condition s)
        (m ⋙ ULift.downFunctor ⋙ AsSmall.down)
        hl (by simp only [snd, ← hr]; rfl)]
      rfl)

instance (C : Type u) [Category.{v} C] :
    (downFunctor : ULift.{w} C ⥤ C).ReflectsIsomorphisms :=
  ULift.equivalence.fullyFaithfulInverse.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (upFunctor : C ⥤ ULift.{w} C).ReflectsIsomorphisms :=
  ULift.equivalence.fullyFaithfulFunctor.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (AsSmall.down : AsSmall.{w} C ⥤ C).ReflectsIsomorphisms :=
  AsSmall.equiv.fullyFaithfulInverse.reflectsIsomorphisms

instance (C : Type u) [Category.{v} C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C).ReflectsIsomorphisms :=
  AsSmall.equiv.fullyFaithfulFunctor.reflectsIsomorphisms

instance : forgetToGrpd.ReflectsIsomorphisms := by
  constructor
  intro A B F hiso
  rcases hiso with ⟨ G , hFG , hGF ⟩
  use ⟨ G , G.map (Groupoid.inv F.point)
    ≫ eqToHom (Functor.congr_obj hFG A.str.pt) ⟩
  constructor
  · apply PointedFunctor.ext
    · simp
    · exact hFG
  · apply PointedFunctor.ext
    · simp
      have h := Functor.congr_hom hGF F.point
      simp [Grpd.id_eq_id, Grpd.comp_eq_comp, Functor.comp_map] at h
      simp [h, eqToHom_map]
    · exact hGF

instance : Functor.ReflectsIsomorphisms pgrpdforgettogrpd := by
  have : (forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor).ReflectsIsomorphisms := by
    rw [← Functor.assoc]
    apply reflectsIsomorphisms_comp
  have : (AsSmall.down
      ⋙ forgetToGrpd
      ⋙ AsSmall.up
      ⋙ upFunctor).ReflectsIsomorphisms := by
    apply reflectsIsomorphisms_comp
  have h : Functor.ReflectsIsomorphisms
    (downFunctor
    ⋙ AsSmall.down
    ⋙ forgetToGrpd
    ⋙ AsSmall.up
    ⋙ upFunctor) := by
    apply reflectsIsomorphisms_comp
  exact h

/--
The following square is a pullback

Core PGrpd.{v,v} -- PGrpd.asSmallFunctor --> PGrpd.{max v u, max v u}
        |                                     |
        |                                     |
Core PGrpd.forgetToGrpd             PGrpd.forgetToGrpd
        |                                     |
        v                                     v
Core Grpd.{v,v}  -- Grpd.asSmallFunctor --> Grpd.{max v u, max v u}
-/
theorem isPullback_corepgrpdforgettogrpd_PGRPDFORGETTOGRPD :
    IsPullback
      inclusionPGrpdCompAsSmallFunctor.{v,u}
      coreFunctorPGrpdForgetToGrpd.{v,u}
      PGRPDFORGETTOGRPD.{v,u}
      inclusionGrpdCompAsSmallFunctor.{v,u} :=
  IsPullback.paste_horiz
    (Core.isPullback_functor'_self pgrpdforgettogrpd.{v,u})
    (isPullback_pgrpdforgettogrpd_PGRPDFORGETTOGRPD.{v,u})

end LargeUniverse

namespace GroupoidNaturalModel

/--
Ctx is
the category of
{small groupoids - size u objects and size u hom sets}
which itself has size u+1 objects (small groupoids)
and size u hom sets (functors).

We want our context category to be a small category so we will use
`AsSmall.{u}` for some large enough `u`
-/
abbrev Ctx := AsSmall.{u} Grpd.{u,u}

namespace Ctx
def ofGrpd : Grpd.{u,u} ⥤ Ctx.{u} := AsSmall.up

def ofGroupoid (Γ : Type u) [Groupoid.{u} Γ] : Ctx.{u} :=
  ofGrpd.obj (Grpd.of Γ)

def toGrpd : Ctx.{u} ⥤ Grpd.{u,u} := AsSmall.down

instance : IsEquivalence Ctx.ofGrpd :=
    IsEquivalence.mk' Ctx.toGrpd (eqToIso rfl) (eqToIso rfl)

/-- This is the terminal or empty context. As a groupoid it has a single point
  given by ⟨⟨⟩⟩ -/
def chosenTerminal : Ctx.{u} := AsSmall.up.obj Grpd.chosenTerminal.{u}

def chosenTerminalIsTerminal : IsTerminal Ctx.chosenTerminal.{u} :=
  IsTerminal.isTerminalObj AsSmall.up.{u} Grpd.chosenTerminal
    Grpd.chosenTerminalIsTerminal
def terminalPoint : Ctx.toGrpd.obj Ctx.chosenTerminal := ⟨⟨⟩⟩


variable {Γ Δ : Ctx.{max u (v+1)}} {C D : Type (v+1)}
  [Category.{v,v+1} C] [Category.{v,v+1} D]


end Ctx

@[simps] def catLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
  obj x := Cat.of (ULift.{u + 1, u} x)
  map {x y} f := downFunctor ⋙ f ⋙ upFunctor

section yonedaCat
variable (C D) [Category.{u} C] [Category.{u} D]

abbrev yonedaCat : Cat.{u,u+1} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj
    (AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op

instance yonedaCatPreservesLimits : PreservesLimits yonedaCat :=
  comp_preservesLimits _ _

variable {Γ Δ : Ctx.{u}} {C D : Type (u+1)}
  [Category.{u,u+1} C] [Category.{u,u+1} D]

/- The bijection y(Γ) → [-,C]   ≃   Γ ⥤ C -/
def yonedaCatEquiv :
    (yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C))
      ≃ Ctx.toGrpd.obj Γ ⥤ C :=
  Equiv.trans yonedaEquiv
    {toFun     := λ A ↦ ULift.upFunctor ⋙ A
     invFun    := λ A ↦ ULift.downFunctor ⋙ A
     left_inv  := λ _ ↦ rfl
     right_inv := λ _ ↦ rfl}

lemma yonedaCatEquiv_yonedaEquivSymm {Γ : Ctx}
    (A : (yonedaCat.obj (Cat.of C)).obj (Opposite.op Γ)) :
    yonedaCatEquiv (yonedaEquiv.symm A) = upFunctor ⋙ A := by
  congr

theorem yonedaCatEquiv_naturality
    (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of C)) (σ : Δ ⟶ Γ) :
    (AsSmall.down.map σ) ⋙ yonedaCatEquiv A
      = yonedaCatEquiv (yoneda.map σ ≫ A) := by
  simp only [AsSmall.down_obj, AsSmall.down_map, yonedaCatEquiv,
    Functor.op_obj, Functor.comp_obj, Cat.of_α,
    Equiv.trans_apply, Equiv.coe_fn_mk, ← yonedaEquiv_naturality]
  rfl

theorem yonedaCatEquiv_comp
    (A : yoneda.obj Γ ⟶ yonedaCat.obj (Cat.of D)) (U : D ⥤ C) :
    yonedaCatEquiv (A ≫ yonedaCat.map U) = yonedaCatEquiv A ⋙ U := by
  aesop_cat


end yonedaCat

def Ctx.homGrpdEquivFunctor {Γ : Ctx} {G : Type v} [Groupoid.{v} G]
    : (Γ ⟶ Ctx.ofGrpd.obj (Grpd.of G))
    ≃ Ctx.toGrpd.obj Γ ⥤ G where
  toFun A := Ctx.toGrpd.map A
  invFun A := Ctx.ofGrpd.map A
  left_inv _ := rfl
  right_inv _ := rfl

def Core.functorToCoreEquiv
    {D : Type u₁} [Groupoid.{v₁} D] {C : Type u} [Category.{v} C]
    : D ⥤ Core C ≃ D ⥤ C where
  toFun A := A ⋙ Core.inclusion _
  invFun A := Core.functorToCore A
  left_inv _ := by
    apply Functor.ext
    · intro x y f
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      apply CategoryTheory.Iso.ext
      rfl
    · intro
      rfl
  right_inv _ := rfl

def functorToAsSmallEquiv {D : Type u₁} [Category.{v₁} D] {C : Type u} [Category.{v} C]
    : D ⥤ AsSmall.{w} C ≃ D ⥤ C where
  toFun A := A ⋙ AsSmall.down
  invFun A := A ⋙ AsSmall.up
  left_inv _ := rfl
  right_inv _ := rfl

def toCoreAsSmallEquiv {Γ : Ctx} {C : Type (v+1)} [Category.{v} C]
    : (Γ ⟶ Ctx.ofGrpd.obj (Grpd.of (Core (AsSmall C))))
    ≃ (Ctx.toGrpd.obj Γ ⥤ C) :=
  Ctx.homGrpdEquivFunctor.trans (
    Core.functorToCoreEquiv.trans functorToAsSmallEquiv)

abbrev Ty : Psh Ctx.{u} := yonedaCat.obj (Cat.of Grpd.{u,u})

abbrev Tm : Psh Ctx.{u} := yonedaCat.obj (Cat.of PGrpd.{u,u})

abbrev tp : Tm ⟶ Ty := yonedaCat.map (PGrpd.forgetToGrpd)

section Ty
variable {Γ : Ctx.{u}} (A : yoneda.obj Γ ⟶ Ty)

abbrev ext : Ctx := Ctx.ofGrpd.obj $ Grpd.of (Groupoidal (yonedaCatEquiv A))

abbrev disp : ext A ⟶ Γ :=
  AsSmall.up.map (Grothendieck.forget _)

abbrev var : (y(ext A) : Psh Ctx) ⟶ Tm :=
  yonedaCatEquiv.symm (Groupoidal.toPGrpd (yonedaCatEquiv A))

/-- The image of (roughly) `Groupoidal.toPGrpd : Grothendieck A ⥤ PGrpd`
  under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
  -/
abbrev yonedaCatMapToPGrpd :
    yonedaCat.obj (IsPullback.uLiftGrothendieck $
      Groupoid.compForgetToCat (yonedaCatEquiv A)) ⟶ Tm :=
  yonedaCat.map
      (Cat.homOf (ULift.downFunctor ⋙ Groupoidal.toPGrpd (yonedaCatEquiv A)))

/-- The image of (roughly) `Grothendieck.forget : Grothendieck A ⥤ Γ` under
  `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapGrothendieckForget :=
      (yonedaCat.map $ IsPullback.uLiftGrothendieckForget
        (Groupoid.compForgetToCat.{u} $ yonedaCatEquiv A))

/-- The image of `yonedaCatEquiv A` under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapYonedaCatEquiv :
    yonedaCat.obj (IsPullback.uLiftΓ.{u,u} $ Ctx.toGrpd.obj Γ) ⟶ Ty :=
  yonedaCat.map (Cat.homOf (ULift.downFunctor.{u,u} ⋙ (yonedaCatEquiv A)))

/-- The image of the pullback `Grothendieck.Groupoidal.isPullback`
  under `yonedaCat` is a pullback,
  since `yonedaCat` preserves limits -/
theorem isPullback_yonedaCatGrothendieckForget_tp :
    IsPullback
      (yonedaCatMapToPGrpd A)
      (yonedaCatMapGrothendieckForget A)
      tp
      (yonedaCatMapYonedaCatEquiv A) :=
  Functor.map_isPullback yonedaCat (Groupoidal.isPullback (yonedaCatEquiv A))

/-- This is a natural isomorphism between functors in the following diagram
  Ctx.{u}------ yoneda -----> Psh Ctx
   |                              Λ
   |                              |
   |                              |
  inclusion                 precomposition with inclusion
   |                              |
   |                              |
   |                              |
   V                              |
Cat.{big univ}-- yoneda -----> Psh Cat

-/
def asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat :
    (AsSmall.up) ⋙ (yoneda : Ctx.{u} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1))
    ≅ Grpd.forgetToCat ⋙ catLift ⋙ yonedaCat where
  hom := {app Γ := yonedaEquiv.symm (CategoryStruct.id _)}
  inv := {
    app Γ := {
      app Δ := λ F ↦
        AsSmall.up.map $ ULift.upFunctor ⋙ F ⋙ ULift.downFunctor}}

/-- `yoneda.map (disp A)` is isomorphic to `yonedaCat(uLiftGrothendieckForget _)` in
  the arrow category, hence forming a pullback square

  yoneda (ext A) ------≅----> yonedaCat(uLift (ext A))
         |                                |
         |                                |
         |                                |
         |                                |
         |                                |
         v                                v
      yoneda Γ --------≅----> yonedaCat(uLift Γ)
-/
theorem isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget :
    IsPullback
      (asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.app _)
      (yoneda.map (disp A))
      (yonedaCatMapGrothendieckForget A)
      (asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.app
        $ Ctx.toGrpd.obj Γ)
      :=
    IsPullback.of_horiz_isIso ⟨
      asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.hom.naturality
      (AsSmall.down.map (disp A))⟩

/-- The pullback required for the natural model `GroupoidNaturalModel.base`-/
theorem isPullback_yonedaDisp_tp :
    IsPullback (var A) (yoneda.map (disp A)) tp A := by
  convert IsPullback.paste_horiz
    (isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget A)
    (isPullback_yonedaCatGrothendieckForget_tp _)
  ext Δ F
  exact congr_fun (@A.naturality (Opposite.op Γ) Δ F.op) (CategoryStruct.id Γ)

end Ty

-- TODO link to this in blueprint
/-- The natural model that acts as the ambient
  model in which the other universes live.
  Note that unlike the other universes this is *not* representable,
  but enjoys having representable fibers that land in itself.
-/
def base : NaturalModelBase Ctx.{u} where
  Ty := Ty
  Tm := Tm
  tp := tp
  ext := ext
  disp := disp
  var := var
  disp_pullback := isPullback_yonedaDisp_tp


def U' : Grpd.{max u (v+1),max u (v+1)} :=
  Grpd.of (Core (AsSmall.{max u (v+1)} Grpd.{v,v}))

lemma U'_eq : U'.{v,u} =
    Core.functor.obj (Cat.asSmallFunctor.obj.{max u (v+1),v,v+1}
      (Cat.of Grpd.{v,v})) :=
  rfl

/-- `U.{v}` is the object representing the
  universe of `v`-small types
  i.e. `y(U) = Ty` for the small natural models `baseU`. -/
def U : Ctx.{max u (v+1)} :=
  Ctx.ofGrpd.obj U'.{v,u}

def E' : Grpd.{max u (v+1),max u (v+1)} :=
  Grpd.of (Core (AsSmall.{max u (v+1)} PGrpd.{v,v}))

lemma E'_eq : E'.{v,u} =
    Core.functor.obj.{max u (v+1), max u (v+1)}
      (Cat.asSmallFunctor.obj.{max u (v+1),v,v+1} (Cat.of PGrpd.{v,v})) :=
  rfl

/-- `E.{v}` is the object representing `v`-small terms,
  living over `U.{v}`
  i.e. `y(E) = Tm` for the small natural models `baseU`. -/
def E : Ctx.{max u (v + 1)} :=
  Ctx.ofGrpd.obj E'.{v,u}

def π'' : AsSmall.{max u (v+1)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+1)} Grpd.{v,v} :=
  AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up

abbrev π' : E'.{v,u} ⟶ U'.{v,u} :=
  Grpd.homOf (Core.functor' π'')

lemma π'_eq : Grpd.homOf (Core.functor' π'') =
    Core.functor.map (Cat.asSmallFunctor.map (Cat.homOf PGrpd.forgetToGrpd)) :=
  rfl

/-- `π.{v}` is the morphism representing `v`-small `tp`,
  for the small natural models `baseU`. -/
abbrev π : E.{v,u} ⟶ U.{v,u} :=
  Ctx.ofGrpd.map π'

open PGrpd LargeUniverse

-- FIXME this has an error without the `dsimp` saying it has
-- two non-defeq category instances
def U.isoYonedaCatGrpd : y(U.{v,u}) ≅ yonedaCat.obj (coregrpd.{v,max u (v+1)}) :=
  asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.app U'.{v,u}
    ≪≫ Functor.mapIso yonedaCat (by
      dsimp [Grpd.forgetToCat, U, U']
      exact ULift.Core.isoCoreULift)

-- FIXME this has an error without the `dsimp` saying it has
-- two non-defeq category instances
def U.isoYonedaCatPGrpd : y(E.{v,u}) ≅ yonedaCat.obj (corepgrpd.{v,max u (v+1)}) :=
  asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.app E'.{v,u}
    ≪≫ Functor.mapIso yonedaCat (by
      dsimp [Grpd.forgetToCat, E, E']
      exact ULift.Core.isoCoreULift)

/-- `toTy` is the map that classifies the universe
  `U` of `v`-small types as a map into the type classifier `Ty`.
  This will fit into the pullback square

    E --------toTm---> Tm
    |                   |
    |                   |
    |                   |
    |                   |
    v                   v
    U---------toTy----->Ty

-/
def U.toTy : y(U.{v,u}) ⟶ Ty.{max u (v+1)} :=
  isoYonedaCatGrpd.hom.{v,u}
  ≫ yonedaCat.map inclusionGrpdCompAsSmallFunctor.{v,max u (v+1)}

def U.toTm : y(E.{v,u}) ⟶ Tm.{max u (v+1)} :=
  isoYonedaCatPGrpd.hom.{v,u}
  ≫ yonedaCat.map inclusionPGrpdCompAsSmallFunctor.{v,max u (v+1)}

namespace U

/--
The image of `isPullback_corepgrpdforgettogrpd_PGRPDFORGETTOGRPD`
under `yonedaCat` is a pullback

yonedaCat (Core PGrpd.{v,v}) ----> yonedaCat (PGrpd.{max v u, max v u}) = Tm
        |                                     |
        |                                     |
        |                                     tp
        |                                     |
        v                                     v
yonedaCat (Core Grpd.{v,v})  ----> yonedaCat (Grpd.{max v u, max v u}) = Ty
-/
theorem isPullback_yonedaCatCorePGrpdForgetToGrpd_tp :
    IsPullback
      (yonedaCat.map (inclusionPGrpdCompAsSmallFunctor.{v,u}))
      (yonedaCat.map (coreFunctorPGrpdForgetToGrpd.{v,u}))
      tp
      (yonedaCat.map (inclusionGrpdCompAsSmallFunctor.{v,u})) :=
  Functor.map_isPullback yonedaCat (isPullback_corepgrpdforgettogrpd_PGRPDFORGETTOGRPD)

theorem isPullback_yπ_yonedaCatCorepgrpdforgettogrpd :
    IsPullback
      U.isoYonedaCatPGrpd.{v,u}.hom
      ym(π.{v,u})
      (yonedaCat.map (corepgrpdforgettogrpd.{v,max u (v+1)}))
      U.isoYonedaCatGrpd.{v,u}.hom :=
  IsPullback.of_horiz_isIso ⟨rfl⟩

/--
The small universe and the ambient natural model form a pullback
      y(E) ------------ toTm --------------> Tm
        |                                     |
        |                                     |
      y(π)                                    tp
        |                                     |
        v                                     v
      y(U) ------------ toTy --------------> Ty
-/
theorem isPullback_yπ_tp :
    IsPullback toTm.{v,u} ym(π.{v,u}) tp toTy.{v,u} :=
  IsPullback.paste_horiz
    isPullback_yπ_yonedaCatCorepgrpdforgettogrpd
    isPullback_yonedaCatCorePGrpdForgetToGrpd_tp.{v,max u (v+1)}

variable {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v})

def classifier : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v} :=
  Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd) ⋙ AsSmall.down

abbrev ext' : Grpd.{max u (v+1), max u (v+1)}:=
  Grpd.of (Groupoidal (classifier A))

abbrev ext : Ctx.{max u (v + 1)} :=
  Ctx.ofGrpd.obj (ext' A)

abbrev disp' : ext' A ⟶ Ctx.toGrpd.obj Γ :=
  Grothendieck.forget _

abbrev disp : ext A ⟶ Γ :=
  AsSmall.up.map (Grothendieck.forget _)

abbrev var' : ext' A ⟶ E'.{v} :=
  Grpd.homOf (Core.functorToCore
    (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up))

abbrev var : ext A ⟶ E.{v} :=
  Ctx.ofGrpd.map (Grpd.homOf (Core.functorToCore
    (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up)))

def toU'' : AsSmall.{max u (v+2)} Grpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} Grpd.{v+1,v+1} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def toU' : U'.{v, max u (v+2)} ⟶ U'.{v+1,max u (v+2)} :=
  Core.functor.map (Cat.homOf toU'')

/-- `toU` is the base map between two `v`-small universes
    E.{v} --------------> E.{v+1}
    |                      |
    |                      |
    |                      |
    |                      |
    v                      v
    U.{v}-------toU-----> U.{v+1}
 -/
def toU : U.{v, max u (v+2)} ⟶ U.{v+1, max u (v+2)} :=
  Ctx.ofGrpd.map toU'

def toE'' : AsSmall.{max u (v+2)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} PGrpd.{v+1,v+1} :=
  AsSmall.down ⋙ PGrpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def toE' : E'.{v, max u (v+2)} ⟶ E'.{v+1,max u (v+2)} :=
  Core.functor.map $ Cat.homOf toE''

def toE : E.{v, max u (v+2)} ⟶ E.{v+1,max u (v+2)} :=
  Ctx.ofGrpd.map toE'

namespace SmallUniverse

theorem comm_sq : Cat.homOf toE''.{v,u} ≫ Cat.homOf π''.{v+1, max u (v+2)} =
  Cat.homOf π''.{v, max u (v+2)} ≫ Cat.homOf toU''.{v,u} := rfl

def toE''' : AsSmall.{v+1} PGrpd.{v,v}
    ⥤ PGrpd.{v+1,v+1} :=
  AsSmall.down ⋙ PGrpd.asSmallFunctor.{v+1}

def toU''' : AsSmall.{v+1} Grpd.{v,v}
    ⥤ Grpd.{v+1,v+1} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1}

open Grothendieck.Groupoidal

theorem isPullback_uLiftGrothendieckForget_forgetToGrpd :
    IsPullback
      (Cat.homOf (ULift.downFunctor ⋙ toPGrpd toU'''.{v}))
      (IsPullback.uLiftGrothendieckForget (Groupoid.compForgetToCat toU'''))
      (Cat.homOf PGrpd.forgetToGrpd.{v+1,v+1})
      (Cat.homOf (ULift.downFunctor.{v+1,v+1} ⋙ toU'''.{v})) :=
  Grothendieck.Groupoidal.isPullback _


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

theorem uniq' (m : s.pt ⟶ Cat.of (AsSmall PGrpd))
    (hl : m ≫ Cat.homOf toE'' = s.fst)
    (hr : m ≫ Cat.homOf π''.{_,max u (v+2)} = s.snd) :
    m = lift' s := by
  have hl' : (m ⋙ AsSmall.down) ⋙ asSmallFunctor.{v+1}
    = s.fst ⋙ AsSmall.down := by rw [← hl]; rfl
  have hr' : (m ⋙ AsSmall.down) ⋙ forgetToGrpd.{v}
    = snd' s := by dsimp [snd']; rw [← hr]; rfl
  apply AsSmall.comp_down_inj 
  exact uniq.{v+1} _ _ (condition' s) _ hl' hr'

end IsPullbackInCat

/--
The following square is a pullback

 AsSmall PGrpd.{v} ------- toE'' ------> AsSmall PGrpd.{v+1}
        |                                     |
        |                                     |
        π'                                    π'
        |                                     |
        |                                     |
        v                                     v
 AsSmall Grpd.{v}  ------- toU'' -----> AsSmall Grpd.{v+1}

in the category `Cat.{max u (v+2), max u (v+2)}`.
Note that these `AsSmall`s are bringing two different sizes
categories into the same category.
We prove this is pullback by using the fact that this `IsMegaPullback`,
i.e. it is universal among categories of all sizes.
-/
theorem isPullback_pgrpdforgettogrpd_pgrpdforgettogrpd :
    IsPullback
      (Cat.homOf toE''.{v,max u (v+2)})
      (Cat.homOf π''.{_,max u (v+2)})
      (Cat.homOf π''.{v+1,max u (v+2)})
      (Cat.homOf toU''.{v,max u (v+2)}) :=
  IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk
      comm_sq lift' fac_left' fac_right' uniq')

/--
The following square is a pullback

 E'.{v,max u (v+2)} ------- toE' ------> E'.{v+1,u}
        |                                     |
        |                                     |
        π'                                    π'
        |                                     |
        v                                     v
 U'.{v,max u (v+2)}  ------- toU' -----> U'.{v+1,u}

in the category `Grpd.{max u (v+2), max u (v+2)}`.
This is because `Core.functor` is a right adjoint,
hence preserves limits.
-/
theorem isPullback_π'_π' :
    IsPullback
      toE'.{v,max u (v+2)}
      π'.{v}
      π'.{v+1}
      toU'.{v,max u (v+2)} :=
  Functor.map_isPullback Core.functor
    isPullback_pgrpdforgettogrpd_pgrpdforgettogrpd

end SmallUniverse

variable {Γ : Ctx.{max u (v+2)}} (A : y(Γ) ⟶ y(U.{v,max u (v+2)}))

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
      SmallUniverse.isPullback_π'_π')

section disp_pullback

variable (Γ : Ctx.{max u (v+1)})

abbrev coreΓ : Grpd.{max u (v+1), max u (v+1)} :=
  Core.functor.obj (Cat.of (Ctx.toGrpd.obj Γ))

variable {Γ} (A : Γ ⟶ U.{v})

abbrev coreExt' : Grpd.{max u (v+1), max u (v+1)}:=
  Core.functor.obj (Cat.of (Groupoidal (classifier A)))

abbrev coreDisp' : coreExt' A ⟶ coreΓ.{v,u} Γ :=
  Core.functor.map $ Cat.homOf $ Grothendieck.forget _

abbrev coreVar' : coreExt' A ⟶
    Core.functor.obj.{max u (v+1), max u (v+1)}
      (Cat.asSmallFunctor.obj.{max u (v+1),v,v+1} (Cat.of PGrpd.{v,v})) :=
  Core.functor.map $ Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up)

abbrev coreA : coreΓ.{v,u} Γ ⟶
    Core.functor.obj.{max u (v+1), max u (v+1)}
      (Cat.asSmallFunctor.obj.{max u (v+1),v,v+1} (Cat.of Grpd.{v,v})) :=
  Core.functor.map (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)))

def isPullback_disp'_asSmallForgetToGrpd_comm_sq :
    Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up)
    ≫ Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd))
    = Cat.homOf (Grothendieck.forget (Groupoid.compForgetToCat (classifier A)))
    ≫ Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)) := rfl

variable {A}
def comm_sq (s : PullbackCone
      (Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd)))
    (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)))) :
    s.fst ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd = s.snd ⋙ classifier A := by
  convert_to s.fst ⋙ AsSmall.down ⋙ forgetToGrpd
    ⋙ AsSmall.up ⋙ AsSmall.down.{v, v + 1, max u (v + 1)} = _
  have := s.condition
  simp only [Cat.asSmallFunctor_obj, Cat.of_α, Cat.homOf, Cat.asSmallFunctor_map, ← Functor.assoc,
    PullbackCone.π_app_left, Cat.comp_eq_comp, PullbackCone.π_app_right, classifier] at *
  rw [this]

def lift (s : PullbackCone
      (Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd)))
    (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)))) :
    s.pt ⟶ Cat.of (Groupoidal (classifier A)) :=
  Groupoidal.IsMegaPullback.lift (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)

theorem fac_left (s : PullbackCone (Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd)))
        (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)))) :
    lift s ≫ Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up) = s.fst := by
  convert_to _ = s.fst ⋙ AsSmall.down.{_, _, max u (v+1)} ⋙ AsSmall.up
  simp only [← Functor.assoc]
  rw [← Groupoidal.IsMegaPullback.fac_left (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)]
  rfl

theorem fac_right (s : PullbackCone
      (Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd)))
    (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)))) :
    lift s ≫ Cat.homOf (Grothendieck.forget (Groupoid.compForgetToCat (classifier A))) = s.snd :=
  Groupoidal.IsMegaPullback.fac_right (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)

theorem uniq (s : PullbackCone
      (Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd)))
    (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd))))
    (m : s.pt ⟶ Cat.of (Grothendieck (Groupoid.compForgetToCat (classifier A))))
    (hl : m ≫ Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up) = s.fst)
    (hr : m ≫ Cat.homOf (Grothendieck.forget (Groupoid.compForgetToCat (classifier A)))
      = s.snd) : m = lift s := by
  apply Groupoidal.IsMegaPullback.uniq
  · rw [← hl] ; rfl
  · rw [← hr] ; rfl

theorem isPullback_disp'_asSmallForgetToGrpd :
    IsPullback
      (Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up))
      (Cat.homOf (Grothendieck.forget (Groupoid.compForgetToCat (classifier A))))
      (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd))
      (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd))) :=
  IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk
      (isPullback_disp'_asSmallForgetToGrpd_comm_sq A)
      lift fac_left fac_right uniq)

variable (A)

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
    (U.coreVar' A)
    (U.coreDisp' A)
    π'
    (coreA A) :=
  Functor.map_isPullback Core.functor isPullback_disp'_asSmallForgetToGrpd

-- /--
--   The following square is a pullback in `Grpd`
-- Core(U.ext' A) ------- inclusion ---> U.ext' A
--      |                                     |
--      |                                     |
--      |                                     |
-- Core(U.disp' A)                            π'
--      |                                     |
--      |                                     |
--      V                                     V
-- Core(Ctx.toGrpd.obj Γ) - inclusion -> Ctx.toGrpd.obj Γ
-- -/
-- theorem isPullback_coreDisp'_disp' :
--   IsPullback
--     (Grpd.homOf (Core.inclusion _))
--     (U.coreDisp' A)
--     (U.disp' A)
--     (Grpd.homOf (Core.inclusion _)) :=
--   IsPullback.of_horiz_isIso ⟨ rfl ⟩

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
    (U.disp' A)
    (U.coreDisp' A)
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
    (U.var' A)
    (U.disp' A)
    π'
    (Ctx.toGrpd.map A) := by
  convert IsPullback.paste_horiz (isPullback_disp'_coreDisp' A) (isPullback_coreDisp'_π' A)
  convert_to Ctx.toGrpd.map A =
    Grpd.homOf (Core.functorToCore (𝟭 ↑Γ.1)) ≫
      Core.functor.map (Cat.homOf (Ctx.toGrpd.map A)) ≫ Core.functor.map (Cat.homOf (Core.inclusion (AsSmall Grpd)))
  have h := Core.adjunction.unit.naturality (Ctx.toGrpd.map A)
  simp only [Ctx.toGrpd, AsSmall.down_obj, Grpd.forgetToCat,
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
  Functor.map_isPullback Ctx.ofGrpd (U.isPullback_disp'_π' A)

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
  Functor.map_isPullback yoneda (U.isPullback_disp_π A)

end disp_pullback
end U

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that unlike `GroupoidNaturalModel.base` this is representable,
  but since representables are `max u (v+1)`-large,
  its representable fibers can be larger than itself.

  This natural model is given by pullback of the natural model `base`.
  TODO However, we likely want to use the explicit `Tm = y(E)` and
  `tp = ym(π)` instead of the grothendieck construction provided.
-/
def smallU : NaturalModelBase Ctx.{max u (v+1)} where
  Ty := y(U.{v})
  Tm := y(E)
  tp := ym(π)
  ext A := U.ext (yoneda.preimage A)
  disp A := U.disp (yoneda.preimage A)
  var A := ym(U.var (yoneda.preimage A))
  disp_pullback A := by
    convert U.isPullback_yonedaDisp_yonedaπ (yoneda.preimage A)
    rw [Functor.map_preimage]

def U.asSmallClosedType' : Ctx.chosenTerminal.{max u (v+2)}
    ⟶ U.{v+1, max u (v+2)} :=
  toCoreAsSmallEquiv.symm ((Functor.const _).obj
    (Grpd.of (Core (AsSmall.{v+1} Grpd.{v,v}))))

def U.asSmallClosedType : y(Ctx.chosenTerminal.{max u (v+2)})
    ⟶ smallU.{v+1, max u (v+2)}.Ty :=
  ym(U.asSmallClosedType')

def U.isoGrpd :
    Core (AsSmall.{max u (v+2)} Grpd.{v,v})
      ⥤ Grpd.{v,v} := Core.inclusion _ ⋙ AsSmall.down

def U.isoExtAsSmallClosedTypeHom :
    Core (AsSmall.{max u (v+2)} Grpd.{v,v})
      ⥤ Groupoidal
        (classifier (asSmallClosedType'.{v, max u (v + 2)})) where
  obj X := ⟨ ⟨⟨⟩⟩ , AsSmall.up.obj.{_,_,v+1} (AsSmall.down.obj X) ⟩
  map {X Y} F := ⟨ (CategoryStruct.id _) , {
    hom := AsSmall.up.map.{_,_,v+1} (AsSmall.down.map F.hom)
    inv := AsSmall.up.map.{_,_,v+1} (AsSmall.down.map (F.inv))
    hom_inv_id := by
      simp only [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
      rfl
    inv_hom_id := by
      simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id] } ⟩

def U.isoExtAsSmallClosedTypeInv :
    Groupoidal
      (classifier (asSmallClosedType'.{v, max u (v + 2)})) ⥤
    Core (AsSmall.{max u (v+2)} Grpd.{v,v}) where
  obj X := AsSmall.up.obj (AsSmall.down.obj.{_,_,v+1} X.fiber)
  map {X Y} F := {
    hom := AsSmall.up.map.{_,_,max u (v+2)} (AsSmall.down.map F.fiber.hom)
    inv := AsSmall.up.map.{_,_,max u (v+2)} (AsSmall.down.map F.fiber.inv)
    hom_inv_id := by simp only [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
    inv_hom_id := by simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id] }

def U.isoExtAsSmallClosedType :
    U.{v,max u (v+2)}
    ≅ smallU.{v+1,max u (v+2)}.ext U.asSmallClosedType.{v, max u (v+2)} where
  hom := Ctx.ofGrpd.map (Grpd.homOf isoExtAsSmallClosedTypeHom.{v,u})
    ≫ eqToHom (by simp only [smallU, asSmallClosedType, preimage_map])
  inv := eqToHom (by simp only [smallU, asSmallClosedType, preimage_map])
    ≫ Ctx.ofGrpd.map (Grpd.homOf isoExtAsSmallClosedTypeInv.{v,u})
  hom_inv_id := by
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl]
    rfl
  inv_hom_id := by
    simp only [Category.assoc, eqToHom_comp_iff, Category.comp_id]
    simp only [← Category.assoc, comp_eqToHom_iff, eqToHom_trans]
    rfl

def smallUHom : UHom smallU.{v, max u (v+2)} smallU.{v+1, max u (v+2)} :=
  UHom.ofRepChosenTerminal Ctx.chosenTerminalIsTerminal $
    @UHomRepTerminal.ofTyIsoExt _ _ _ _ _ _
    { mapTy := ym(U.toU.{v,max u (v+2)})
      mapTm := ym(U.toE)
      pb := U.isPullback_yπ_yπ }
    U.asSmallClosedType
    (Functor.mapIso yoneda U.isoExtAsSmallClosedType.{v,u})

def U.asClosedType :
    yoneda.obj Ctx.chosenTerminal ⟶ base.Ty :=
  yonedaCatEquiv.invFun ((CategoryTheory.Functor.const _).obj
    (Grpd.of U'.{v,u}))

def U.isoExtAsClosedTypeFun : Core (AsSmall Grpd)
    ⥤ Groupoidal (yonedaCatEquiv U.asClosedType.{v,u}) where
  obj X := ⟨ ⟨⟨⟩⟩ , X ⟩
  map {X Y} F := ⟨ id _ , F ⟩

def U.isoExtAsClosedTypeInv : Groupoidal (yonedaCatEquiv U.asClosedType.{v,u})
    ⥤ Core (AsSmall Grpd) where
  obj X := X.fiber
  map {X Y} F := F.fiber

def U.isoExtAsClosedType :
    U.{v,u} ≅ base.ext asClosedType.{v,u} where
  hom := Ctx.ofGrpd.map isoExtAsClosedTypeFun
  inv := Ctx.ofGrpd.map isoExtAsClosedTypeInv

def largeUHom : UHom smallU.{v,u} base :=
  UHom.ofRepChosenTerminal Ctx.chosenTerminalIsTerminal $
    UHomRepTerminal.ofTyIsoExt _
    { mapTy := U.toTy
      mapTm := U.toTm
      pb := U.isPullback_yπ_tp }
    (Functor.mapIso yoneda U.isoExtAsClosedType)

def uHomSeqObjs (i : Nat) (h : i < 4) : NaturalModelBase Ctx.{3} :=
  match i with
  | 0 => smallU.{0,3}
  | 1 => smallU.{1,3}
  | 2 => smallU.{2,3}
  | 3 => base.{3}
  | (n+4) => by omega

def uHomSeqHomSucc' (i : Nat) (h : i < 3) :
    (uHomSeqObjs i (by omega)).UHom (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => smallUHom.{0,3}
  | 1 => smallUHom.{1,3}
  | 2 => largeUHom.{2,3}
  | (n+3) => by omega

/--
  The groupoid natural model with two nested representable universes
-/
def uHomSeq : NaturalModelBase.UHomSeq Ctx.{3} where
  length := 3
  objs := uHomSeqObjs
  homSucc' := uHomSeqHomSucc'

end GroupoidNaturalModel

end CategoryTheory

end
