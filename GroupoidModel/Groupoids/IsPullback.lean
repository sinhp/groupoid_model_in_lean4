import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat

import GroupoidModel.Russell_PER_MS.NaturalModelBase
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal
import GroupoidModel.Groupoids.Basic

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory ULift Grothendieck
  Limits NaturalModelBase CategoryTheory.Functor

namespace GroupoidModel
namespace IsPullback

def groupoidalAsSmallFunctorToPGrpd :
    Groupoidal (Grpd.asSmallFunctor.{max w (v+1), v, v})
    ⥤ PGrpd.{v,v} where
  obj x := PGrpd.fromGrpd x.base
    (AsSmall.down.obj.{v, v, max w (v + 1)} x.fiber)
  map f := {
    toFunctor := f.base
    point := AsSmall.down.map f.fiber}
  map_id := sorry
  map_comp := sorry

def pGrpdToGroupoidalAsSmallFunctor : PGrpd.{v, v} ⥤
    Groupoidal (Grpd.asSmallFunctor.{max w (v+1), v, v}) where
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

def lift_uniq (m : C ⥤ PGrpd.{v,v})
    (hl : m ⋙ PGrpd.asSmallFunctor.{max w (v+1)} = fst)
    (hr : m ⋙ PGrpd.forgetToGrpd.{v} = snd) :
    m = lift fst snd condition := by
  unfold lift
  convert_to (m ⋙ pGrpdToGroupoidalAsSmallFunctor.{max w (v+1)})
    ⋙ groupoidalAsSmallFunctorToPGrpd = _
  rw [Groupoidal.IsMegaPullback.lift_uniq fst snd condition
    (m ⋙ pGrpdToGroupoidalAsSmallFunctor.{max w (v+1)}) hl hr]

end PGrpd.IsMegaPullback'

namespace LargeUHom

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
  Cat.ofULift.{max u (v+1) + 1} (AsSmall.{u} Grpd.{v,v})
def pgrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.ofULift.{max u (v+1) + 1} (AsSmall.{u} PGrpd.{v,v})
def coregrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of $ Core $ ULift.{max u (v+1) + 1} (AsSmall.{u} Grpd.{v,v})
def corepgrpd : Cat.{max u (v+1), max u (v+1) + 1} :=
  Cat.of $ Core $ ULift.{max u (v+1) + 1} (AsSmall.{u} PGrpd.{v,v})

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
  Cat.homOf $ Core.map' $
    downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor

def coreFunctorPGrpdForgetToGrpd : corepgrpd.{v,u} ⟶ coregrpd.{v,u} :=
  Cat.homOf (Core.map.map pgrpdforgettogrpd)

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

def yUIsoYonedaCatGrpd : y(U.{v,u})
    ≅ yonedaCat.obj (coregrpd.{v,max u (v+1)}) :=
  asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.app
    U'.{v,u} ≪≫ Functor.mapIso yonedaCat (eqToIso (by rfl)
      ≪≫ ULift.Core.isoCoreULift)

def yEIsoYonedaCatPGrpd : y(E.{v,u})
    ≅ yonedaCat.obj (corepgrpd.{v,max u (v+1)}) :=
  asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat.app
    E'.{v,u} ≪≫ Functor.mapIso yonedaCat (eqToIso (by rfl)
      ≪≫ ULift.Core.isoCoreULift)

namespace IsPullback

theorem comm_sq :
    pgrpdassmallfunctor.{v,u}
    ≫ PGRPDFORGETTOGRPD.{v,u}
    = pgrpdforgettogrpd.{v,u}
    ≫ grpdassmallfunctor.{v,u} :=
  rfl

variable (s : PullbackCone PGRPDFORGETTOGRPD.{v,u} grpdassmallfunctor.{v,u})

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
theorem isPullback_pgrpdforgettogrpd_PGRPDFORGETTOGRPD :
    IsPullback
      pgrpdassmallfunctor.{v,u}
      pgrpdforgettogrpd.{v,u}
      PGRPDFORGETTOGRPD.{v,u}
      grpdassmallfunctor.{v,u} :=
  IsPullback.of_isLimit $
  PullbackCone.IsLimit.mk
    IsPullback.comm_sq
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
      rw [IsMegaPullback'.lift_uniq s.fst (snd s) (condition s)
        (m ⋙ ULift.downFunctor ⋙ AsSmall.down)
        hl (by simp only [snd, ← hr]; rfl)]
      rfl)

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
    (Core.isPullback_map'_self pgrpdforgettogrpd.{v,u})
    (isPullback_pgrpdforgettogrpd_PGRPDFORGETTOGRPD.{v,u})

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
      yEIsoYonedaCatPGrpd.{v,u}.hom
      ym(π.{v,u})
      (yonedaCat.map (corepgrpdforgettogrpd.{v,max u (v+1)}))
      yUIsoYonedaCatGrpd.{v,u}.hom :=
  IsPullback.of_horiz_isIso ⟨rfl⟩

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
def toTy : y(U.{v,u}) ⟶ Ty.{max u (v+1)} :=
  yUIsoYonedaCatGrpd.hom.{v,u}
  ≫ yonedaCat.map inclusionGrpdCompAsSmallFunctor.{v,max u (v+1)}

def toTm : y(E.{v,u}) ⟶ Tm.{max u (v+1)} :=
  yEIsoYonedaCatPGrpd.hom.{v,u}
  ≫ yonedaCat.map inclusionPGrpdCompAsSmallFunctor.{v,max u (v+1)}

/--
The small universe and the ambient natural model form a pullback
      y(E) ------------ toTm --------------> Tm
        |                                     |
        |                                     |
     ym(π)                                    tp
        |                                     |
        v                                     v
      y(U) ------------ toTy --------------> Ty
-/
theorem isPullback_yπ_tp :
    IsPullback toTm.{v,u} ym(π.{v,u}) tp toTy.{v,u} :=
  IsPullback.paste_horiz
    isPullback_yπ_yonedaCatCorepgrpdforgettogrpd
    isPullback_yonedaCatCorePGrpdForgetToGrpd_tp.{v,max u (v+1)}

end LargeUHom

namespace Base
variable {Γ : Ctx.{u}} (A : yoneda.obj Γ ⟶ Ty)

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
    yonedaCat.obj (Cat.ofULift.{u+1} $ Ctx.toGrpd.obj Γ) ⟶ Ty :=
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

/-- The pullback square required for `GroupoidNaturalModel.base`

                  var A
  yoneda (ext A) ----------> Ty
         |                   |
         |                   |
         |                   tp
  yoneda(disp A)             |
         |                   |
         |                   |
         v                   v
      yoneda Γ ------------> Tm
                     A
-/
theorem isPullback_yonedaDisp_tp :
    IsPullback (var A) (yoneda.map (disp A)) tp A := by
  convert IsPullback.paste_horiz
    (isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget A)
    (isPullback_yonedaCatGrothendieckForget_tp _)
  ext Δ F
  exact congr_fun (@A.naturality (Opposite.op Γ) Δ F.op) (CategoryStruct.id Γ)

end Base

namespace SmallUHom

variable {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v})

def toU'' : AsSmall.{max u (v+2)} Grpd.{v,v}
    ⥤ AsSmall.{max u (v+2)} Grpd.{v+1,v+1} :=
  AsSmall.down ⋙ Grpd.asSmallFunctor.{v+1} ⋙ AsSmall.up

def toU' : U'.{v, max u (v+2)} ⟶ U'.{v+1,max u (v+2)} :=
  Core.map.map (Cat.homOf toU'')

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
  Core.map.map $ Cat.homOf toE''

def toE : E.{v, max u (v+2)} ⟶ E.{v+1,max u (v+2)} :=
  Ctx.ofGrpd.map toE'

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
This is because `Core.map` is a right adjoint,
hence preserves limits.
-/
theorem isPullback_π'_π' :
    IsPullback
      toE'.{v,max u (v+2)}
      π'.{v}
      π'.{v+1}
      toU'.{v,max u (v+2)} :=
  Functor.map_isPullback Core.map
    isPullback_π''_π''

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
      isPullback_π'_π')
end SmallUHom

namespace SmallBase

open U PGrpd

abbrev coreΓ (Γ : Ctx.{max u (v+1)}) : Grpd.{max u (v+1), max u (v+1)} :=
  Core.map.obj (Cat.of (Ctx.toGrpd.obj Γ))

variable {Γ : Ctx.{max u (v+1)}} (A : Γ ⟶ U.{v})

abbrev coreExt' : Grpd.{max u (v+1), max u (v+1)}:=
  Core.map.obj (Cat.of (Groupoidal (classifier A)))

abbrev coreDisp' : coreExt' A ⟶ coreΓ.{v,u} Γ :=
  Core.map.map $ Cat.homOf $ Grothendieck.forget _

abbrev coreVar' : coreExt' A ⟶
    Core.map.obj.{max u (v+1), max u (v+1)}
      (Cat.asSmallFunctor.obj.{max u (v+1),v,v+1} (Cat.of PGrpd.{v,v})) :=
  Core.map.map $ Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up)

abbrev coreA : coreΓ.{v,u} Γ ⟶
    Core.map.obj.{max u (v+1), max u (v+1)}
      (Cat.asSmallFunctor.obj.{max u (v+1),v,v+1} (Cat.of Grpd.{v,v})) :=
  Core.map.map (Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)))

def isPullback_disp'_asSmallForgetToGrpd_comm_sq :
    Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up)
    ≫ Cat.homOf (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd))
    = Cat.homOf (Grothendieck.forget (Groupoid.compForgetToCat (classifier A)))
    ≫ Cat.homOf (Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd)) := rfl

variable {Γ : Ctx.{max u (v+1)}} (A : Γ ⟶ U.{v})

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
  rw [this]

def lift : s.pt ⟶ Cat.of (Groupoidal (classifier A)) :=
  Groupoidal.IsMegaPullback.lift
    (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)

@[simp] theorem fac_left : lift s
    ≫ Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up)
    = s.fst := by
  convert_to _ = s.fst ⋙ AsSmall.down.{_, _, max u (v+1)}
    ⋙ AsSmall.up
  simp only [← Functor.assoc]
  rw [← Groupoidal.IsMegaPullback.fac_left
    (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)]
  rfl

@[simp] theorem fac_right : lift s
    ≫ Cat.homOf (Grothendieck.forget
      (Groupoid.compForgetToCat (classifier A)))
    = s.snd :=
  Groupoidal.IsMegaPullback.fac_right
    (s.fst ⋙ AsSmall.down) s.snd (comm_sq s)

theorem lift_uniq
    (m : s.pt ⟶ Cat.of (Grothendieck
      (Groupoid.compForgetToCat (classifier A))))
    (hl : m ≫ Cat.homOf (Groupoidal.toPGrpd
      (classifier A) ⋙ AsSmall.up)
      = s.fst)
    (hr : m ≫ Cat.homOf (Grothendieck.forget
      (Groupoid.compForgetToCat (classifier A)))
      = s.snd) : m = lift s := by
  apply Groupoidal.IsMegaPullback.lift_uniq
  · rw [← hl] ; rfl
  · rw [← hr] ; rfl

theorem isPullback_disp'_asSmallForgetToGrpd :
    IsPullback
      (Cat.homOf (Groupoidal.toPGrpd (classifier A) ⋙ AsSmall.up))
      (Cat.homOf (Grothendieck.forget
        (Groupoid.compForgetToCat (classifier A))))
      (Cat.asSmallFunctor.map (Cat.homOf forgetToGrpd))
      (Cat.homOf (Ctx.toGrpd.map A ⋙
        Core.inclusion (AsSmall Grpd))) :=
  IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk
      (isPullback_disp'_asSmallForgetToGrpd_comm_sq A)
      lift fac_left fac_right lift_uniq)

end IsPullback

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
    π'
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
    (var' A)
    (disp' A)
    π'
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
