import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Functor.ReflectsIso

import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal


/-!
Here we construct the natural model for groupoids.
-/

universe w v u v₁ u₁ v₂ u₂

noncomputable section
open CategoryTheory ULift Grothendieck


namespace CategoryTheory

namespace IsPullback
variable {C : Type u₁} [Category.{v₁} C]

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Construct an `IsPullback` from an `IsPullback`
  and an isomorphism with the tip of the cone -/
theorem of_iso_isPullback (h : IsPullback fst snd f g) {Q} (i : Q ≅ P) :
      IsPullback (i.hom ≫ fst) (i.hom ≫ snd) f g := sorry

end IsPullback

namespace ULift

variable (C : Type u₁) [Category.{v₁} C]

def iso_self : Cat.of (ULift.{u₁} C) ≅ Cat.of C where
  hom := ULift.downFunctor
  inv := ULift.upFunctor

end ULift

instance Groupoid.asSmall (Γ : Type w) [Groupoid.{v} Γ] :
    Groupoid (AsSmall.{max w u v} Γ) where
  inv f := AsSmall.up.map (inv (AsSmall.down.map f))

def Grpd.asSmallFunctor : Grpd.{v, u} ⥤ Grpd.{max w v u, max w v u} where
  obj Γ := Grpd.of $ AsSmall.{max w v u} Γ
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

namespace PGrpd

instance asSmallPointedGroupoid (Γ : Type w) [PointedGroupoid.{v} Γ] :
    PointedGroupoid.{max w v u, max w v u} (AsSmall.{max w v u} Γ) := {
  Groupoid.asSmall.{w,v,u} Γ with
  pt := AsSmall.up.obj PointedGroupoid.pt}

def asSmallFunctor : PGrpd.{v, u} ⥤ PGrpd.{max w v u, max w v u} where
  obj Γ := PGrpd.of $ AsSmall.{max w v u} Γ
  map F := {
    toFunctor := AsSmall.down ⋙ F.toFunctor ⋙ AsSmall.up
    point := AsSmall.up.map F.point}


end PGrpd

namespace Core

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

@[simp]
theorem id_inv (X : C) :
    Iso.inv (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl

@[simp]
theorem comp_inv {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).inv = g.inv ≫ f.inv :=
  rfl

def functor' (F : C ⥤ D) : Core C ⥤ Core D where
  obj := F.obj
  map f := {
    hom := F.map f.hom
    inv := F.map f.inv}
  map_id x := by
    simp only [Grpd.coe_of, id_hom, Functor.map_id, id_inv]
    congr 1
  map_comp f g := by
    simp only [Grpd.coe_of, comp_hom, Functor.map_comp, comp_inv]
    congr 1

lemma functor'_comp_inclusion (F : C ⥤ D) :
    functor' F ⋙ inclusion D = inclusion C ⋙ F :=
  rfl

def functor : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := Grpd.homOf (functor' F)

variable {Γ : Type u} [Groupoid.{v} Γ]

/-  A functor from a groupoid into a category is equivalent
    to a functor from the groupoid into the core -/
def functorToCoreEquiv : Γ ⥤ D ≃ Γ ⥤ Core D where
  toFun := functorToCore
  invFun := forgetFunctorToCore.obj
  left_inv _ := rfl
  right_inv _ := by
    simp [functorToCore, forgetFunctorToCore]
    apply Functor.ext
    · intro x y f
      simp only [inclusion, id_eq, Functor.comp_obj, Functor.comp_map,
        IsIso.Iso.inv_hom, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      congr
    · intro 
      rfl 

namespace IsPullback

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D)

lemma w : inclusion C ⋙ F = Core.functor' F ⋙ inclusion D := rfl

lemma w' : Cat.homOf (inclusion C) ≫ Cat.homOf F
    = Cat.homOf (Core.functor' F) ⋙ Cat.homOf (inclusion D) := rfl

variable {F} [F.ReflectsIsomorphisms] 

def lift (s : Limits.PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    s.pt ⥤ Core C := {
  obj := s.fst.obj
  map {x y} f := @asIso _ _ _ _ (s.fst.map f) $ by
    let f' : F.obj (s.fst.obj x) ≅ F.obj (s.fst.obj y) :=
      (eqToIso s.condition).app x ≪≫ s.snd.map f ≪≫ (eqToIso s.condition.symm).app y
    have hnat : F.map (s.fst.map f) ≫ _
      = _ ≫ (inclusion D).map (s.snd.map f)
      := (eqToHom s.condition).naturality f
    have h : F.map (s.fst.map f) = f'.hom := by
      simp only [Cat.eqToHom_app, comp_eqToHom_iff] at hnat
      simp only [hnat, f', Core.inclusion]
      simp
    have : IsIso (F.map (s.fst.map f)) := by rw [h]; exact Iso.isIso_hom f'
    exact Functor.ReflectsIsomorphisms.reflects F (s.fst.map f)
  map_id x := by
    simp only [asIso, Functor.map_id, IsIso.inv_id]
    congr 1
  map_comp f g := by
    simp only [asIso, Functor.map_comp, IsIso.inv_comp]
    congr 1
    simp
}

def fac_left (s : Limits.PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    lift s ≫ Cat.homOf (inclusion C) = s.fst := rfl

theorem Core.eqToIso_hom {a b : Core C} (h1 : a = b)
  (h2 : (inclusion C).obj a = (inclusion C).obj b) :
    (eqToHom h1).hom = eqToHom h2 := by
  cases h1
  rfl

def fac_right (s : Limits.PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D))) :
    lift s ≫ Cat.homOf (functor' F) = s.snd := by
  apply Functor.ext
  · intro x y f
    apply Functor.map_injective (inclusion D)
    have h := Functor.congr_hom s.condition f
    unfold Cat.homOf at *
    unfold inclusion at *
    simp only [Cat.of_α, Cat.comp_obj, lift, functor', comp_hom] at *
    convert h
    · apply Core.eqToIso_hom
    · apply Core.eqToIso_hom
  · intro x
    exact Functor.congr_obj s.condition x

def uniq (s : Limits.PullbackCone (Cat.homOf F) (Cat.homOf (inclusion D)))
  (m : s.pt ⟶ Cat.of (Core C))
  (fl : m ≫ Cat.homOf (inclusion C) = s.fst)
  (fr : m ≫ Cat.homOf (functor' F) = s.snd) :
    m = lift s := by
  apply Functor.ext
  · intro x y f
    apply Functor.map_injective (inclusion C)
    have h := Functor.congr_hom fl f
    unfold Cat.homOf at *
    unfold inclusion at *
    simp only [Cat.of_α, Cat.comp_map, lift, comp_hom, asIso_hom] at *
    rw [h, Core.eqToIso_hom, Core.eqToIso_hom]
  · intro x
    exact Functor.congr_obj fl x

/--
  In the category of categories,
  if functor `F : C ⥤ D` reflects isomorphisms
  then taking the `Core` is pullback stable along `F`

  Core C ---- inclusion -----> C
    |                          |
    |                          |
    |                          |
 Core.functor' F               F
    |                          |
    |                          |
    V                          V
  Core D ---- inclusion -----> D
-/
theorem isPullback_functor'_self :
    IsPullback
      (Cat.homOf $ inclusion C)
      (Cat.homOf $ functor' F)
      (Cat.homOf F)
      (Cat.homOf $ inclusion D) :=
  IsPullback.of_isLimit $
      Limits.PullbackCone.IsLimit.mk (w' F) lift fac_left fac_right uniq

end IsPullback

end Core

namespace PGrpd

namespace IsPullback
def CAT : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (Cat.{max (v+1) u, max (v+1) u})
def PCAT : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (PCat.{max (v+1) u, max (v+1) u})
def GRPD : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (Grpd.{max (v+1) u, max (v+1) u})
def PGRPD : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (PGrpd.{max (v+1) u, max (v+1) u})
def grpd : Cat.{max (v+1) u, max (v+1) u + 1} :=
  IsPullback.uLiftΓ.{max (v+1) u} (AsSmall.{u} Grpd.{v,v})
def pgrpd : Cat.{max (v+1) u, max (v+1) u + 1} :=
  IsPullback.uLiftΓ.{max (v+1) u} (AsSmall.{u} PGrpd.{v,v})


abbrev grothendieckAsSmallFunctor : Type (max u (v+1)) :=
  Grothendieck $
    Grpd.asSmallFunctor.{max u (v+1), v, v}
    ⋙ Grpd.forgetToCat.{max u (v+1)}

def GROTH : Cat.{max (v+1) u, max (v+1) u + 1} :=
  Cat.of (ULift.{max u (v+1) + 1, max (v+1) u}
        grothendieckAsSmallFunctor.{v,u})

def PCATFORGETTOCAT : PCAT.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf PCat.forgetToCat.{max (v+1) u, max (v+1) u}
def PGRPDFORGETTOGRPD : PGRPD.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf PGrpd.forgetToGrpd.{max (v+1) u, max (v+1) u}
def GRPDFORGETTOCAT : GRPD.{v,u} ⟶ CAT.{v,u} :=
  Cat.homOf Grpd.forgetToCat.{max (v+1) u, max (v+1) u}
def PGRPDFORGETTOPCAT : PGRPD.{v,u} ⟶ PCAT.{v,u} :=
  Cat.homOf PGrpd.forgetToPCat.{max (v+1) u, max (v+1) u}

def pGrpdForgetToGrpd : pgrpd.{v,u} ⟶ grpd.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up ⋙ upFunctor)
def grpdAsSmallFunctor : grpd.{v,u} ⟶ GRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ Grpd.asSmallFunctor.{max u (v+1)})
def pGrpdAsSmallFunctor : pgrpd.{v,u} ⟶ PGRPD.{v,u} :=
  Cat.homOf (downFunctor ⋙ AsSmall.down ⋙ PGrpd.asSmallFunctor.{max u (v+1)})


def asSmallFunctorCompForgetToCat' :
    AsSmall.{u} Grpd.{v,v} ⥤ Cat.{max (v+1) u, max (v+1) u} :=
  AsSmall.down
    ⋙ Grpd.asSmallFunctor.{max u (v+1), v, v}
    ⋙ Grpd.forgetToCat.{max u (v+1)}

-- def asSmallFunctorCompForgetToCat : grpd.{v,u} ⟶ CAT.{v,u} :=
--   Cat.homOf $ ULift.downFunctor ⋙ asSmallFunctorCompForgetToCat'

def grothendieckAsSmallFunctorToPGrpd :
    grothendieckAsSmallFunctor.{v, u} ⥤ PGrpd.{v,v} where
  obj x := PGrpd.fromGrpd x.base
    (AsSmall.down.obj.{v, v, max (v + 1) u} x.fiber)
  map f := {
    toFunctor := f.base
    point := AsSmall.down.map f.fiber}

def pGrpdToGrothendieckAsSmallFunctor :
    PGrpd.{v, v} ⥤ grothendieckAsSmallFunctor.{v,u} where
  obj x := {
    base := Grpd.of x
    fiber := AsSmall.up.obj.{v, v, max (v + 1) u} x.str.pt}
  map f := {
    base := f.toFunctor
    fiber := AsSmall.up.map f.point}
  map_comp f g := by
    apply Grothendieck.ext
    · simp [Grpd.forgetToCat, Grpd.asSmallFunctor]
    · rfl

def grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor' :
    grothendieckAsSmallFunctor.{v,u} ⥤ Grothendieck asSmallFunctorCompForgetToCat'.{v,u} where
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

def grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor :
    Grothendieck asSmallFunctorCompForgetToCat'.{v,u} ⥤ grothendieckAsSmallFunctor.{v,u} where
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
      ≅ Cat.of (ULift.{max u (v+1) + 1, max (v+1) u}
        grothendieckAsSmallFunctor.{v,u}) where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGrothendieckAsSmallFunctor
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ grothendieckAsSmallFunctorToPGrpd
    ⋙ AsSmall.up
    ⋙ ULift.upFunctor

def pGrpdIsoULiftGrothendieck :
    pgrpd.{v,u}
      ≅ IsPullback.uLiftGrothendieck
        asSmallFunctorCompForgetToCat'.{v,u} where
  hom := ULift.downFunctor
    ⋙ AsSmall.down
    ⋙ pGrpdToGrothendieckAsSmallFunctor
    ⋙ grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor'
    ⋙ ULift.upFunctor
  inv := ULift.downFunctor
    ⋙ grothendieckAsSmallFunctorToGrothendieckAsSmallFunctor
    ⋙ grothendieckAsSmallFunctorToPGrpd
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
        ⋙ (ULift.iso_self PCAT.{v,u}).hom)
      (IsPullback.uLiftGrothendieckForget asSmallFunctorCompForgetToCat')
      PCATFORGETTOCAT.{v,u}
      (IsPullback.uLiftA asSmallFunctorCompForgetToCat'
        ⋙ (ULift.iso_self CAT.{v,u}).hom)
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
    (pGrpdAsSmallFunctor ≫ PGRPDFORGETTOPCAT.{v,u})
    pGrpdForgetToGrpd.{v,u}
    PCATFORGETTOCAT.{v,u}
    (grpdAsSmallFunctor ≫ GRPDFORGETTOCAT.{v,u}) :=
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
      pGrpdAsSmallFunctor.{v,u}
      pGrpdForgetToGrpd.{v,u}
      PGRPDFORGETTOGRPD.{v,u}
      grpdAsSmallFunctor.{v,u} :=
  IsPullback.of_right
    isPullback_pgrpdforgettogrpd_PCATFORGETTOCAT.{v,u}
    rfl
    isPullback_forgetToGrpd_forgetToCat

end IsPullback
end PGrpd


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

-- def Ctx.coreOfCategory (C : Type u) [Category.{v} C] : Ctx.{max w v u} :=
--   Ctx.ofGroupoid (Core (AsSmall.{w} C))

def core : Cat.{v,v+1} ⥤ Ctx.{max u (v + 1)} :=
  Core.functor.{v,v+1}
  ⋙ Grpd.asSmallFunctor.{u,v,v+1}
  ⋙ Ctx.ofGrpd.{max u (v + 1)}

variable {Γ Δ : Ctx.{max u (v + 1)}} {C D : Type (v+1)}
  [Category.{v,v+1} C] [Category.{v,v+1} D]

def yonedaCoreEquiv' :
    (Γ ⟶ core.obj.{v,u} (Cat.of C))
      ≃ Ctx.toGrpd.obj Γ ⥤ Core C where
  toFun A := toGrpd.map A ⋙ AsSmall.down 
  invFun A := Ctx.ofGrpd.map (A ⋙ AsSmall.up)
  left_inv _ := rfl
  right_inv _ := rfl

-- /- The bijection y(Γ) → y(core C) ≃ Γ ⥤ C -/
-- def yonedaCoreEquiv :
--     (y(Γ) ⟶ y(core.obj.{v,u} (Cat.of C)))
--       ≃ Ctx.toGrpd.obj Γ ⥤ C :=
--   Yoneda.fullyFaithful.homEquiv.symm.trans
--     (yonedaCoreEquiv'.trans
--     Core.functorToCoreEquiv.symm)

/- The bijection Γ → core C ≃ Γ ⥤ C -/
def yonedaCoreEquiv :
    (Γ ⟶ core.obj.{v,u} (Cat.of C))
      ≃ Ctx.toGrpd.obj Γ ⥤ C :=
  Equiv.trans
    yonedaCoreEquiv'
    Core.functorToCoreEquiv.symm

end Ctx

@[simps] def catLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
  obj x := Cat.of (ULift.{u + 1, u} x)
  map {x y} f := downFunctor ⋙ f ⋙ upFunctor

variable (C D) [Category.{u} C] [Category.{u} D]

abbrev yonedaCat : Cat.{u,u+1} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj
    (AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op

instance yonedaCatPreservesLim : Limits.PreservesLimits yonedaCat :=
  Limits.comp_preservesLimits _ _

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

/-- The image of the pullback `Grothendieck.Groupoidal.isPullback` under `yonedaCat` -/
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

/-- `U.{v}` is the object representing the
  universe of `v`-small types
  i.e. `y(U) = Ty` for the small natural models `baseU`. -/
abbrev U : Ctx.{max u (v + 1)} :=
  Ctx.core.obj.{v,u} $ Cat.of Grpd.{v,v}

/-- `E.{v}` is the object representing `v`-small terms,
  living over `U.{v}`
  i.e. `y(E) = Tm` for the small natural models `baseU`. -/
abbrev E : Ctx.{max u (v + 1)} :=
  Ctx.core.obj.{v,u} $ Cat.of PGrpd.{v,v}

/-- `π.{v}` is the morphism representing `v`-small `tp`,
  for the small natural models `baseU`. -/
abbrev π : E.{v} ⟶ U.{v} :=
  Ctx.core.map.{v,u} $ Cat.homOf PGrpd.forgetToGrpd

namespace U
variable {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v})

/-- `liftSucc` is the base map between two `v`-small universes 
    E.{v} ---------------> E.{v+1}
    |                      |
    |                      |
    |                      |
    |                      |
    v                      v
    U.{v}-----liftsucc---->U.{v+1}
 -/
def liftSucc' : U.{v,max u (v+2)} ⟶ U.{v+1,max u (v+2)} :=
  Ctx.ofGrpd.map $
    AsSmall.down
    ⋙ (Core.functor'.{v,v+1,v+1,v+2} Grpd.asSmallFunctor.{v+1}
      : Core Grpd.{v,v} ⥤ Core Grpd.{v+1,v+1})
    ⋙ AsSmall.up

#check PGrpd.IsPullback.grpdAsSmallFunctor

def toTy' : Ctx.toGrpd.obj U.{v,u} ⥤ Grpd.{max u (v+1), max u (v+1)} :=
  AsSmall.down
    ⋙ Core.inclusion Grpd.{v,v}
    ⋙ Grpd.asSmallFunctor.{max u (v+1)}

def toTm' : Ctx.toGrpd.obj E.{v,u} ⥤ PGrpd.{max u (v+1), max u (v+1)} :=
  AsSmall.down
    ⋙ Core.inclusion PGrpd.{v,v}
    ⋙ PGrpd.asSmallFunctor.{max u (v+1)}

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
  yonedaCatEquiv.symm toTy'

lemma toTy_eq : yonedaCatEquiv.symm toTy' = sorry := by
  dsimp [yonedaCatEquiv, toTy']
  -- rw [yonedaEquiv_symm]
  
  sorry

def toTm : y(E.{v,u}) ⟶ Tm.{max u (v+1)} :=
  yonedaCatEquiv.symm toTm'


def isPullback_π_tp :
    IsPullback toTm ym(π) tp toTy := by
  
  sorry

-- /-- This is a natural model isomorphic to `baseU`,
--   its type classifier `Ty` is exactly `y(U.{v})` but its term classifier
--   `Tm` is the context extension from the ambient model `base`
-- -/
-- def baseU' : NaturalModelBase Ctx.{max u (v+1)} :=
--   NaturalModelBase.pullback base.{max u (v + 1)} toTy.{v,u}

theorem baseU'_isPullback :
    IsPullback (base.var toTy) (yoneda.map (base.disp toTy)) base.tp toTy.{v,u}
  := base.{max u (v+1)}.disp_pullback toTy.{v,u}

def baseU'.TmIsoEHom : Groupoidal (toTy'.{v,u})
    ⥤ PGrpd.{v,v} := by
  dsimp [toTy']
  
  sorry

def baseU'.TmIsoE : base.{max u (v+1)}.ext toTy.{v,u} ≅ E.{v} where
  -- Functor.mapIso AsSmall.up.map sorry 
  hom := Ctx.yonedaCoreEquiv.invFun baseU'.TmIsoEHom
    
  inv := sorry

abbrev ext : Ctx.{max u (v + 1)} :=
  GroupoidNaturalModel.ext (ym(A) ≫ toTy)

-- def ext_iso_ext : U.ext A ≅ GroupoidNaturalModel.ext (ym(A) ≫ toTy) := sorry

abbrev disp : ext A ⟶ Γ :=
  GroupoidNaturalModel.disp (ym(A) ≫ toTy)

abbrev var : ext A ⟶ E.{v} := sorry
  -- Ctx.yonedaCoreEquiv.symm $ Groupoidal.toPGrpd (Ctx.yonedaCoreEquiv A)

theorem isPullback_disp_π {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v}) :
    IsPullback (U.var (A)) (U.disp (A)) π A :=
  sorry

theorem isPullback_yoneda_disp_yoneda_π
    {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v}) :
    IsPullback
      ym(U.var (A))
      ym(U.disp (A))
      ym(π)
      ym(A) := 
  Functor.map_isPullback yoneda (isPullback_disp_π A)


end U

-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that unlike `GroupoidNaturalModel.base` this is representable,
  but since representables are `max u (v + 1)`-large,
  its representable fibers can be larger than itself.

  This natural model is given by pullback of the natural model `base`.
  TODO However, we likely want to use the explicit `Tm = y(E)` and
  `tp = ym(π)` instead of the grothendieck construction provided.
-/
def baseU : NaturalModelBase Ctx.{max u (v + 1)} where
  Ty := y(U.{v})
  Tm := y(E.{v})
  tp := ym(π.{v})
  ext A := U.ext (Yoneda.fullyFaithful.preimage A)
  disp A := U.disp (Yoneda.fullyFaithful.preimage A)
  var A := ym(U.var (Yoneda.fullyFaithful.preimage A))
  disp_pullback A := by
    convert U.isPullback_yoneda_disp_yoneda_π (Yoneda.fullyFaithful.preimage A)
    aesop_cat

def baseUU : NaturalModelBase Ctx.{max u (v + 2)} :=
  baseU.{v+1,u}.pullback ym(U.liftSucc'.{v,u})

def uHomSeqObjs (i : Nat) (h : i < 3) : NaturalModelBase Ctx.{2} :=
  match i with
  | 0 => baseUU.{0,2}
  | 1 => baseU.{1,2}
  | 2 => base.{2}
  | (n+3) => by omega

-- instance : Limits.HasTerminal Ctx := sorry

open NaturalModelBase

-- def baseUU.UHom : UHom baseUU.{v,max u (v+2)} baseU.{v+1,max u (v+2)} := {
--   baseU.pullbackHom ym(ULiftSucc'.{v,u}) with
--   U := sorry
--   U_pb := sorry
-- }

-- def baseU.UHom : UHom baseU.{v,max u (v+1)} base.{max u (v+1)} := {
--   base.pullbackHom ULiftMax with
--   U := sorry
--   U_pb := sorry
-- }

def uHomSeqHomSucc' (i : Nat) (h : i < 2) :
    (uHomSeqObjs i (by omega)).UHom (uHomSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => by
    dsimp [uHomSeqObjs]
    
    sorry -- NaturalModelBase.UHom.ofTarskiU base.{2} _ _
  | 1 => sorry
  | (n+2) => by omega

/--
  The groupoid natural model with two nested representable universes
-/
def uHomSeq : NaturalModelBase.UHomSeq Ctx.{2} where
  length := 2
  objs := uHomSeqObjs
  homSucc' := uHomSeqHomSucc'

end GroupoidNaturalModel

open GroupoidNaturalModel



end CategoryTheory

-- noncomputable
end
