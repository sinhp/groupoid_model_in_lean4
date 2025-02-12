import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Core

import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal


/-!
Here we construct the natural model for groupoids.
-/

universe w v u v₁ u₁ v₂ u₂

noncomputable section
open CategoryTheory ULift Grothendieck

/-
Grpd.{u, u} is
the category of
{small groupoids - size u objects and size u hom sets}
which itself has size u+1 objects (small groupoids)
and size u hom sets (functors).

We want our context category to be a small category so we will use
`AsSmall.{u}` for some large enough `u`
-/

namespace CategoryTheory

instance (Γ : Grpd.{v, w}) : Groupoid (AsSmall.{max w u v} Γ) where
  inv f := AsSmall.up.map (inv (AsSmall.down.map f))

def Grpd.asSmallFunctor : Grpd.{v, u} ⥤ Grpd.{max w v u, max w v u} where
  obj Γ := Grpd.of $ AsSmall.{max w v u} Γ
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

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

end Core

namespace GroupoidNaturalModel
abbrev Ctx := AsSmall.{u} Grpd.{u,u}

namespace Ctx
def ofGroupoid : Grpd.{u,u} ⥤ Ctx.{u} := AsSmall.up

def toGrpd : Ctx.{u} ⥤ Grpd.{u,u} := AsSmall.down

-- def Ctx.coreOfCategory (C : Type u) [Category.{v} C] : Ctx.{max w v u} :=
--   Ctx.ofGroupoid (Core (AsSmall.{w} C))


def core : Cat.{v,v+1} ⥤ Ctx.{max u (v + 1)} :=
  Core.functor.{v,v+1}
  ⋙ Grpd.asSmallFunctor.{u,v,v+1}
  ⋙ Ctx.ofGroupoid.{max u (v + 1)}

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

variable {Γ : Ctx.{u}} (A : yoneda.obj Γ ⟶ Ty)

abbrev tp : Tm ⟶ Ty := yonedaCat.map (PGrpd.forgetToGrpd)

abbrev ext : Ctx := Ctx.ofGroupoid.obj $ Grpd.of (Groupoidal (yonedaCatEquiv A))

abbrev disp : ext A ⟶ Γ :=
  AsSmall.up.map (Grothendieck.forget (yonedaCatEquiv A ⋙ Grpd.forgetToCat))

abbrev var : (y(ext A) : Psh Ctx) ⟶ Tm :=
  yonedaCatEquiv.symm (Groupoidal.toPGrpd (yonedaCatEquiv A))

/-- `grpdCore.{v}` serves as the universe of `v`-small types
  i.e. the "`Ty`" for the small (as in yoneda(...)) natural models. -/
abbrev grpdCore : Ctx.{max u (v + 1)} :=
  Ctx.core.obj.{v,u} $ Cat.of Grpd.{v,v}

/-- `grpdCoreLiftMax` is the map that classifies the universe
  `grpdCore` of `v`-small types as a map into the type classifier `Ty`.
  This will fit into the pullback square

    E ---------------> Tm
    |                   |
    |                   |
    |                   |
    |                   |
    v                   v
    U--grpdCoreLiftMax-->Ty

-/
def grpdCoreLiftMax : y(grpdCore.{v,u}) ⟶ Ty.{max u (v+1)} :=
  yonedaCatEquiv.symm $
    AsSmall.down
    ⋙ Core.inclusion Grpd.{v,v}
    ⋙ Grpd.asSmallFunctor.{max u (v+1)}

-- lemma yonedaEquiv_grpdCoreLiftMax :
--     yonedaEquiv grpdCoreLiftMax.{v,u} = 
--     ULift.downFunctor.{max u (v + 1), max u (v + 1), max (u + 1) (v + 2)}
--       ⋙ AsSmall.down.{v, v + 1, max u (v + 1)}
--       ⋙ Core.inclusion Grpd.{v,v}
--       ⋙ Grpd.asSmallFunctor.{max u (v+1)} := rfl

/-- The image of (roughly) `Groupoidal.toPGrpd : Grothendieck A ⥤ PGrpd`
  under `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
  -/
abbrev yonedaCatMapToPGrpd :
    yonedaCat.obj (IsPullback.uLiftGrothendieck $ Groupoidal.toCat (yonedaCatEquiv A)) ⟶ Tm :=
  yonedaCat.map
      (Cat.homOf (ULift.downFunctor ⋙ Groupoidal.toPGrpd (yonedaCatEquiv A)))

/-- The image of (roughly) `Grothendieck.forget : Grothendieck A ⥤ Γ` under
  `yonedaCat`.
  Used in the pullback diagram `isPullback_yonedaCatULiftGrothendieckForget_tp`
-/
abbrev yonedaCatMapGrothendieckForget :=
      (yonedaCat.map $ IsPullback.uLiftGrothendieckForget
        (Groupoidal.toCat.{u} $ yonedaCatEquiv A))

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
    Functor.map_isPullback _ (Groupoidal.isPullback _)

def asSmallUp_comp_yoneda_iso_forgetToCat_comp_catLift_comp_yonedaCat :
    (AsSmall.up) ⋙ (yoneda : Ctx.{u} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1))
    ≅ Grpd.forgetToCat ⋙ catLift ⋙ yonedaCat where
  hom := {app Γ := yonedaEquiv.symm (CategoryStruct.id _)}
  inv := {
    app Γ := {
      app Δ := λ F ↦ AsSmall.up.map $ ULift.upFunctor ⋙ F ⋙ ULift.downFunctor}}

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

theorem isPullback_yonedaDisp_tp :
    IsPullback (var A) (yoneda.map (disp A)) tp A := by
  convert IsPullback.paste_horiz
    (isPullback_yonedaDisp_yonedaCatULiftGrothendieckForget A)
    (isPullback_yonedaCatGrothendieckForget_tp _)
  ext Δ F
  exact congr_fun (@A.naturality (Opposite.op Γ) Δ F.op) (CategoryStruct.id Γ)

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


-- TODO link to this in blueprint
/-- The natural model that acts as the classifier of `v`-large terms and types.
  Note that unlike `GroupoidNaturalModel.base` this is representable,
  but since representables are `max u (v + 1)`-large,
  its representable fibers can be larger than itself.
-/
def baseU : NaturalModelBase Ctx.{max u (v + 1)} :=
  NaturalModelBase.pullback base.{max u (v + 1)} grpdCoreLiftMax.{v,u}

def uHomSeqObjs (i : Nat) (h : i < 3) : NaturalModelBase Ctx.{2} :=
  match i with
  | 0 => baseU.{0,2}
  | 1 => baseU.{1,2}
  | 2 => base
  | (n+3) => by omega

-- instance : Limits.HasTerminal Ctx := sorry

open NaturalModelBase

def grpdCoreLiftSucc : grpdCore.{v,max u (v+2)} ⟶ grpdCore.{v+1,max u (v+2)} :=
  Ctx.ofGroupoid.map $
    AsSmall.down
    ⋙ (Core.functor'.{v,v+1,v+1,v+2} Grpd.asSmallFunctor.{v+1}
      : Core Grpd.{v,v} ⥤ Core Grpd.{v+1,v+1})
    ⋙ AsSmall.up

lemma grpdCoreLiftSucc_comp_LiftMax :
  ym(grpdCoreLiftSucc.{v,u}) ≫ grpdCoreLiftMax.{v+1,max u (v+2)}
    = grpdCoreLiftMax.{v, max u (v+2)} := by
  -- ext Γ x
  apply yonedaCatEquiv.injective
  rw [← yonedaCatEquiv_naturality]
  -- simp [grpdCoreLiftMax, grpdCoreLiftSucc]
  convert_to _ ⋙ yonedaCatEquiv (yonedaCatEquiv.symm _) =
    yonedaCatEquiv (yonedaCatEquiv.symm _)
  rw [Equiv.apply_symm_apply]
  rw [Equiv.apply_symm_apply]

  -- rw[yonedaCatEquiv_yonedaEquivSymm]
  -- rw[yonedaCatEquiv_yonedaEquivSymm]
  simp [grpdCoreLiftSucc, Ctx.ofGroupoid]
  simp [Functor.assoc]
  congr 1
  
  -- simp [← Functor.assoc]
  have h : Core.functor' Grpd.asSmallFunctor.{v+1,v,v} ⋙ Core.inclusion Grpd.{v+1,v+1} ⋙ Grpd.asSmallFunctor.{u,v+1,v+1} =
    Core.inclusion Grpd ⋙ Grpd.asSmallFunctor.{max u (v+1),v,v} := by
    simp [← Functor.assoc]
    rw [Core.functor'_comp_inclusion]
    simp [Functor.assoc]
    congr 1

    sorry
  sorry
  -- apply Functor.ext
  -- · sorry
  -- simp [grpdCoreLiftMax, grpdCoreLiftSucc]
  -- have h := yonedaEquiv_comp
  -- · intro x
  --   simp
  --   sorry

def baseU.UHom : Hom baseU.{v,max u (v+2)} baseU.{v+1,max u (v+2)} := by
  let f :=
  Hom.subst base.{max u (v+2)} grpdCoreLiftMax.{v+1,u} grpdCoreLiftSucc.{v,u}
  dsimp [baseU]
  -- have h := dkflj.{v,u}

  -- these are not defeq, but they are both pullbacks of the same map.
  sorry
  -- { Hom.subst base grpdCoreLiftMax grpdCoreLiftSucc with
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
