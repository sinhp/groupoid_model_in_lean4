import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat

import GroupoidModel.Russell_PER_MS.NaturalModel
import GroupoidModel.Grothendieck.Groupoidal.IsPullback

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory ULift Grothendieck.Groupoidal
  Limits NaturalModelBase CategoryTheory.Functor

namespace CategoryTheory.PGrpd
def pGrpdToGroupoidalAsSmallFunctor : PGrpd.{v, v} ⥤
    ∫(Grpd.asSmallFunctor.{max w (v+1), v, v}) :=
  Grothendieck.functorTo (Grothendieck.forget _)
  (fun x => AsSmall.up.obj.{v, v, max w (v + 1)} x.fiber)
  (fun f => AsSmall.up.map f.fiber)
  (by aesop_cat)
  (by aesop_cat)

def groupoidalAsSmallFunctorToPGrpd :
    ∫(Grpd.asSmallFunctor.{max w (v+1), v, v}) ⥤ PGrpd.{v,v} :=
  PGrpd.functorTo (Grothendieck.forget _)
  (fun x => AsSmall.down.obj.{v, v, max w (v + 1)} x.fiber)
  (fun f => AsSmall.down.map f.fiber)
  (by aesop_cat)
  (by aesop_cat)

@[simp] def pGrpdToGroupoidalAsSmallFunctor_groupoidalAsSmallFunctorToPGrpd :
    groupoidalAsSmallFunctorToPGrpd ⋙ pGrpdToGroupoidalAsSmallFunctor = 𝟭 _ :=
  rfl

@[simp] def groupoidalAsSmallFunctorToPGrpd_pGrpdToGroupoidalAsSmallFunctor :
    pGrpdToGroupoidalAsSmallFunctor ⋙ groupoidalAsSmallFunctorToPGrpd = 𝟭 _ :=
  rfl

@[simp] def pGrpdToGroupoidalAsSmallFunctor_forget : pGrpdToGroupoidalAsSmallFunctor
    ⋙ Grothendieck.Groupoidal.forget = Grothendieck.forget _ :=
  rfl

def asSmallFunctor : PGrpd.{v, v} ⥤ PGrpd.{max w (v+1), max w (v+1)} :=
  pGrpdToGroupoidalAsSmallFunctor ⋙
  Grothendieck.Groupoidal.toPGrpd Grpd.asSmallFunctor.{max w (v+1), v, v}

end CategoryTheory.PGrpd

namespace GroupoidModel

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

@[simps] def equivalence : CategoryTheory.Equivalence Grpd.{u,u} Ctx.{u} where
  functor := AsSmall.up
  inverse := AsSmall.down
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl

abbrev ofGrpd : Grpd.{u,u} ⥤ Ctx.{u} := equivalence.functor

abbrev toGrpd : Ctx.{u} ⥤ Grpd.{u,u} := equivalence.inverse

def ofGroupoid (Γ : Type u) [Groupoid.{u} Γ] : Ctx.{u} :=
  ofGrpd.obj (Grpd.of Γ)

def ofCategory (C : Type (v+1)) [Category.{v} C] : Ctx.{max u (v+1)} :=
  Ctx.ofGrpd.obj $ Grpd.of (Core (AsSmall C))

def homOfFunctor {C : Type (v+1)} [Category.{v} C] {D : Type (w+1)} [Category.{w} D]
    (F : C ⥤ D) : Ctx.ofCategory.{v, max u (v+1) (w+1)} C
    ⟶ Ctx.ofCategory.{w, max u (v+1) (w+1)} D :=
  Ctx.ofGrpd.map $ Grpd.homOf $ Core.map' $ AsSmall.down ⋙ F ⋙ AsSmall.up

instance : ChosenFiniteProducts Ctx := equivalence.chosenFiniteProducts

end Ctx

@[simps] def catLift : Cat.{u,u} ⥤ Cat.{u,u+1} where
  obj x := Cat.of (ULift.{u + 1, u} x)
  map {x y} f := downFunctor ⋙ f ⋙ upFunctor

section yonedaCat
variable (C D) [Category.{u} C] [Category.{u} D]

/-- `yonedaCat` is the following composition

  Cat --- yoneda ---> Psh Cat -- restrict along inclusion --> Psh Ctx

  where Ctx --- inclusion ---> Cat
  takes a groupoid and forgets it to a category
  (with appropriate universe level adjustments)
-/
abbrev yonedaCat : Cat.{u,u+1} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙ (whiskeringLeft _ _ _).obj
    (AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift).op

instance yonedaCatPreservesLimits : PreservesLimits yonedaCat :=
  comp_preservesLimits _ _

variable {Γ Δ : Ctx.{u}} {C D : Cat.{u,u+1}}

def yonedaCatEquivAux : (yonedaCat.obj C).obj (Opposite.op Γ)
    ≃ (Ctx.toGrpd.obj Γ) ⥤ C where
  toFun     := λ A ↦ ULift.upFunctor ⋙ A
  invFun    := λ A ↦ ULift.downFunctor ⋙ A
  left_inv  := λ _ ↦ rfl
  right_inv := λ _ ↦ rfl

/- The bijection y(Γ) → [-,C]   ≃   Γ ⥤ C -/
def yonedaCatEquiv : (yoneda.obj Γ ⟶ yonedaCat.obj C)
    ≃ Ctx.toGrpd.obj Γ ⥤ C :=
  yonedaEquiv.trans yonedaCatEquivAux

lemma yonedaCatEquiv_yonedaEquivSymm {Γ : Ctx}
    (A : (yonedaCat.obj C).obj (Opposite.op Γ)) :
    yonedaCatEquiv (yonedaEquiv.symm A) = upFunctor ⋙ A := by
  congr

theorem yonedaCatEquiv_naturality_left
    (A : yoneda.obj Γ ⟶ yonedaCat.obj C) (σ : Δ ⟶ Γ) :
    yonedaCatEquiv (yoneda.map σ ≫ A) =
    (Ctx.toGrpd.map σ) ⋙ yonedaCatEquiv A:= by
  simp only [AsSmall.down_obj, AsSmall.down_map, yonedaCatEquiv,
    Functor.op_obj, Functor.comp_obj, Cat.of_α,
    Equiv.trans_apply, Equiv.coe_fn_mk, ← yonedaEquiv_naturality]
  rfl

theorem yonedaCatEquiv_naturality_right
    (A : yoneda.obj Γ ⟶ yonedaCat.obj D) (U : D ⥤ C) :
    yonedaCatEquiv (A ≫ yonedaCat.map U) = yonedaCatEquiv A ⋙ U := rfl

theorem yonedaCatEquiv_symm_naturality_left
    (A : Ctx.toGrpd.obj Γ ⥤ C) (σ : Δ ⟶ Γ) :
    yoneda.map σ ≫ yonedaCatEquiv.symm A =
    yonedaCatEquiv.symm (Ctx.toGrpd.map σ ⋙ A) := rfl

theorem yonedaCatEquiv_symm_naturality_right
    (A : Ctx.toGrpd.obj Γ ⥤ D) (U : D ⥤ C) :
    yonedaCatEquiv.symm (A ⋙ U) =
    yonedaCatEquiv.symm A ≫ yonedaCat.map U := rfl

end yonedaCat

def Ctx.homGrpdEquivFunctor {Γ : Ctx} {G : Type v} [Groupoid.{v} G]
    : (Γ ⟶ Ctx.ofGrpd.obj (Grpd.of G))
    ≃ Ctx.toGrpd.obj Γ ⥤ G where
  toFun A := Ctx.toGrpd.map A
  invFun A := Ctx.ofGrpd.map A
  left_inv _ := rfl
  right_inv _ := rfl

section

variable {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {C : Type (v+1)} [Category.{v} C]
    {D : Type (v+1)} [Category.{v} D]

def toCoreAsSmallEquiv : (Γ ⟶ Ctx.ofGrpd.obj (Grpd.of (Core (AsSmall C))))
    ≃ (Ctx.toGrpd.obj Γ ⥤ C) :=
  Ctx.homGrpdEquivFunctor.trans (
    Core.functorToCoreEquiv.symm.trans functorToAsSmallEquiv)

theorem toCoreAsSmallEquiv_symm_naturality_left {A : Ctx.toGrpd.obj Γ ⥤ C} :
    toCoreAsSmallEquiv.symm (Ctx.toGrpd.map σ ⋙ A) = σ ≫ toCoreAsSmallEquiv.symm A := by
  sorry

theorem toCoreAsSmallEquiv_naturality_left (A : Γ ⟶ Ctx.ofCategory C) :
    toCoreAsSmallEquiv (σ ≫ A) = Ctx.toGrpd.map σ ⋙ toCoreAsSmallEquiv A := by
  sorry

/- The bijection y(Γ) → y[-,C]   ≃   Γ ⥤ C -/
abbrev yonedaCategoryEquiv {Γ : Ctx} {C : Type (v+1)} [Category.{v} C] :
    (y(Γ) ⟶ y(Ctx.ofCategory C))
    ≃ Ctx.toGrpd.obj Γ ⥤ C :=
  Yoneda.fullyFaithful.homEquiv.symm.trans toCoreAsSmallEquiv

theorem yonedaCategoryEquiv_naturality_left (A : y(Γ) ⟶ y(Ctx.ofCategory C)) :
    yonedaCategoryEquiv (ym(σ) ≫ A) = Ctx.toGrpd.map σ ⋙ yonedaCategoryEquiv A :=
  sorry

theorem yonedaCategoryEquiv_naturality_left' (A : y(Γ) ⟶ y(Ctx.ofCategory C))
    {σ : y(Δ) ⟶ y(Γ)} : yonedaCategoryEquiv (σ ≫ A) =
    Ctx.toGrpd.map (Yoneda.fullyFaithful.preimage σ)
    ⋙ yonedaCategoryEquiv A := by
  have h : σ = ym(Yoneda.fullyFaithful.preimage σ) := by simp
  rw [h, yonedaCategoryEquiv_naturality_left]
  rfl

theorem yonedaCategoryEquiv_symm_naturality_left {A : Ctx.toGrpd.obj Γ ⥤ C} :
    yonedaCategoryEquiv.symm (Ctx.toGrpd.map σ ⋙ A) = ym(σ) ≫ yonedaCategoryEquiv.symm A := by
  rw [yonedaCategoryEquiv.symm_apply_eq, yonedaCategoryEquiv_naturality_left, Equiv.apply_symm_apply]

theorem yonedaCategoryEquiv_naturality_right {D : Type (v+1)} [Category.{v} D]
    (A : y(Γ) ⟶ y(Ctx.ofCategory C)) (F : C ⥤ D) :
    yonedaCategoryEquiv (A ≫ ym(Ctx.homOfFunctor F)) = yonedaCategoryEquiv A ⋙ F :=
  sorry

theorem yonedaCategoryEquiv_symm_naturality_right
    {A : Ctx.toGrpd.obj Γ ⥤ C} (F : C ⥤ D):
    yonedaCategoryEquiv.symm (A ⋙ F) =
    yonedaCategoryEquiv.symm A ≫ ym(Ctx.homOfFunctor F) := by
  sorry

end

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
    (yoneda : Ctx.{u} ⥤ Ctx.{u}ᵒᵖ ⥤ Type (u + 1))
    ≅ AsSmall.down ⋙ Grpd.forgetToCat ⋙ catLift ⋙ yonedaCat where
  hom := {app Γ := yonedaEquiv.symm (CategoryStruct.id _)}
  inv := {
    app Γ := {
      app Δ := λ F ↦
        AsSmall.up.map $ ULift.upFunctor ⋙ F ⋙ ULift.downFunctor}}

/-- `U.{v}` is the object representing the
  universe of `v`-small types
  i.e. `y(U) = Ty` for the small natural models `smallU`. -/
def U : Ctx.{max u (v+1)} :=
  Ctx.ofCategory Grpd.{v,v}

/-- `E.{v}` is the object representing `v`-small terms,
  living over `U.{v}`
  i.e. `y(E) = Tm` for the small natural models `smallU`. -/
def E : Ctx.{max u (v + 1)} :=
  Ctx.ofCategory PGrpd.{v,v}


/-- `π.{v}` is the morphism representing `v`-small `tp`,
  for the small natural models `smallU`. -/
abbrev π : E.{v,max u (v+1)} ⟶ U.{v, max u (v+1)} :=
  Ctx.homOfFunctor PGrpd.forgetToGrpd

namespace U

variable {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v})

def classifier : Ctx.toGrpd.obj Γ ⥤ Grpd.{v,v} :=
  Ctx.toGrpd.map A ⋙ Core.inclusion (AsSmall Grpd) ⋙ AsSmall.down

abbrev ext : Ctx.{max u (v + 1)} :=
  Ctx.ofGrpd.obj (Grpd.of ∫(classifier A))

abbrev disp : ext A ⟶ Γ :=
  Ctx.ofGrpd.map forget

abbrev var : ext A ⟶ E.{v} :=
  toCoreAsSmallEquiv.symm (toPGrpd (classifier A))

section SmallUHom

variable {Γ : Ctx.{max u (v + 1)}} (A : Γ ⟶ U.{v})

-- TODO rename `U.toU` to `U.liftU` and rename `U.toE` to `U.liftE`
/-- `toU` is the base map between two `v`-small universes
               toE
    E.{v} --------------> E.{v+1}
    |                      |
    |                      |
  π |                      | π
    |                      |
    v                      v
    U.{v}-------toU-----> U.{v+1}
 -/
def toU : U.{v, max u (v+2)} ⟶ U.{v+1, max u (v+2)} :=
  Ctx.homOfFunctor.{v+1,v} Grpd.asSmallFunctor.{v+1}

def toE : E.{v, max u (v+2)} ⟶ E.{v+1,max u (v+2)} :=
  Ctx.homOfFunctor.{v+1,v} PGrpd.asSmallFunctor.{v+1}

end SmallUHom

end U

end GroupoidModel

end
