import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat

import GroupoidModel.Russell_PER_MS.NaturalModelBase
import GroupoidModel.Grothendieck.IsPullback
import GroupoidModel.Grothendieck.Groupoidal

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory ULift Grothendieck
  Limits NaturalModelBase CategoryTheory.Functor

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

def toCoreAsSmallEquiv {Γ : Ctx} {C : Type (v+1)} [Category.{v} C]
    : (Γ ⟶ Ctx.ofGrpd.obj (Grpd.of (Core (AsSmall C))))
    ≃ (Ctx.toGrpd.obj Γ ⥤ C) :=
  Ctx.homGrpdEquivFunctor.trans (
    Core.functorToCoreEquiv.symm.trans functorToAsSmallEquiv)

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

end Ty

def U' : Grpd.{max u (v+1),max u (v+1)} :=
  Grpd.of (Core (AsSmall.{max u (v+1)} Grpd.{v,v}))

/-- `U.{v}` is the object representing the
  universe of `v`-small types
  i.e. `y(U) = Ty` for the small natural models `baseU`. -/
def U : Ctx.{max u (v+1)} :=
  Ctx.ofGrpd.obj U'.{v,u}

def E' : Grpd.{max u (v+1),max u (v+1)} :=
  Grpd.of (Core (AsSmall.{max u (v+1)} PGrpd.{v,v}))

/-- `E.{v}` is the object representing `v`-small terms,
  living over `U.{v}`
  i.e. `y(E) = Tm` for the small natural models `baseU`. -/
def E : Ctx.{max u (v + 1)} :=
  Ctx.ofGrpd.obj E'.{v,u}

def π'' : AsSmall.{max u (v+1)} PGrpd.{v,v}
    ⥤ AsSmall.{max u (v+1)} Grpd.{v,v} :=
  AsSmall.down ⋙ PGrpd.forgetToGrpd ⋙ AsSmall.up

abbrev π' : E'.{v,u} ⟶ U'.{v,u} :=
  Grpd.homOf (Core.map' π'')

lemma π'_eq : Grpd.homOf (Core.map' π'') =
    Core.map.map (Cat.asSmallFunctor.map (Cat.homOf PGrpd.forgetToGrpd)) :=
  rfl

/-- `π.{v}` is the morphism representing `v`-small `tp`,
  for the small natural models `baseU`. -/
abbrev π : E.{v,u} ⟶ U.{v,u} :=
  Ctx.ofGrpd.map π'

namespace U

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

end U

end GroupoidModel

end
