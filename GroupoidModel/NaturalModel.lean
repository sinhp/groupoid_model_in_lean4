/-
Natural Models:
see https://arxiv.org/pdf/1406.3219
for the definition of a natural model
and how to model the type formers Σ,Π,Id.
A recent talk is here:
https://awodey.github.io/talks/ATT.pdf
-/

import Mathlib

import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.FunctorCategory


--import Poly
import Poly.LCCC.Basic
import Poly.LCCC.Presheaf
import Poly.Exponentiable
import Poly.Polynomial

-- import Poly.Exponentiable


universe u v

namespace CategoryTheory

open Functor Limits Opposite Representable

noncomputable section

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]

/-
We will need at least the following:
  - the category Ctx (to be interpreted as small groupoids)
  - the display maps of contexts, arising from iterated context extensions
  - the presheaf category 𝓔 = Psh(Ctx) in which the model lives
  - the presheaf Ty : Ctxᵒᵖ → Set of types in context
  - the presheaf Tm : Ctxᵒᵖ → Set of terms in context
  - the typing natural transformation tp : Tm ⟶ Ty
  - the proof that tp is (re)presentable
  - the polynomial endofunctor Pₜ : 𝓔 ⥤ 𝓔
  - the rules for Π-types as an operation on Pₜ(tp)
  - the rules for Σ-types as an operation on Pₜ(tp)
  - the rules for Id-types as an operation on tp : Tm ⟶ Ty
  - the universe Set of (small) discrete groupoids,
      along with its discrete (op-)fibration Set* ⟶ Set
  It would probably also be useful to have:
  - the proof that presentable natural transformations are "tiny" maps
    (the pushforward has a right adjoint)
  - the proof that Pₜ is therefore cocontinuous, since tp is tiny
  - need to add a general formulation for (groupoid) quotient types
  -/

/-!
# (Re)Presentable Natural Transformations
-/

class IsPresentable {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where
  ext (Γ : Ctx) (A : Ty.obj (op Γ)) : Ctx
  disp (Γ : Ctx) (A : Ty.obj (op Γ)) : ext Γ A ⟶ Γ
  var (Γ : Ctx) (A : Ty.obj (op Γ)) : Tm.obj (op (ext Γ A))
  pullback {Γ : Ctx} (A : Ty.obj (op Γ)) :
    IsPullback (yonedaEquiv.symm (var Γ A)) (yoneda.map (disp Γ A)) tp (yonedaEquiv.symm A)

namespace IsPresentable

-- variable {Tm Ty : Ctxᵒᵖ ⥤ Type v} (tp : Tm ⟶ Ty) [IsPresentable tp]

-- instance [IsPresentable tp] {X : Ctx} {q : Ty.obj (op X)} : Representable (pullback (yonedaEquiv.2 q) tp) := pullback_present q

-- /-- The presenting object of a presentable natural transformation. -/
-- def Present {X : Ctx} (q : Ty.obj (op X)) : Ctx :=
--   Classical.choose (has_representation (F := pullback (yonedaEquiv.2 q) tp))

-- /-- -/
-- def present {X : Ctx} (q : Ty.obj (op X)) : Present tp q ⟶ X := sorry

-- def var {X : Ctx} (q : Ty.obj (op X)) : yoneda.obj (Present tp q) ⟶ Tm := sorry

-- def square {X : Ctx} (q : Ty.obj (op X)) : yoneda.map (present tp q) ≫ yonedaEquiv.2 q = var f q ≫ f := sorry

end IsPresentable


/-!
# Natural Models
-/

local notation "Σ_ " => Over.map

local notation "Δ_ " => Over.baseChange

local notation "Π_ " => CartesianExponentiable.functor

section UvPoly

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C] [LCC C]

/-- The identity polynomial functor in single variable. -/
@[simps!]
def id (X : C) : UvPoly C := ⟨X, X, 𝟙 X, by infer_instance⟩

-- Note (SH): We define the functor associated to a single variable polyonimal in terms of `MvPoly.functor` and then reduce the proofs of statements about single variable polynomials to the multivariable case using the equivalence between `Over (⊤_ C)` and `C`.

def toMvPoly (P : UvPoly C) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨P.B, P.E, terminal.from P.E, P.p, P.exp, terminal.from P.B⟩

-- def hom (P : UvPoly C) (X : Over (⊤_ C)) : sorry → sorry := X.hom

/-- We use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`. Alternatively we can give a direct definition of `functor` in terms of exponetials. -/

def proj (P : UvPoly C) : C ⥤ C := equivOverTerminal.functor ⋙  P.functor'  ⋙ equivOverTerminal.inverse

attribute [instance] UvPoly.exp

def _root_.UvPoly.proj (P : UvPoly C) (X : Over (⊤_ C)) :
  ((Π_P.p).obj ((Δ_ (terminal.from P.E)).obj X)).left ⟶ P.B :=
  ((Δ_ (terminal.from _) ⋙ (Π_ P.p)).obj X).hom

set_option synthInstance.maxHeartbeats 100000 in
def _root_.UvPoly.star {𝒞} [Category 𝒞] [HasFiniteWidePullbacks 𝒞] [HasTerminal 𝒞] (P1 P2 : UvPoly 𝒞) : UvPoly 𝒞 :=
  let E : 𝒞 := P1.E
  let B : 𝒞 := P1.B
  let D : 𝒞 := P2.E
  let C : 𝒞 := P2.B
  let f : E ⟶ B := P1.p
  let g : D ⟶ C := P2.p
  {
    B := P1.functor.obj C
    E := sorry
    p := sorry
    exp := sorry
  }

def _root_.UvPoly.equiv {𝒞} [Category 𝒞] [HasFiniteWidePullbacks 𝒞] [HasTerminal 𝒞]
    (P : UvPoly 𝒞) (Γ : 𝒞) (X : 𝒞) :
    (Γ ⟶ P.functor.obj X) ≃ Σ b : Γ ⟶ P.B, pullback P.p b ⟶ X := sorry

end UvPoly


namespace NaturalModel

instance : HasFiniteWidePullbacks (Psh.{u,v} Ctx) := hasFiniteWidePullbacks_of_hasFiniteLimits _

instance : LCC (Psh Ctx) := @LCCC.mkOfOverCC _ _ _ ⟨CategoryOfElements.pshOverCCC⟩

instance {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : CartesianExponentiable tp where
  functor := LCC.pushforward tp
  adj := LCC.adj _

def uvPoly {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : UvPoly (Psh Ctx) := ⟨_, _, tp, inferInstance⟩

def P {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Psh Ctx ⥤ Psh Ctx := (uvPoly tp).functor

def proj {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : (P tp).obj Ty ⟶ Ty :=
  (uvPoly tp).proj _

class NaturalModelPi {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where
  Pi : (P tp).obj Ty ⟶ Ty
  lam : (P tp).obj Tm ⟶ Tm
  Pi_pullback : IsPullback lam ((P tp).map tp) tp Pi

class NaturalModelSigma {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where
  Sig : (P tp).obj Ty ⟶ Ty
  pair : ((uvPoly tp).star (uvPoly tp)).E ⟶ Tm
  Sig_pullback : IsPullback pair ((uvPoly tp).star (uvPoly tp)).p tp Sig

class NaturalModelId {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where

class NaturalModelU {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) extends IsPresentable tp : Type _ where
  U : Ty.obj (op (⊤_ _))
  El : yoneda.obj (ext (⊤_ Ctx) U) ⟶ Ty
  -- U_El : ((P tp).obj Ty).obj (op (⊤_ _)) := (by
    -- have := ((uvPoly tp).equiv _ _).symm ⟨_, _⟩
    -- dsimp [P, uvPoly, UvPoly.functor, equivOverTerminal, equivOverTerminal', UvPoly.functor',
    --   Equivalence.mk, UvPoly.toMvPoly, MvPoly.functor, CartesianExponentiable.functor,
    --   MvPoly.instCartesianExponentiableP, LCC.pushforward, OverCC.pushforwardFunctor, OverCC.pushforwardObj]
    -- )

class NaturalModel {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) extends
  IsPresentable tp, NaturalModelPi tp, NaturalModelSigma tp,
  NaturalModelId tp, NaturalModelU tp : Type _

end NaturalModel
