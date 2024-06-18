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
  - the presheaf Type : Ctxᵒᵖ → Set of types in context
  - the presheaf Term : Ctxᵒᵖ → Set of terms in context
  - the typing natural transformation t : Term ⟶ Type
  - the proof that t is (re)presentable
  - the polynomial endofunctor Pₜ : 𝓔 ⥤ 𝓔
  - the rules for Π-types as an operation on Pₜ(t)
  - the rules for Σ-types as an operation on Pₜ(t)
  - the rules for Id-types as an operation on t : Term ⟶ Type
  - the universe Set of (small) discrete groupoids,
      along with its discrete (op-)fibration Set* ⟶ Set
  It would probably also be useful to have:
  - the proof that presentable natural transformations are "tiny" maps
    (the pushforward has a right adjoint)
  - the proof that Pₜ is therefore cocontinuous, since t is tiny
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

-- variable {Tm Ty : Ctxᵒᵖ ⥤ Type v} (tp : Tm ⟶ Ty) [IsPresentable t]

-- instance [IsPresentable tp] {X : Ctx} {q : Ty.obj (op X)} : Representable (pullback (yonedaEquiv.2 q) t) := pullback_present q

-- /-- The presenting object of a presentable natural transformation. -/
-- def Present {X : Ctx} (q : Ty.obj (op X)) : Ctx :=
--   Classical.choose (has_representation (F := pullback (yonedaEquiv.2 q) t))

-- /-- -/
-- def present {X : Ctx} (q : Ty.obj (op X)) : Present t q ⟶ X := sorry

-- def var {X : Ctx} (q : Ty.obj (op X)) : yoneda.obj (Present t q) ⟶ Tm := sorry

-- def square {X : Ctx} (q : Ty.obj (op X)) : yoneda.map (present t q) ≫ yonedaEquiv.2 q = var f q ≫ f := sorry

end IsPresentable


/-!
# Natural Models
-/

instance : HasFiniteWidePullbacks (Psh Ctx) := hasFiniteWidePullbacks_of_hasFiniteLimits _

def Pt {Tm Ty : Psh Ctx} (t : Tm ⟶ Ty) : Psh Ctx ⥤ Psh Ctx :=
  UvPoly.functor ⟨_, _, t, sorry⟩


class NaturalModelPi {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where
  tp_pres : IsPresentable tp
  Pi : (Pt tp).obj Ty ⟶ Ty
  lam : (Pt tp).obj Tm ⟶ Tm
  Pi_pullback : IsPullback lam ((Pt tp).map tp) tp Pi

class NaturalModelSigma {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where
  tp_pres : IsPresentable tp
  Sig : (Pt tp).obj Ty ⟶ Ty
  SigPairObj : Psh Ctx := sorry
  SigPairProj : SigPairObj ⟶ (Pt tp).obj Ty := sorry
  pair : SigPairObj ⟶ Tm := sorry
  Sig_pullback : IsPullback pair ((Pt t).map t) t Pi

class NaturalModelId {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where
  tp_pres : IsPresentable tp

class NaturalModelU {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Type _ where
  tp_pres : IsPresentable tp


namespace NaturalModel


end NaturalModel
