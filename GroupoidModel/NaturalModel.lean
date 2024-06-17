/-
Natural Models:
see https://arxiv.org/pdf/1406.3219
for the definition of a natural model
and how to model the type formers Σ,Π,Id.
A recent talk is here:
https://awodey.github.io/talks/ATT.pdf
-/

import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.FunctorCategory
import Mathlib
import Poly.LCCC.Polynomial
import Poly.Exponentiable
import Poly.Presheaves.presheaves

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

class IsPresentable {Tm Tp : Psh Ctx} (t : Tm ⟶ Tp) : Type _ where
  extension (Γ : Ctx) (A : Tp.obj (op Γ)) : Ctx
  p (Γ : Ctx) (A : Tp.obj (op Γ)) : extension Γ A ⟶ Γ
  var (Γ : Ctx) (A : Tp.obj (op Γ)) : Tm.obj (op (extension Γ A))
  pullback {Γ : Ctx} (A : Tp.obj (op Γ)) :
    IsPullback (yonedaEquiv.symm (var Γ A)) (yoneda.map (p Γ A)) t (yonedaEquiv.symm A)

namespace IsPresentable

-- variable {Tm Tp : Ctxᵒᵖ ⥤ Type v} (t : Tm ⟶ Tp) [IsPresentable t]

-- instance [IsPresentable t] {X : Ctx} {q : Tp.obj (op X)} : Representable (pullback (yonedaEquiv.2 q) t) := pullback_present q

-- /-- The presenting object of a presentable natural transformation. -/
-- def Present {X : Ctx} (q : Tp.obj (op X)) : Ctx :=
--   Classical.choose (has_representation (F := pullback (yonedaEquiv.2 q) t))

-- /-- -/
-- def present {X : Ctx} (q : Tp.obj (op X)) : Present t q ⟶ X := sorry

-- def var {X : Ctx} (q : Tp.obj (op X)) : yoneda.obj (Present t q) ⟶ Tm := sorry

-- def square {X : Ctx} (q : Tp.obj (op X)) : yoneda.map (present t q) ≫ yonedaEquiv.2 q = var f q ≫ f := sorry

end IsPresentable


/-!
# Natural Models
-/

instance : HasFiniteWidePullbacks (Psh Ctx) := hasFiniteWidePullbacks_of_hasFiniteLimits _

def Pt {Tm Tp : Psh Ctx} (t : Tm ⟶ Tp) : Psh Ctx ⥤ Psh Ctx :=
  -- UvPoly.functor' ⟨_, _, t⟩
  sorry

class NaturalModel {Tm Tp : Psh Ctx} (t : Tm ⟶ Tp) : Type _ where
  t_rep : IsPresentable t
  Pi : (Pt t).obj Tp ⟶ Tp
  lam : (Pt t).obj Tm ⟶ Tm
  Pi_pullback : IsPullback lam ((Pt t).map t) t Pi
  Sigma : (Pt t).obj Tp ⟶ Tp


namespace NaturalModel


end NaturalModel
