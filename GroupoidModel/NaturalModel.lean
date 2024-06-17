/-
Natural Models:
see https://arxiv.org/pdf/1406.3219
for the definition of a natural model
and how to model the type formers Σ,Π,Id.
-/

import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Presheaf

universe u v

namespace CategoryTheory

open Functor Limits Opposite Representable

noncomputable section

variable {C : Type u} [Category.{v} C] [HasTerminal C]

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
  - the type-formers Σ, Π, Id as operations on polynomials over 𝓔
  - the universe Set of (small) discrete groupoids,
      along with its discrete (op-)fibration Set* ⟶ Set
  It would also be useful to have:
  - the proof that presentable natural transformations are tiny maps
  - the proof that Pₜ is therefore cocontinuous, since t is tiny
  -/

/-!
# (Re)Presentable Natural Transformations
-/


class IsPresentable {P Q : C ᵒᵖ ⥤ Type v} (f : P ⟶ Q) : Type _ where
  pullback_present : {X : C} → (q : Q.obj (op X)) → Representable (pullback (yonedaEquiv.2 q) f)

namespace IsPresentable

variable {P Q : C ᵒᵖ ⥤ Type v} (f : P ⟶ Q) [IsPresentable f]

instance [IsPresentable f] {X : C} {q : Q.obj (op X)} : Representable (pullback (yonedaEquiv.2 q) f) := pullback_present q

/-- The presenting object of a presentable natural transformation. -/
def Present {X : C} (q : Q.obj (op X)) : C :=
  Classical.choose (has_representation (F := pullback (yonedaEquiv.2 q) f))

/-- -/
def present {X : C} (q : Q.obj (op X)) : Present f q ⟶ X := sorry

def var {X : C} (q : Q.obj (op X)) : yoneda.obj (Present f q) ⟶ P := sorry

def square {X : C} (q : Q.obj (op X)) : yoneda.map (present f q) ≫ yonedaEquiv.2 q = var f q ≫ f := sorry

end IsPresentable


/-!
# Natural Models
-/

class NaturalModel {Tp Tm : C ᵒᵖ ⥤ Type v} (tp : Tp ⟶ Tm) : Type _ where
  tp_rep : IsPresentable tp

namespace NaturalModel


end NaturalModel
