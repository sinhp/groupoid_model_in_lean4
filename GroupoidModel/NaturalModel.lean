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
