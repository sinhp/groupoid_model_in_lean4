/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Wojciech Nawrocki
-/
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Lean.Meta.Simp
import Mathlib.Tactic.Simps.Basic
import Mathlib.Util.AddRelatedDecl
import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# The `functor_map` attribute

Adding `@[functor_map]` to a lemma named `fact` of shape `∀ .., f ≫ g = i ≫ j`,
where `f g i j` are morphisms in some category `C`,
will create a new lemma named `fact_functor_map` of shape
`∀ .. {D : Type} [Category D] (F : C ⥤ D), F.map f ≫ F.map g = F.map i ≫ F.map j`,
with the conclusion simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for generating lemmas which the simplifier can use even on expressions
that appear under a functor.

There is also a term elaborator `functor_map_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace CategoryTheory

universe v₁ u₁ v₂ u₂
variable {C : Type u₁} [Category.{v₁} C]

private theorem eq_functor_map {X Y : C} {f g : X ⟶ Y} (w : f = g) :
    ∀ {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D), F.map f = F.map g := by
  intros; rw [w]

/-- Like `categorySimp` but also includes `Functor.map_comp`, `Functor.map_id`. -/
def categorySimp' (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Category.comp_id, ``Category.id_comp, ``Category.assoc,
    ``Functor.id_obj, ``Functor.id_map, ``Functor.comp_obj, ``Functor.comp_map,
    ``Functor.map_id, ``Functor.map_comp] e
    (config := { decide := false })

def functorMapExpr (e : Expr) (lvl_params : Bool) : MetaM (Expr × List Level) := do
  let [v₂, u₂] ←
    if lvl_params then
      let v₂ := mkLevelParam (← mkFreshLMVarId).name
      let u₂ := mkLevelParam (← mkFreshLMVarId).name
      pure [v₂, u₂]
    else mkFreshLevelMVars 2 | panic! "internal error"
  let e ← mapForallTelescope (forallTerm := e) fun e => do
    let eTp ← inferType e
    let some (hom, _, _) := eTp.eq? | throwError "expected an equality, got{indentD eTp}"
    if !hom.isAppOf ``Quiver.Hom then
      throwError "expected an equality of morphisms, got{indentD eTp}"
    let [.succ v₁, u₁] := hom.getAppFn.constLevels! |
      throwError "unexpected universe levels in{indentD hom.getAppFn}"
    let e' ← mkAppM' (.const ``eq_functor_map [v₁, u₁, v₂, u₂]) #[e]
    simpType categorySimp' e'
  return (e, [v₂, u₂])

syntax (name := functor_map) "functor_map" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `functor_map
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| functor_map $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`functor_map` can only be used as a global attribute"
    addRelatedDecl src "_functor_map" ref stx? fun type value levels => do
      let (e, levels') ← functorMapExpr (← mkExpectedTypeHint value type) true
      pure (e, levels ++ levels'.map fun | .param n => n | _ => panic! "")
  | _ => throwUnsupportedSyntax }

open Term in
elab "functor_map_of% " t:term : term => do
  Prod.fst <$> functorMapExpr (← elabTerm t none) false

end CategoryTheory
