import Lean.Meta.Tactic
import Lean.Meta.Tactic.Grind

open Lean Elab Meta Tactic

def elabGrindCases : TacticM Unit := withMainContext do
  let gs ← getGoals
  let mut gs' := []
  for g in gs do
    let fn ← g.withContext do
      let tp ← g.getType
      forallTelescopeReducing tp (whnfType := true) fun _ tp =>
        return tp.getAppFn'
    let some (tpNm, _) := fn.const? |
      gs' := g :: gs'
      continue
    let nm ← g.getTag
    let ctrNm := tpNm ++ nm
    if ← hasConst ctrNm then
      let arg : TSyntax ``Parser.Tactic.grindParam :=
        ⟨.node default ``Parser.Tactic.grindParam #[
          .node default ``Parser.Tactic.grindLemma #[
            mkNullNode, mkIdent ctrNm
          ]
        ]⟩
      let tac ← `(tactic| try grind [$arg])
      let [] ← evalTacticAt tac g |
        gs' := g :: gs'
        continue
    else
      let tac ← `(tactic| try grind)
      let [] ← evalTacticAt tac g |
        gs' := g :: gs'
        continue
  setGoals gs'

/-- Looks at the `case l` label of each goal
and tries to solve it by `grind [Foo.l]`
where `Foo` is the head of the goal type,
possibly under a telescope of universal quantifiers. -/
elab "grind_cases" : tactic => elabGrindCases
