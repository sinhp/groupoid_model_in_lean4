import Lean.Elab.Command

open Lean Meta Elab Term Command

/-- For all `i < n`,
sample `i` sequential applications of an identity lambda to `Type`,
named `benchDef_id_<i>`.
For example,
```
def benchDef_id_2 : Type 1 :=
  (fun (x : Type 1) => x) ((fun (x : Type 1) => x) Type)
``` -/
elab "#sample_ids" n:num : command => liftTermElabM do
  let idFn := Expr.lam `x (.sort 2) (.bvar 0) default
  let mut acc := .sort 1 -- Type 0
  for i in [0 : n.getNat] do
    let name : Name := Name.anonymous.str s!"benchDef_id_{i}"
    if i != 0 then do
      acc := .app idFn acc
    -- let accPP ← ppExpr acc
    -- logInfo m!"acc[{i}] := {accPP}"
    addDecl <| .defnDecl
      { name,
        levelParams := [],
        type := ← inferType acc,
        value := acc,
        hints := default
        safety := .safe }
