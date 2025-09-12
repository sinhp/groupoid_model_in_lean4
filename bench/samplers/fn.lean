import Lean.Elab.Command

open Lean Meta Elab Term Command

/-- For all `i < n`,
sample `i` lambda binders on top of the constant `Type`,
named `benchDef_fn_<i>`.
For example,
```
def benchDef_fn_2 : Type → Type → Type 1 :=
  fun (_ : Type) => fun (_ : Type) => Type
``` -/
elab "#sample_fns" n:num : command => liftTermElabM do
  let mut acc := .sort 1 -- Type 0
  for i in [0 : n.getNat] do
    let name : Name := Name.anonymous.str s!"benchDef_fn_{i}"
    if i != 0 then do
      acc := .lam `x (.sort 1) acc default
    -- let accPP ← ppExpr acc
    -- logInfo m!"acc[{i}] := {accPP}"
    addDecl <| .defnDecl
      { name,
        levelParams := [],
        type := ← inferType acc,
        value := acc,
        hints := default
        safety := .safe }
