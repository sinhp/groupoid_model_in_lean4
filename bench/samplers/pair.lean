import Lean.Elab.Command

open Lean Meta Elab Term Command

/-- For all `i < n`, creates a definition:
  `benchDef_pair_i := fun x ↦ ...`

The definitions build nested pairs where:
- `benchDef_pair_0 := fun x ↦ ⟨x, x⟩` (base case)
- `benchDef_pair_1 := fun x ↦ ⟨x, ⟨x, x⟩⟩`
- `benchDef_pair_2 := fun x ↦ ⟨x, ⟨x, ⟨x, x⟩⟩⟩`
- And so on...

Each definition adds one more level of nesting to the previous pair structure.
-/
elab "#sample_pairs" n:num : command => liftTermElabM do
  let sigma_mk := Lean.mkConst ``Sigma.mk [1, 1]
  let mut tm := mkAppN sigma_mk #[.sort 1, .lam default (.sort 1) (.sort 1) default, (.bvar 0), (.bvar 0)]
  let mut pair := Expr.lam `x (.sort 1) tm default
  for i in [0 : n.getNat] do
    let name : Name := Name.anonymous.str s!"benchDef_pair_{i}"
    if i != 0 then do
      let tm_type := ← inferType tm
      tm := mkAppN sigma_mk #[.sort 1, .lam default (.sort 1) tm_type default, (.bvar 0), tm]
      pair := Expr.lam `x (.sort 1) tm default
    -- let pairPP := ← ppExpr pair
    -- logInfo m!"benchDef_pair_{i} := {pairPP}"
    addDecl <| .defnDecl
      { name,
        levelParams := [],
        type := ← inferType pair,
        value := pair,
        hints := default
        safety := .safe }
