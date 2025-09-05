import Lean.Elab.Command

open Lean Meta Elab Term Command

/-- For all `i < n`, creates a definition:
  `benchDef_prod_i : Type 1 := ...`

The definitions build nested products where:
- `benchDef_prod_0 = Type`
- `benchDef_prod_1 = (_ : Type) × Type`
- `benchDef_prod_2 = (_ : Type) × (_ : Type) × Type`
- And so on... -/
elab "#sample_prods" n:num : command => liftTermElabM do
  let mut acc := Expr.sort 1
  for i in [0 : n.getNat] do
    let name : Name := Name.str .anonymous s!"benchDef_prod_{i}"
    if i != 0 then do
      let prod := Lean.mkConst ``Sigma [1, 1]
      acc := mkAppN prod #[Expr.sort 1, .lam default (.sort 1) acc default]
    -- let type ← inferType acc
    -- logInfo m!"benchDef_prod_{i} : {← ppExpr type} := {← ppExpr acc}"
    addDecl <| Declaration.defnDecl
      { name,
        levelParams := [],
        type := ← inferType acc
        value := acc
        hints := default
        safety := .safe }
