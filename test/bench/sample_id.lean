import Lean.Elab.Command
import bench.sample_llm

open Lean Meta Elab Term Command

partial def IterId (x : Expr) (i : Nat) : MetaM Expr := do
  let mut acc := x
  for _ in [:i] do
    acc ← mkAppM' (mkConst ``id) #[acc]
  return acc

open Char
def isSampleBenchDef (n : Name) : Bool :=
  match n with
  | .str (.str _ s1) s2 =>
    -- components come as: ... → "sample<n>" (s1) ← "benchDef_<m>" (s2) ← _ (rest)
    let ok1 := s1.startsWith "sample"
      && isDigit ((s1.drop 6).get 0)
    let ok2 := s2.startsWith "benchDef_"
      && isDigit ((s2.drop 9).get 0)
    ok1 && ok2
  | _ => false

elab "#gen_id" num:num : command => liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants do
    if !isSampleBenchDef n then continue
    let .defnInfo d := ci | continue
    try
      for i in [0 : num.getNat] do
        let name : Name := n ++ Name.str .anonymous s!"id_{i}"
        let mut acc := d.value
        if i != 0 then do acc ← mkAppM ``id #[acc] --mkAppM' (mkConst ``id) #[acc]
        addDecl <| .defnDecl
          { name,
            levelParams := d.levelParams,
            type := d.type,
            value := acc,
            hints := d.hints
            safety := d.safety }

    catch ex =>
      logInfo m!"gen_id error :\n{ex.toMessageData}"
      continue

#gen_id 40
