import Lean.Meta.Tactic

/-! ## Mutual induction

A rudimentary mutual induction tactic. Written with Claude Sonnet 4 assistance. -/

open Lean Elab Meta Tactic

partial def splitConjunctions (mvarId : MVarId) (type : Expr) : MetaM (List MVarId) := do
  let type ← instantiateExprMVars (← whnf type)
  let_expr And P Q := type | return [mvarId]
  let pfP ← mkFreshExprMVar P (kind := .synthetic)
  let pfQ ← mkFreshExprMVar Q (kind := .synthetic)
  let pf ← mkAppM ``And.intro #[pfP, pfQ]
  mvarId.assign pf
  let left ← splitConjunctions pfP.mvarId! P
  let right ← splitConjunctions pfQ.mvarId! Q
  return left ++ right

/-
TODOs:
- auto-solve the `True` goals
- add automatic abstraction of non-bvar indices:
  intro equation, apply recursor, elim equation
- better UX: operate on multiple goals like
  `mutual_induction | case1 => h generalizing w | case2 => h'`
-/

partial def elabMutualInduction (A : Ident) : TacticM Unit := withMainContext do
  -- Find `A`; it must belong to a mutual inductive family.
  let nmA ← realizeGlobalConstNoOverloadWithInfo A
  let iA ← getConstInfo nmA
  let .inductInfo iA := iA | throwErrorAt A "expected the name of an inductive type"
  if iA.all.length < 2 then throwErrorAt A "expected the name of a mutual inductive type"

  -- Map each type in the family to a metavariable
  -- to be filled in with the motive for that type.
  let mut typeToMotive : Std.HashMap Name MVarId := {}
  let .recInfo iRec ← getConstInfo (mkRecName iA.all[0]!) | throwError "internal error"
  let lvls ← mkFreshLevelMVars iRec.levelParams.length
  let tp := iRec.type.instantiateLevelParams iRec.levelParams lvls
  -- Introduce mvars for the parameters; unification will ensure they match up between motives.
  let (_, _, tp) ← forallMetaBoundedTelescope tp iRec.numParams
  let (ms, _, tp) ← forallMetaBoundedTelescope tp iRec.numMotives
  -- We assume the recursor's motives and `InductiveVal.all` are ordered identically.
  for i in [:iA.all.length] do
    typeToMotive := typeToMotive.insert iA.all[i]! ms[i]!.mvarId!

  -- Split a conjunction goal into subgoals.
  let g ← getMainGoal
  let goals ← splitConjunctions g (← g.getType)

  -- For a goal of the form `∀ (…), Foo … → B`,
  -- where `Foo …` is the first premise that belongs to the mutual inductive family,
  -- return `λ (…) (x : Foo …), B`.
  let rec lambdafyGoal (g : MVarId) (tp : Expr) : MetaM Expr :=
    forallBoundedTelescope tp (some 1) fun
      | #[x], tp => do
        let xTp ← inferType x
        if iA.all.any (xTp.isAppOf ·) then
          mkLambdaFVars #[x] tp
        else
          let r ← lambdafyGoal g tp
          mkLambdaFVars #[x] r
      | _, _ => throwError "goal has no premise in family '{nmA}'{indentD g}"

  -- Map each type in the family to the goal it solves.
  let mut typeToGoal : Std.HashMap Name MVarId := {}
  for g in goals do
    let gTp ← g.getType
    let motive ← lambdafyGoal g gTp
    let motiveTp ← inferType motive
    -- FIXME: quadratic loop
    let mut done := false
    for nm in iA.all do
      let m := typeToMotive[nm]!
      let mTp ← m.getType
      if ← isDefEq mTp motiveTp then
        if let some (g' : MVarId) := typeToGoal[nm]? then
          throwError m!"multiple goals eliminate '{nm}':{indentD g}and{indentD g'}"
        -- Assign `m := motive`
        let _ ← isDefEq (Expr.mvar m) motive
        typeToGoal := typeToGoal.insert nm g
        done := true
        continue
    if !done then
      throwError "goal matches no recursor motive{indentD g}"

  -- The remaining types have no goal; set those motives to `fun .. => True`.
  for nm in iA.all do
    if !typeToGoal.contains nm then
      let m := typeToMotive[nm]!
      let mTp ← m.getType
      let trueMotive ← forallTelescopeReducing mTp fun xs _ => do
        mkLambdaFVars xs (← mkAppM ``True #[])
      let _ ← isDefEq (Expr.mvar m) trueMotive

  -- Create goals for the recursors' premises (identical across recursors),
  -- and assign each conjunct to the corresponding recursion.
  let (indGoals, _, _) ← forallMetaBoundedTelescope tp iRec.numMinors
  for nm in iA.all do
    let some g := typeToGoal[nm]? | continue
    let .recInfo iRec ← getConstInfo (mkRecName nm) | throwError "internal error"
    let mut args := Array.range iRec.numParams |>.map fun _ => none
    for nm in iA.all do
      args := args.push (some <| Expr.mvar typeToMotive[nm]!)
    args := args ++ indGoals.map some
    let pf ← mkAppOptM iRec.name args
    g.assign pf

  -- Set the goals to be recursion premises.
  setGoals <| indGoals.toList.map (·.mvarId!)

/-- `mutual_induction Foo` eliminates the mutual inductive family that `Foo` is part of. -/
elab "mutual_induction" A:ident : tactic => elabMutualInduction A
