import Canonical.Main
import GroupoidModel.Syntax.Frontend.Prelude

open Canonical Lean Elab Term Command Meta

/-- Increment an m-ary number. Thanks Claude! -/
def incMAry (n : Array Nat) (m : Nat) : Array Nat × Bool :=
  if m <= 1 then (n, false)
  else go n 0
  where
    go (arr : Array Nat) (i : Nat) : Array Nat × Bool :=
      if h : i < arr.size then
        let digit := arr[i]
        let newDigit := digit + 1
        if newDigit < m then
          (arr.set i newDigit, false)
        else
          let arr' := arr.set i 0
          go arr' (i + 1)
      else
        (arr.push 1, true)

/-- Canonical outputs contain underconstrained universe mvars.
This function fills them in.
It takes an extremely naïve approach: try all combinations of levels up to `maxLvl`.
If `all = true`, it returns all combinations that work;
otherwise, it returns the first one. -/
def instLevels (maxLvl : Nat) (e : Expr) (all : Bool := false) : MetaM (List Expr) := do
  -- First replace any `Sort ?u` by `Type ?u` (we don't support `Prop`).
  let e := e.replace fun
    | .sort (.mvar l) => some <| .sort <| mkLevelSucc <| .mvar l
    | _ => none
  let mut lvls := collectLevelMVars {} e |>.result
  let mut attempt := Array.replicate lvls.size 0
  let mctx ← getMCtx
  let mut carry := false
  let mut ret := []
  while 0 < lvls.size && !carry do
    setMCtx mctx
    for _h : iLvl in [0:attempt.size] do
      assignLevelMVar lvls[iLvl]! (.ofNat attempt[iLvl])
    if ← isTypeCorrect e then
      let e ← instantiateMVars e
      ret := e :: ret
      if !all then return ret
    (attempt, carry) := incMAry attempt maxLvl
  return ret

axiom app.{u,v} {A : Type u} {B : A → Type v} (f : (a : A) → B a) (a : A) : B a
axiom fst.{u,v} {A : Type u} {B : A → Type v} (p : (a : A) × B a) : A
axiom snd.{u,v} {A : Type u} {B : A → Type v} (p : (a : A) × B a) : B (fst p)
axiom idRec.{v,u} {A : Type u} (t : A) (M : (y : A) → Identity t y → Type v)
    (r : M t (.refl t)) (u : A) (h : Identity t u) : M u h

/-- Turn the axioms above into definable terms. -/
partial def deaxiomatize : Expr → Expr :=
  Expr.replace fun e =>
    match_expr e with
    | app _ _ f a =>
      let f := deaxiomatize f
      let a := deaxiomatize a
      return .app f a
    | fst α β p =>
      let α := deaxiomatize α
      let β := deaxiomatize β
      let p := deaxiomatize p
      let ls := e.getAppFn'.constLevels!
      return mkApp3 (.const ``Sigma.fst ls) α β p
    | snd α β p =>
      let α := deaxiomatize α
      let β := deaxiomatize β
      let p := deaxiomatize p
      let ls := e.getAppFn'.constLevels!
      return mkApp3 (.const ``Sigma.snd ls) α β p
    | idRec _ t M r u h => Id.run do
      let t := deaxiomatize t
      let M := deaxiomatize M
      let r := deaxiomatize r
      let u := deaxiomatize u
      let h := deaxiomatize h
      let [ℓ₁, ℓ₂] := e.getAppFn'.constLevels! | return none
      -- `idRec` has a motive that eliminates into `Type`,
      -- whereas `Identity.rec` eliminates into `Sort`
      -- so bump the level by one.
      return mkApp5 (.const ``Identity.rec [mkLevelSucc ℓ₁, ℓ₂]) t M r u h
    | _ => none

/-- Samples n terms of the given type using Canonical. -/
elab "#sample" maxLvl:num n:num m:num : command => liftTermElabM do
  let config := {
    count := n.getNat.toUSize /- sample `n` types -/
    simp := false /- prevents adding extra definitions like `Eq.rec` -/
  }
  -- We sample NF types built out of Π/Σ/Id
  let premises := #[ ``Canonical.Pi, ``Sigma, ``Identity ]
  -- Canonical has `Sort : Sort` and the level is ignored.
  let typ ← toCanonical (.sort 0) premises config
  -- dbg_trace typ
  let result ← canonical typ config.count.toUInt64 config.count
  let tps ← result.terms.mapM fun term => fromCanonical term (.sort 0)
  for _h : iTp in [0:tps.size] do
    let tp := tps[iTp]
    withLogging do
    let config := { config with count := m.getNat.toUSize /- sample `m` terms -/ }
    -- We sample terms that may use eliminators
    let premises := premises ++ #[
      ``Canonical.Pi.f,  ``app,
      ``Sigma.mk, ``fst, ``snd,
      ``Identity.refl, ``idRec
    ]
    let typ ← toCanonical tp premises config
    -- dbg_trace typ
    -- -- TODO: smaller timeout?
    let result ← canonical typ config.count.toUInt64 config.count
    let tms ← result.terms.mapM fun term => fromCanonical term tp
    for _h : iTm in [0:tms.size] do
      let tm := tms[iTm]
      let tm := deaxiomatize tm

      let tms ← instLevels maxLvl.getNat tm (all := true)
      for _h : iTmInst in [0:tms.length] do
        let tm := tms[iTmInst]
        let name := `benchDef |>.num iTp |>.num iTm |>.num iTmInst
        addDecl <| .defnDecl {
          name
          levelParams := []
          type := ← inferType tm -- not guaranteed to have type `tp`
          value := tm
          hints := default
          safety := default
        }
        logInfo m!"added {name} := {tm}"

-- Hack: `instLevels` tends to run out of heartbeats
set_option pp.universes true in
set_option maxHeartbeats 0 in
#sample 3 3 1
