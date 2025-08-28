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

universe u v
axiom app {A : Type u} {B : A → Type v} (f : (a : A) → B a) (a : A) : B a
axiom fst {A : Type u} {B : A → Type v} (p : (a : A) × B a) : A
axiom snd {A : Type u} {B : A → Type v} (p : (a : A) × B a) : B (fst p)
axiom idRec {A : Type u} (t : A) (M : (y : A) → Identity t y → Type v) (r : M t (.refl t)) (u : A)
    (h : Identity t u) : M u h

/-- Samples n terms of the given type using Canonical. -/
elab "#sample" maxLvl:num n:num m:num : command => liftTermElabM do
  let config := {
    count := n.getNat.toUSize /- sample `n` types -/
    simp := false /- prevents adding extra definitions like `Eq.rec` -/
  }
  let premises := #[
    ``Canonical.Pi, ``Canonical.Pi.f, ``app,
    ``Sigma.mk, ``fst, ``snd,
    ``Identity.refl, ``idRec
  ]
  -- Canonical has `Sort : Sort` and the level is ignored.
  let typ ← toCanonical (.sort 0) premises config
  -- dbg_trace typ
  let result ← canonical typ config.count.toUInt64 config.count
  let tps ← result.terms.mapM fun term => fromCanonical term (.sort 0)
  for _h : iTp in [0:tps.size] do
    let tp := tps[iTp]
    -- We pass this type back to canonical; because canonical ignores universe levels,
    -- we only need one instantiation.
    let [tp] ← instLevels maxLvl.getNat tp | continue

    let config := { config with
      count := m.getNat.toUSize /- sample `m` terms -/
    }
    let typ ← toCanonical tp premises config
    -- dbg_trace typ
    -- TODO: smaller timeout?
    let result ← canonical typ config.count.toUInt64 config.count
    let tms ← result.terms.mapM fun term => fromCanonical term tp
    for _h : iTm in [0:tms.size] do
      let tm := tms[iTm]
      let tms ← instLevels maxLvl.getNat tm (all := true)
      for _h : iTmInst in [0:tms.length] do
        let tm := tms[iTmInst]
        let name := `benchDef |>.num iTp |>.num iTm |>.num iTmInst
        logInfo m!"found {name} := {tm}"
        addDecl <| .defnDecl {
          name
          levelParams := []
          type := ← inferType tm -- not guaranteed to have type `tp`
          value := tm
          hints := default
          safety := default
        }

#sample 2 5 5
