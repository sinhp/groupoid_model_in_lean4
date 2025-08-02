import Qq

namespace Qq

open Lean Meta

def withLetDeclQ {n : Type → Type} {u : Level} {α : Type} [Monad n] [MonadControlT MetaM n]
    (name : Name) (type : Q(Sort u)) (val : Q($type)) (k : (v : Q($type)) → $v =Q $val → n α)
    (nondep : Bool := false) (kind : LocalDeclKind := .default) : n α :=
  withLetDecl name type val (fun x => k x .unsafeIntro) nondep kind

def mkLetFVarsQ {u : Level} {T : Q(Sort u)} (xs : Array Lean.Expr) (e : Q($T))
    (usedLetOnly := true) (generalizeNondepLet := true)
    (binderInfoForMVars := BinderInfo.implicit) : MetaM Q($T) :=
  mkLetFVars xs e (usedLetOnly := usedLetOnly) (generalizeNondepLet := generalizeNondepLet)
    (binderInfoForMVars := binderInfoForMVars)

end Qq

open Qq

def equateNat (n m : Q(Nat)) : Lean.MetaM Q($n = $m) := do
  let some vn ← Lean.Meta.evalNat (← Lean.Meta.whnf n)
    | throwError "cannot evaluate Nat{Lean.indentExpr n}"
  let some vm ← Lean.Meta.evalNat (← Lean.Meta.whnf m)
    | throwError "cannot evaluate Nat{Lean.indentExpr m}"
  if vm != vn then throwError "equality does not hold{Lean.indentD ""}{n} = {m}"
  Lean.Meta.mkEqRefl n

def ltNat (n m : Q(Nat)) : Lean.MetaM Q($n < $m) := do
  let some vn ← Lean.Meta.evalNat (← Lean.Meta.whnf n)
    | throwError "cannot evaluate Nat{Lean.indentExpr n}"
  let some vm ← Lean.Meta.evalNat (← Lean.Meta.whnf m)
    | throwError "cannot evaluate Nat{Lean.indentExpr m}"
  if vm <= vn then throwError "inequality does not hold{Lean.indentD ""}{n} < {m}"
  let pf ← Lean.Meta.mkEqRefl q(decide ($n < $m))
  Lean.Meta.mkAppM ``of_decide_eq_true #[pf]

-- /-- Hacks to use during development:
-- `as_aux_lemma` blocks are not elaborated and kernel typechecking is off,
-- speeding up interactive feedback. -/
-- -- FIXME: make `as_aux_lemma` or general `by` elaboration async for lower interaction latency.
-- macro_rules
--   | `(tactic| as_aux_lemma => $s:tacticSeq) => `(tactic| sorry)
-- set_option linter.unusedTactic false
-- set_option linter.unreachableTactic false
-- set_option debug.skipKernelTC true
