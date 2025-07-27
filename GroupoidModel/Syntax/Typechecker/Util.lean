import Qq

namespace Qq

open Lean Meta

def withLetDeclQ {n : Type → Type} {u : Level} {α : Type} [Monad n] [MonadControlT MetaM n]
    (name : Name) (type : Q(Sort u)) (val : Q($type)) (k : (v : Q($type)) → $v =Q $val → n α)
    (nondep : Bool := false) (kind : LocalDeclKind := .default) : n α :=
  withLetDecl name type val (fun x => k x .unsafeIntro) nondep kind

def mkLetFVarsQ {u : Level} {T : Q(Sort u)} (xs : Array Lean.Expr) (e : Q($T))
    (usedLetOnly := true) (generalizeNondepLet := true)
    (binderInfoForMVars := BinderInfo.implicit) : MetaM Lean.Expr :=
  mkLetFVars xs e (usedLetOnly := usedLetOnly) (generalizeNondepLet := generalizeNondepLet)
    (binderInfoForMVars := binderInfoForMVars)

end Qq

open Qq

def equateNat (n m : Q(Nat)) : Lean.MetaM Q($n = $m) := do
  let some vn ← Lean.Meta.evalNat n | throwError "cannot evaluate{Lean.indentExpr n}"
  let some vm ← Lean.Meta.evalNat m | throwError "cannot evaluate{Lean.indentExpr m}"
  if vm != vn then throwError "equality does not hold{Lean.indentD ""}{n} = {m}"
  Lean.Meta.mkEqRefl n

def ltNat (n m : Q(Nat)) : Lean.MetaM Q($n < $m) := do
  let some vn ← Lean.Meta.evalNat n | throwError "cannot evaluate{Lean.indentExpr n}"
  let some vm ← Lean.Meta.evalNat m | throwError "cannot evaluate{Lean.indentExpr m}"
  if vm <= vn then throwError "inequality does not hold{Lean.indentD ""}{n} < {m}"
  let pf ← Lean.Meta.mkEqRefl q(decide ($n < $m))
  Lean.Meta.mkAppM ``of_decide_eq_true #[pf]

/-- Continue with a `have` declaration in the local context.

Introducing `have`s is crucial for obtaining proofs
whose size is linear rather than exponential
in the length of the computation trace.

For example,
```lean
let p : Q(P) := q(..)
let q : Q(Q) := q(..[$p])
let r : Q(R) := q(..[$p])
let s : Q(S) := q(..[$q, $r])
```
will have the full proof term `p` occur in `s`
as many times as the sum of its occurrences in `q` and `r`.

IDEA: `withHave` is syntactically heavy.
Instead, we could write the typechecker in CPS style,
e.g. `withEvalTp` instead of `evalTp`.
Also, `withEvalTp` could then introduce `let`-bindings
that would be bound by the _caller_ (but this might not be useful). -/
def withHave {α : Type} {P : Q(Prop)} (pf : Q($P)) (k : Q($P) → Lean.MetaM α) : Lean.MetaM α :=
  withLetDeclQ `pf _ pf (fun x _ => k x) (nondep := true)

def mkHaves {P : Q(Prop)} (xs : Array Lean.Expr) (e : Q($P)) : Lean.MetaM Q($P) :=
  mkLetFVarsQ xs e (generalizeNondepLet := false)

-- /-- Hacks to use during development:
-- `as_aux_lemma` blocks are not elaborated and kernel typechecking is off,
-- speeding up interactive feedback. -/
-- -- FIXME: make `as_aux_lemma` or general `by` elaboration async for lower interaction latency.
-- macro_rules
--   | `(tactic| as_aux_lemma => $s:tacticSeq) => `(tactic| sorry)
-- set_option linter.unusedTactic false
-- set_option linter.unreachableTactic false
-- set_option debug.skipKernelTC true
