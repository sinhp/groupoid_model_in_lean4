import HoTTLean.Model.Unstructured.InternalTheory
import HoTTLean.Frontend.Shallow
import HoTTLean.Frontend.Translation

/-! Elaborators for `tp%{..}`, `tm%{..}`, and `⸨..⸩`. -/

namespace SynthLean

open Qq
open Lean Meta Elab Term
open CategoryTheory ChosenTerminal
open Model UnstructuredUniverse

-- inductive ExpectedTheory {u : Level} (χ : Q(Type u))

structure ElabData where
  lctx : LocalContext
  linsts : LocalInstances
  u : Level
  χ : Q(Type u)
  E : Q(Axioms $χ)

private abbrev ElabExt := EnvExtension (Option ElabData)

/-- When elaborating terms such as `tm%{t ⸨u⸩}`,
we must communicate some information (e.g. which theory is in use)
from the outer `tm%{..}` elaborator to the inner `⸨..⸩` elaborator
(the term `t ⸨u⸩` is processed using Lean's default `elabTerm`,
so we can't just call something with the right argument).
`CoreM` is only extensible through environment extensions,
so we use one to communicate this data.

It would alternatively be possible for `tm%{..}` to traverse its argument
and preprocess occurrences of `⸨..⸩`
(this is what `quote4` does with antiquotations like `q(t $(u))`),
but the present implementation strategy appears more straightforward. -/
initialize elabExt : ElabExt ← registerEnvExtension (pure none)

/-- Identify the signature and theory
that a `tp%/tm% (theory := thy)` expression is expected to elaborate into. -/
def elabExpectedTheory (thy : Option Term) (expectedType : Lean.Expr) :
    TermElabM ((u : Level) × (χ : Q(Type u)) × Q(Axioms $χ)) := do
  let v ← mkFreshLevelMVar
  let χ ← mkFreshExprMVarQ q(Type v)
  if let some thy := thy then
    let E ← elabTermEnsuringTypeQ thy q(Axioms $χ)
    return ⟨v, q($χ), q($E)⟩
  -- This may assign the expected type.
  if !(← isDefEq expectedType q(SynthLean.Expr $χ)) then
    throwError "This macro produces a SynthLean expression. \
      The expected type must be of the form{indentExpr q(SynthLean.Expr $χ)}"
  let u ← mkFreshLevelMVar
  let 𝒞 ← mkFreshExprMVarQ q(Type u)
  let _cat ← mkFreshExprMVarQ q(Category.{v,u} $𝒞)
  let _ct ← mkFreshExprMVarQ q(ChosenTerminal.{v,u} $𝒞)
  let s ← mkFreshExprMVarQ q(UHomSeq $𝒞)
  if ← isDefEq χ q(($s).SigInt) then
    if !(← instantiateMVars s).hasMVar then
      return ⟨v, q(($s).SigInt), q(($s).thyInt)⟩
  throwError "Could not infer the theory from the expected type. \
  Please provide (theory := ..) explicitly."

-- TODO: term expressions
/-- Elaborate a SynthLean type expression.

## Expected theory

This elaborator needs to know the *expected theory*
w.r.t. which the expression should be typechecked.
When the optional `(theory := thy)` argument is provided, the expected theory is `thy`.
Otherwise the expected theory is inferred from the expected type `eT`:
- When `eT = SynthLean.Expr s.SigInt` for `s : UHomSeq 𝒞`,
  the expected theory is `s.thyInt`. -/
-- TODO: Infer `computeAxioms` when `eT = SynthLean.Expr Lean.Name`?
elab "tp%" thy:group("(" "theory" ":=" term ")")? "{" t:term "}" : term <= expectedType => do
  let thy := thy.map (⟨·.raw[3]⟩)
  let ⟨u, χ, E⟩ ← elabExpectedTheory thy expectedType
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  modifyEnv (elabExt.modifyState · fun _ => some ⟨lctx, linsts, u, χ, E⟩)
  let t ← withLCtx {} {} <| elabTerm t none
  let (_, T) ←
    try translateAsTp (u := u) χ t |>.run E
    catch e =>
      throwError "failed to translate type{Lean.indentExpr t}\nerror: {e.toMessageData}"
  return T

/-- *Deinterpretation* `⸨..⸩` (the *Scott unbracket*) works in any `tm%{..}/tp%{..}` context
where the expected theory is `s.thyInt`.
It allows us to name a semantic constant in the syntax
(so, in a sense, it is inverse to interpretation `⟦..⟧`).
It obeys the following rule,
where `⊢ᵢ` is the internal typing judgment,
and `⊢` is Lean's usual typing.
```
Γ ⊢ t ⇐ 𝟭_ _ ⟶ s[u].Tm
-----------------------
· ⊢ᵢ ⸨t⸩ ⇐ Type u
``` -/
-- TODO: demand that `t` have a certain semantic type.
elab "⸨" t:term "⸩" : term <= expectedType => do
  let some elabData := elabExt.getState (← getEnv)
    | throwError "The `⸨..⸩` macro can only appear inside `tp%` or `tm%` macros."
  let .sort (.succ w) ← inferType expectedType
    | throwError "The expected type must be of the form `Type u`. \
      Try an explicit annotation like `(⸨..⸩ : Type 0)`."
  if w.hasMVar then
    throwError "The expected type {Expr.sort w.succ} contains metavariables."

  let { lctx, linsts, u := v, χ, E } := elabData

  withLCtx lctx linsts do
    let u ← mkFreshLevelMVar
    let 𝒞 : Q(Type u) ← mkFreshExprMVarQ q(Type u)
    let _cat : Q(Category.{v,u} $𝒞) ← mkFreshExprMVarQ q(Category.{v,u} $𝒞)
    let _ct : Q(ChosenTerminal.{v,u} $𝒞) ← mkFreshExprMVarQ q(ChosenTerminal.{v,u} $𝒞)
    let s : Q(UHomSeq $𝒞) ← mkFreshExprMVarQ q(UHomSeq $𝒞)
    if !(← isDefEq E q(($s).thyInt)) then
      throwError "The expected theory should be of the form{indentExpr q(($s).thyInt)}\n\
        but is{indentExpr E}"

    let l ← getSortLevel w
    have l : Q(ℕ) := toExpr l
    let lt ← ltNat q($l) q(univMax)
    let extExpectedType := q(𝟭_ _ ⟶ $s[$l].Tm)
    let t ← elabTermEnsuringTypeQ t extExpectedType

    let st : Q(($s).SigInt) := q(UHomSeq.SigInt.tm.{v,u} (by get_elem_tactic) $t)
    let qt : Q(Lean.Expr) := @toExpr Lean.Expr _ st
    let expectedType : Q(Type w) := expectedType
    return q(SemAx $expectedType $qt)

end SynthLean
