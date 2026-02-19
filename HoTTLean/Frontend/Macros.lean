import HoTTLean.Model.Unstructured.InternalTheory
import HoTTLean.Frontend.Shallow
import HoTTLean.Frontend.Translation

/-! Elaborators for `tp%{..}`, `tm%{..}`, and `⸨..⸩`. -/

namespace SynthLean

open Qq
open Lean Meta Elab Term
open CategoryTheory ChosenTerminal
open Model UnstructuredUniverse

inductive ExpectedTheory : {u : Level} → Q(Type u) → Type
  | internal {u : Level} (𝒞 : Q(Type u))
    {v : Level} (cat : Q(Category.{v, u} $𝒞)) (ct : Q(ChosenTerminal.{v,u} $𝒞))
    (s : Q(UHomSeq $𝒞)) : ExpectedTheory q(($s).SigInt)
  | other {u : Level} {χ : Q(Type u)} (E : Q(Axioms $χ)) : ExpectedTheory q($χ)

def ExpectedTheory.theory {u : Level} : {χ : Q(Type u)} → ExpectedTheory q($χ) → Q(Axioms $χ)
  | _, .internal _ _ _ s => q(($s).thyInt)
  | _, .other E => q($E)

structure ElabData where
  lctx : LocalContext
  linsts : LocalInstances
  u : Level
  χ : Q(Type u)
  E : ExpectedTheory q($χ)

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
but the present implementation strategy appears more straightforward.

For those who know Fitch-style modal type theory:
this is basically a janky implementation of context locking. -/
initialize elabExt : ElabExt ← registerEnvExtension (pure none)

/-- Identify the signature and theory that a `tp%/tm% (theory := thy)` expression should target. -/
-- TODO: Infer `computeAxioms` when `eT = SynthLean.Expr Lean.Name`?
def elabExpectedTheory (thy : Option Term) (expectedType : Lean.Expr) :
    TermElabM ((u : Level) × (χ : Q(Type u)) × ExpectedTheory q($χ)) := do
  let v ← mkFreshLevelMVar
  let χ ← mkFreshExprMVarQ q(Type v)
  if let some thy := thy then
    let E ← elabTermEnsuringTypeQ thy q(Axioms $χ)
    let u ← mkFreshLevelMVar
    let 𝒞 : Q(Type u) ← mkFreshExprMVarQ q(Type u)
    let _cat : Q(Category.{v,u} $𝒞) ← mkFreshExprMVarQ q(Category.{v,u} $𝒞)
    let _ct : Q(ChosenTerminal.{v,u} $𝒞) ← mkFreshExprMVarQ q(ChosenTerminal.{v,u} $𝒞)
    let s : Q(UHomSeq $𝒞) ← mkFreshExprMVarQ q(UHomSeq $𝒞)
    if ← isDefEq E q(($s).thyInt) then
      return ⟨v, q(($s).SigInt), .internal q($𝒞) q($_cat) q($_ct) q($s)⟩
    else
      return ⟨v, q($χ), .other q($E)⟩
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
      return ⟨v, q(($s).SigInt), .internal q($𝒞) q($_cat) q($_ct) q($s)⟩
  throwError "Could not infer the theory from the expected type. \
  Please provide (theory := ..) explicitly."

elab_rules : term <= expectedType | `(tp% $[$thy:theorySpec]? {$t}) => do
  let thy := thy.map (⟨·.raw[3]⟩)
  let ⟨u, χ, E⟩ ← elabExpectedTheory thy expectedType
  let env ← getEnv
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  let t ←
    withEnv (elabExt.modifyState env fun _ => some ⟨lctx, linsts, u, χ, E⟩) <|
    -- FIXME: Would be really cool to also display the locked,
    -- external context in the tactic state.
    withLCtx {} {} <|
    -- Ensure that infotrees store the `elabExt`.
    withSaveInfoContext do
      -- TODO: Need to also deal with mctx?
      let w ← mkFreshLevelMVar
      elabTermEnsuringType t (some <| .sort (.succ w))
  let (_, T) ←
    try translateAsTp (u := u) χ t |>.run E.theory
    catch e =>
      throwError "Failed to translate type{Lean.indentExpr t}\nError: {e.toMessageData}"
  return T

-- TODO: term expressions

elab_rules : term <= expectedType | `(⸨$t_stx⸩) => do
  let w ← mkFreshLevelMVar
  if !(← isDefEq expectedType (.sort (.succ w))) then
    throwError "Expected a term of type{indentExpr expectedType}\n\
    but got{indentD ""}⸨..⸩ : {Expr.sort (.succ w)}"

  let some elabData := elabExt.getState (← getEnv)
    | throwError "The `⸨..⸩` macro can only appear inside `tp%` or `tm%` macros."
  let { lctx, linsts, E := .internal (u := u) (v := v) _ _ _ s, .. } := elabData
    | throwError "The `⸨..⸩` macro can only be used in the internal theory of a model."

  -- expected Type is one of P : Sort 0 : Type 0 : Type 1
  -- h : P : Sort 0 : Type 0 : Type 1
  withEnv (elabExt.modifyState (← getEnv) fun _ => none) do
  -- Reinstate the external local context and instances.
  withLCtx lctx linsts do
  -- Ensure that infotrees store the `elabExt`.
  withSaveInfoContext do
    let l ← mkFreshExprMVarQ q(ℕ)
    let _lt ← mkFreshExprMVarQ q($l < ($s).length + 1)
    let t ← elabTermEnsuringTypeQ t_stx q(𝟭_ _ ⟶ $s[$l].Ty)

    -- FIXME: how should we external/internal mvars, in particular in `l`/`w`?
    -- Can we postpone here, wait until `l`/`w` are concrete,
    -- and then unify them?
    -- For now we only handle closed `t` and `l`.
    if t.hasMVar then
      throwErrorAt t_stx "Term contains metavariables{indentExpr t}"
    let l ← instantiateMVars l
    let some nl ← (evalNat l).run
      | throwErrorAt t_stx "Semantic type has unknown universe level{indentExpr l}"
    if !(← isLevelDefEq nl.toLevel w) then
      throwErrorAt t_stx "Got semantic type at level{indentExpr l}\n\
      but expected{indentExpr <| expectedType}"

    -- Ensure `l < univMax`
    let lt ← ltNat q($l) q(univMax)

    -- `semTy` is well-formed in the external local context.
    let semTy : Q(($s).SigInt) := q(UHomSeq.SigInt.ty.{v,u} $lt $t)
    -- `qst` is a closed expression, well-formed in any local context
    -- (in particular in the internal one).
    let qst : Q(Lean.Expr) := @toExpr Lean.Expr _ semTy
    let expectedType : Q(Type w) := expectedType

    return q(SemAx $expectedType $qst)

open PrettyPrinter Delaborator SubExpr

@[delab app.SynthLean.SemAx]
def delabSemAx : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 2
  let some elabData := elabExt.getState (← getEnv) | failure
  let qst ← evalExprExpr (e.getArg! 1)
  let pos := (← getPos).pushNaryArg 2 1
  let st ← withLCtx elabData.lctx elabData.linsts <|
    withTheReader SubExpr (fun _ => { expr := qst, pos }) <|
      delab
  `(⸨$st⸩)

end SynthLean
