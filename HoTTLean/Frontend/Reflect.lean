import Lean
import Qq
import HoTTLean.Prelude
import HoTTLean.Typechecker.Synth
import HoTTLean.Frontend.Translation

/-! We define the `@[reflect]` attribute. -/

namespace SynthLean

open Lean Meta
open Qq

/-- Find axioms used by the given constant,
and return them as an axiom environment.
Fails if any axiom has not yet been reflected
as a definition of type `CheckedAx _`. -/
def computeAxioms (constNm : Name) : MetaM ((E : Q(Axioms Name)) × Q(($E).Wf)) := do
  let env ← getEnv
  let (_, st) ← (CollectAxioms.collect constNm).run env |>.run {}
  let axioms := st.axioms
  -- The output includes `constNm` if it is itself an axiom.
  let axioms := axioms.filter (· != constNm)
  -- Order the axioms by '(`a` uses `b`) or (`a`'s name is lex below `b`'s name)'.
  let mut axiomAxioms : Std.HashMap Name (Array Name) := {}
  for axNm in axioms do
    let (_, st) ← (CollectAxioms.collect axNm).run env |>.run {}
    let axioms := st.axioms.filter (· != axNm)
    axiomAxioms := axiomAxioms.insert axNm axioms
  let mut axioms := axioms.qsort fun a b => axiomAxioms[b]!.contains a || a.lt b
  -- HACK: replace `sorryAx` with our universe-monomorphic versions.
  if let some i := axioms.findIdx? (· == ``sorryAx) then
    axioms := axioms.set! i `sorryAx₀
    for i in [1:univMax] do
      axioms := axioms.push (Name.anonymous.str s!"sorryAx{Nat.subDigitChar i}")
  let mut E : Q(Axioms Name) := q(.empty _)
  let mut Ewf : Q(($E).Wf) := q(Axioms.empty_wf _)
  for axNm in axioms do
    let checkedAxNm := axNm ++ reflectPostfix
    if !(← hasConst checkedAxNm) then
      throwError "Axiom '{Expr.const checkedAxNm []}' has not been reflected. \
        Try marking it with `@[reflect]`."
    let axCi ← getConstInfo checkedAxNm
    if !axCi.type.isAppOfArity' ``CheckedAx 2 then
      throwError "checked axiom '{axNm}' has unexpected type{indentExpr axCi.type}"
    let #[_, axE] := axCi.type.getAppArgs | throwError "internal error"
    have axE : Q(Axioms Name) := axE
    have ax : Q(CheckedAx $axE) := .const checkedAxNm []
    -- (Aux `have`s work around bugs in Qq elaboration.)
    have E' : Q(Axioms Name) := E
    have Ewf' : Q(($E').Wf) := Ewf
    let .inr get_name ← lookupAxiom q($E') q(($ax).name) | continue
    let le ← checkAxiomsLe q($axE) q($E')
    let E'' : Q(Axioms Name) :=
      q(($E').snoc ($ax).l ($ax).name ($ax).tp ($ax).wf_tp.le_univMax ($ax).wf_tp.isClosed)
    let Ewf'' : Q(($E'').Wf) :=
      q(($Ewf').snoc ($ax).name (($ax).wf_tp.of_axioms_le $le) $get_name)
    E := E''
    Ewf := Ewf''
  return ⟨E, Ewf⟩

/-- Reflect the axiom `ci` as a `CheckedAx`,
adding that to the Lean environment. -/
def addCheckedAx (ci : AxiomVal) : MetaM Unit := do
  let (l, T) ←
    try translateAsTp q(Lean.Name) ci.type |>.run
    catch e =>
      throwError "failed to translate type{Lean.indentExpr ci.type}\nerror: {e.toMessageData}"

  let ⟨axioms, wf_axioms⟩ ← computeAxioms ci.name
  have name : Q(Name) := toExpr ci.name
  let .inr _ ← lookupAxiom q($axioms) q($name)
    | throwError "internal error: axiom '{ci.name}' has already been added, \
      but elaboration succeeded"
  TypecheckerM.run do
  let Twf ← checkTp q($axioms) q($wf_axioms) q([]) q($l) q($T)
  let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Lean.Name from []) q($T)
  let value : Q(CheckedAx $axioms) := q(
    { name := $name
      get_name := ‹_›
      l := $l
      tp := $T
      nfTp := $vT
      wf_nfTp := $vTeq .nil <| $Twf .nil
    }
  )

  -- TODO: `addDeclQ`
  addDecl <| .defnDecl {
    name := ci.name ++ reflectPostfix
    levelParams := []
    type := q(CheckedAx $axioms)
    value := ShareCommon.shareCommon' value
    hints := .regular 0 -- TODO: what height?
    safety := .safe
  }

/-- Reflect the definition `ci` as a `CheckedDef`,
adding that to the Lean environment. -/
def addCheckedDef (ci : DefinitionVal) : MetaM Unit := do
  let (l, T) ←
    try translateAsTp q(Lean.Name) ci.type |>.run
    catch e =>
      throwError "failed to translate type{Lean.indentExpr ci.type}\nerror: {e.toMessageData}"
  let (k, t) ←
    try translateAsTm q(Lean.Name) ci.value |>.run
    catch e =>
      throwError "failed to translate term{Lean.indentExpr ci.value}\nerror: {e.toMessageData}"
  if l != k then throwError "internal error: inferred level mismatch"

  let ⟨axioms, wf_axioms⟩ ← computeAxioms ci.name
  TypecheckerM.run do
  let Twf ← checkTp q($axioms) q($wf_axioms) q([]) q($l) q($T)
  let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Lean.Name from []) q($T)
  let twf ← checkTm q($axioms) q($wf_axioms) q([]) q($l) q($vT) q($t)
  let value : Q(CheckedDef $axioms) := q(
    { l := $l
      tp := $T
      nfTp := $vT
      wf_nfTp := $vTeq .nil <| $Twf .nil
      val := $t
      wf_val := $twf .nil <| $vTeq .nil <| $Twf .nil
    }
  )

  addDecl <| .defnDecl {
    name := ci.name ++ reflectPostfix
    levelParams := []
    type := q(CheckedDef $axioms)
    /- The kernel does not max-share terms before checking them,
    and our tactics are currently bad at producing highly shared terms.
    Maximal sharing improves checking time asymptotically on some benchmarks (`bench.samplers.id`)
    and by a constant factor on others (`bench.samplers.fn`). -/
    value := ShareCommon.shareCommon' value
    hints := .regular 0 -- TODO: what height?
    safety := .safe
  }

/--
When applied to a definition or axiom,
this attribute reflects its type and value
as deeply embedded `SynthLean.Expr` syntax
together with a proof that the syntax is well-typed
in SynthLean's minimal version of Martin-Löf type theory (MLTT).
All this is stored in a new definition of type `CheckedDef` or `CheckedAx`,
called `thisDef.reflection`.

Note that SynthLean's MLTT does not support `Prop`
and many features of Lean such as inductive types.
The attribute will fail if these occur in the definition.
-/
initialize registerBuiltinAttribute {
  name := `reflect
  descr := "" -- Is `descr` even used for anything?
  applicationTime := .afterCompilation
  add := fun declName _stx _attrKind => do
    match ← getConstInfo declName with
    | .axiomInfo i => discard <| MetaM.run (addCheckedAx i)
    | .defnInfo i => discard <| MetaM.run (addCheckedDef i)
    | _ => throwError "Unsupported command."
}

-- Reflect definitions from our prelude as `Checked*`.
run_meta do
  let addAx (nm : Name) := do
    let .axiomInfo i ← getConstInfo nm | throwError "internal error"
    addCheckedAx i
  let addDef (nm : Name) := do
    let .defnInfo i ← getConstInfo nm | throwError "internal error"
    addCheckedDef i
  addDef ``Identity.rfl₀
  addDef ``Identity.rfl₁
  addDef ``Identity.symm₀
  addDef ``Identity.symm₁
  addDef ``Identity.trans₀
  addDef ``Identity.trans₁
  addAx ``sorryAx₀
  addAx ``sorryAx₁
  addAx ``sorryAx₂

end SynthLean
