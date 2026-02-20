import Lean
import Qq
import HoTTLean.Typechecker.Synth
import HoTTLean.Frontend.EnvExt
import HoTTLean.Frontend.Translation

namespace SynthLean

open Lean Elab Command
open Qq

def envDiff (old new : Environment) : Array ConstantInfo := Id.run do
  let mut ret := #[]
  for (c, i) in new.constants.map₂ do
    if old.constants.map₂.contains c then continue
    if c.isInternal then continue
    ret := ret.push i
  return ret

/-- Find axioms used by the given constant in the given theory environment,
and return them as an axiom environment.
Assumes that all such axioms are present in the ambient environment
as definitions of type `CheckedAx _` under the same name. -/
def computeAxioms (thyEnv : Environment) (constNm : Name) :
    MetaM ((E : Q(Axioms Name)) × Q(($E).Wf)) := do
  let (_, st) ← (CollectAxioms.collect constNm).run thyEnv |>.run {}
  let axioms := st.axioms
  -- The output includes `constNm` if it is itself an axiom.
  let axioms := axioms.filter (· != constNm)
  -- Order the axioms by '`a` uses `b`'.
  let mut axiomAxioms : Std.HashMap Name (Array Name) := {}
  for axNm in axioms do
    let (_, st) ← (CollectAxioms.collect axNm).run thyEnv |>.run {}
    let axioms := st.axioms.filter (· != axNm)
    axiomAxioms := axiomAxioms.insert axNm axioms
  let mut axioms := axioms.qsort (fun a b => axiomAxioms[b]!.contains a)
  -- HACK: replace `sorryAx` with our universe-monomorphic versions.
  if let some i := axioms.findIdx? (· == ``sorryAx) then
    axioms := axioms.set! i `sorryAx₀
    for i in [1:univMax] do
      axioms := axioms.push (Name.anonymous.str s!"sorryAx{Nat.subDigitChar i}")
  let mut E : Q(Axioms Name) := q(.empty _)
  let mut Ewf : Q(($E).Wf) := q(Axioms.empty_wf _)
  for axNm in axioms do
    let axCi ← getConstInfo axNm
    if !axCi.type.isAppOfArity' ``CheckedAx 2 then
      throwError "checked axiom '{axNm}' has unexpected type{indentExpr axCi.type}"
    let #[_, axE] := axCi.type.getAppArgs | throwError "internal error"
    have axE : Q(Axioms Name) := axE
    have ax : Q(CheckedAx $axE) := .const axNm []
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

/-- Add an axiom `ci` defined in environment `thyEnv`
to the Lean environment as a `CheckedAx`. -/
def addCheckedAx (thyEnv : Environment) (ci : AxiomVal) : MetaM Unit := do
  let env ← getEnv
  let (l, T) ← withEnv thyEnv do
    try translateAsTp q(Lean.Name) ci.type |>.run env
    catch e =>
      throwError "failed to translate type{Lean.indentExpr ci.type}\nerror: {e.toMessageData}"

  let ⟨axioms, wf_axioms⟩ ← computeAxioms thyEnv ci.name
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
    name := ci.name
    levelParams := []
    type := q(CheckedAx $axioms)
    value := ShareCommon.shareCommon' value
    hints := .regular 0 -- TODO: what height?
    safety := .safe
  }

/-- Add a definition `ci` defined in environment `thyEnv`
to the Lean environment as a `CheckedDef`. -/
def addCheckedDef (thyEnv : Environment) (ci : DefinitionVal) : MetaM Unit := do
  let env ← getEnv
  let (l, T) ← withEnv thyEnv do
    try translateAsTp q(Lean.Name) ci.type |>.run env
    catch e =>
      throwError "failed to translate type{Lean.indentExpr ci.type}\nerror: {e.toMessageData}"
  let (k, t) ← withEnv thyEnv do
    try translateAsTm q(Lean.Name) ci.value |>.run env
    catch e =>
      throwError "failed to translate term{Lean.indentExpr ci.value}\nerror: {e.toMessageData}"
  if l != k then throwError "internal error: inferred level mismatch"

  let ⟨axioms, wf_axioms⟩ ← computeAxioms thyEnv ci.name
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
    name := ci.name
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

def elabAxiom (thyNm : Name) (stx : Syntax) : CommandElabM Unit := do
  let thyData ← getTheoryData thyNm
  let thyEnv' ← withEnv thyData.env do Command.elabDeclaration stx; getEnv
  if ← MonadLog.hasErrors then
    return
  setTheoryData thyNm { thyData with env := thyEnv' }
  let diff := envDiff thyData.env thyEnv'
  let #[.axiomInfo i] := diff
    | throwError "expected exactly one axiom, got {diff.size}:\
      {Lean.indentD ""}{diff.map (·.name)}"
  saveShallowTheoryConst thyNm (.axiomInfo i)
  Command.liftTermElabM <| addCheckedAx thyEnv' i

def elabDeclaration (thyNm : Name) (stx : Syntax) : CommandElabM Unit := do
  let thyData ← getTheoryData thyNm
  let thyEnv' ← withEnv thyData.env do Command.elabDeclaration stx; getEnv
  if ← MonadLog.hasErrors then
    return
  setTheoryData thyNm { thyData with env := thyEnv' }
  let diff := envDiff thyData.env thyEnv'
  let #[.defnInfo i] := diff
    | throwError "expected exactly one definition, got {diff.size}:\
      {Lean.indentD ""}{diff.map (·.name)}"
  saveShallowTheoryConst thyNm (.defnInfo i)
  Command.liftTermElabM <| addCheckedDef thyEnv' i

/-- Declare a new SynthLean theory with the given name.
Theories start off with no axioms or definitions.
You can add these using `<theory> def` and `<theory> axiom`,
where `<theory>` is your chosen name. -/
elab "declare_theory " thy:ident : command => do
  let thyNm := thy.getId
  saveTheoryDecl thyNm
  let pre : TSyntax `str := quote s!"{thyNm} "
  -- Bug: `command` written directly inside the quotation is hygienized,
  -- and then the quoted command fails to run.
  let cmdId : Ident := mkIdent `command
  elabCommand <| ← `(command|
    -- TODO: this makes `thyNm` a keyword token; not great?
    elab $pre:str cmd:command : $cmdId:ident => do
      match cmd.raw[0].getKind with
      | `«#check» | `«#print» =>
        let thyData ← getTheoryData $(quote thyNm)
        withEnv thyData.env <| elabCommand cmd
        return
      | _ => pure ()

      match cmd.raw[1].getKind with
      | ``Parser.Command.definition => elabDeclaration $(quote thyNm) cmd
      | ``Parser.Command.axiom => elabAxiom $(quote thyNm) cmd
      | _ => throwError "unhandled command:{indentD cmd}"
  )

-- Reflect definitions from the prelude as `Checked*`.
run_meta do
  let thyData ← mkInitTheoryData default default
  let addAx (nm : Name) := do
    let .axiomInfo i ← withEnv thyData.env <| getConstInfo nm | throwError "internal error"
    addCheckedAx thyData.env i
  let addDef (nm : Name) := do
    let .defnInfo i ← withEnv thyData.env <| getConstInfo nm | throwError "internal error"
    addCheckedDef thyData.env i
  -- TODO: fold
  addDef `Identity.rfl₀
  addDef `Identity.rfl₁
  addDef `Identity.symm₀
  addDef `Identity.symm₁
  addDef `Identity.trans₀
  addDef `Identity.trans₁
  addAx `sorryAx₀
  addAx `sorryAx₁
  addAx `sorryAx₂

end SynthLean
