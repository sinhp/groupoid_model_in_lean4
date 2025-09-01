import Lean
import Qq
import GroupoidModel.Syntax.Typechecker.Synth
import GroupoidModel.Syntax.Frontend.EnvExt
import GroupoidModel.Syntax.Frontend.Translation

namespace Leanternal

open Lean Elab Command
open Qq

def envDiff (old new : Environment) : Array ConstantInfo := Id.run do
  let mut ret := #[]
  for (c, i) in new.constants.map₂ do
    if old.constants.map₂.contains c then continue
    if c.isInternal then continue
    ret := ret.push i
  return ret

def elabAxiom (thyNm : Name) (stx : Syntax) : CommandElabM Unit := do
  let thyData ← getTheoryData thyNm
  let thyEnv' ← withEnv thyData.env do Command.elabDeclaration stx; getEnv
  if ← MonadLog.hasErrors then
    return
  let diff := envDiff thyData.env thyEnv'
  let #[.axiomInfo ci] := diff
    | throwError "expected exactly one axiom, got {diff.size}:\
      {Lean.indentD ""}{diff.map (·.name)}"
  Command.liftTermElabM do
    let env ← getEnv
    let (l, T) ←
      try withEnv thyData.env <| translateAsTp ci.type |>.run env
      catch e =>
        throwError "failed to translate type{Lean.indentExpr ci.type}\nerror: {e.toMessageData}"
    trace[Leanternal.Translation]
      "axiom.\{{l}} {ci.name} :\
          {Lean.indentExpr T |>.nest 2}"

    have axioms : Q(Axioms Name) := thyData.axioms
    have wf_axioms : Q(($axioms).Wf) := thyData.wf_axioms
    have name : Q(Name) := toExpr ci.name
    let .inr _ ← lookupAxiom q($axioms) q($name)
      | throwError "internal error: axiom '{ci.name}' has already been added, \
        but elaboration succeeded"
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
      value
      hints := .regular 0 -- TODO: what height?
      safety := .safe
    }
    have a : Q(CheckedAx $axioms) := .const ci.name []

    saveShallowTheoryConst thyNm (.axiomInfo ci)
    setTheoryData thyNm { thyData with
      env := thyEnv'
      axioms := q(($a).snocAxioms)
      wf_axioms := q(($a).wf_snocAxioms $wf_axioms)
    }

def elabDeclaration (thyNm : Name) (stx : Syntax) : CommandElabM Unit := do
  let thyData ← getTheoryData thyNm
  let thyEnv' ← withEnv thyData.env do Command.elabDeclaration stx; getEnv
  if ← MonadLog.hasErrors then
    return
  let diff := envDiff thyData.env thyEnv'
  let #[.defnInfo ci] := diff
    | throwError "expected exactly one definition, got {diff.size}:\
      {Lean.indentD ""}{diff.map (·.name)}"
  Command.liftTermElabM do
    let env ← getEnv
    let (l, T) ←
      try withEnv thyData.env <| translateAsTp ci.type |>.run env
      catch e =>
        throwError "failed to translate type{Lean.indentExpr ci.type}\nerror: {e.toMessageData}"
    let (k, t) ←
      try withEnv thyData.env <| translateAsTm ci.value |>.run env
      catch e =>
        throwError "failed to translate term{Lean.indentExpr ci.value}\nerror: {e.toMessageData}"
    if l != k then throwError "internal error: inferred level mismatch"
    trace[Leanternal.Translation]
      "def.\{{l}} {ci.name} :\
          {Lean.indentExpr T |>.nest 2}\n\
      :=\
        {Lean.indentExpr t}"

    have axioms : Q(Axioms Name) := thyData.axioms
    have wf_axioms : Q(($axioms).Wf) := thyData.wf_axioms
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
      value
      hints := .regular 0 -- TODO: what height?
      safety := .safe
    }

    saveShallowTheoryConst thyNm (.defnInfo ci)
    setTheoryData thyNm { thyData with env := thyEnv' }

/-- Declare a new Leanternal theory with the given name.
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

end Leanternal
