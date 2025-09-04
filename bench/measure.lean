import Lean
import Mathlib.Tactic.MoveAdd
import GroupoidModel.Syntax.Frontend.Commands

open Lean Elab Meta Term Leanternal Command
open Qq

/-- Measure times taken by various components on definition `n`
and append them to the NDJSON file `f`.

We time how long it takes for:
- the Lean kernel to verify the definition - `t_kernel`; and
- SynthLean to translate to a deep embedding - `t_translate`; and
- SynthLean to typecheck the embedded type and term - `t_typecheck`; and
- the Lean kernel to verify the reflected typing derivation - `t_rkernel`. -/
elab "#measure" n:ident f:str : command => liftTermElabM do
  let .defnInfo d ← getConstInfo n.getId | throwError "'{n}' is not a definition"

  let dt_kernel ← try
      let t₀ ← IO.monoNanosNow
      -- Important option: ensures that addDecl will wait for the kernel.
      withOptions (fun opts => Elab.async.set opts false) do
      withoutModifyingEnv <| addDecl <| .defnDecl {
        name := d.name ++ `benchr
        levelParams := []
        type := d.type
        value := d.value
        hints := .regular 0 -- TODO: what height?
        safety := .safe
      }
      let t₁ ← IO.monoNanosNow
      pure (t₁ - t₀)
    catch ex =>
      throwError "kernel failed: {ex.toMessageData}"

  let env ← getEnv
  let (dt_translate, l, T, t) ← try
      let t₀ ← IO.monoNanosNow
      let (l, T) ← translateAsTp d.type |>.run env
      let (_, t) ← translateAsTm d.value |>.run env
      let t₁ ← IO.monoNanosNow
      pure (t₁ - t₀, l, T, t)
    catch ex =>
      throwError "translation failed: {ex.toMessageData}"

  let axioms : Q(Axioms Name) := q(Axioms.empty Name)
  have wf_axioms : Q(($axioms).Wf) := q(Axioms.empty_wf Name)

  let (dt_typecheck, value) ← try
      let t₀ ← IO.monoNanosNow
      let Twf ← checkTp q($axioms) q($wf_axioms) q([]) q($l) q($T)
      let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Lean.Name from []) q($T)
      let twf ← checkTm q($axioms) q($wf_axioms) q([]) q($l) q($vT) q($t)
      let t₁ ← IO.monoNanosNow
      let value : Q(CheckedDef $axioms) := q(
        { l := $l
          tp := $T
          nfTp := $vT
          wf_nfTp := $vTeq .nil <| $Twf .nil
          val := $t
          wf_val := $twf .nil <| $vTeq .nil <| $Twf .nil
        }
      )
      pure (t₁ - t₀, value)
    catch ex =>
      throwError "typechecking failed: {ex.toMessageData}"

  let dt_rkernel ← try
      let t₀ ← IO.monoNanosNow
      -- Important option: ensures that addDecl will wait for the kernel.
      withOptions (fun opts => Elab.async.set opts false) do
      withoutModifyingEnv <| addDecl <| .defnDecl {
        name := d.name ++ `benchl
        levelParams := []
        type := q(CheckedDef $axioms)
        value
        hints := .regular 0 -- TODO: what height?
        safety := .safe
      }
      let t₁ ← IO.monoNanosNow
      pure (t₁ - t₀)
    catch ex =>
      throwError "rkernel failed: {ex.toMessageData}"

  IO.FS.withFile f.getString .append fun fTimes => do
    let j : Json := json%
      { name : $(d.name),
        sz: $(d.value.size),
        t_kernel: $dt_kernel,
        t_translate: $dt_translate,
        t_typecheck: $dt_typecheck,
        t_rkernel: $dt_rkernel }
    fTimes.putStrLn j.compress
    fTimes.flush
