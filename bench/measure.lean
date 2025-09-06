import Lean
import GroupoidModel.Syntax.Typechecker.Synth
import GroupoidModel.Syntax.Frontend.Translation

open Lean Elab Meta Term Command
open Leanternal
open Qq

inductive Measurement where
  | nanos | heartbeats

def timedSection {α : Type} {m : Type → Type} [Monad m] [MonadError m] [MonadLiftT BaseIO m]
    (title : String) (meas : Measurement) (x : m α) : m (α × ℕ) := do
  try
    match meas with
    | .nanos =>
      let t₀ ← IO.monoNanosNow
      let a ← x
      let t₁ ← IO.monoNanosNow
      return (a, t₁ - t₀)
    | .heartbeats => withHeartbeats x
  catch ex =>
    throwError "{title} failed: {ex.toMessageData}"

def shareQ {u : Level} {α : Q(Sort u)} (e : Q($α)) : (e' : Q($α)) ×' $e' =Q $e :=
  ⟨ShareCommon.shareCommon' e, .unsafeIntro⟩

/-- Measure effort taken by various components on definition `n`
and append them to the NDJSON file `f`.
If `b = 0`, we measure effort in heartbeats;
otherwise in nanoseconds.

We time how long it takes for:
- the Lean kernel to verify the definition - `t_kernel`; and
- SynthLean to translate to a deep embedding - `t_translate`; and
- SynthLean to typecheck the embedded type and term - `t_typecheck`; and
- the Lean kernel to verify the reflected typing derivation - `t_rkernel`. -/
elab "#measure" n:ident f:str b:num : command => liftTermElabM do
  let .defnInfo d ← getConstInfo n.getId | throwError "'{n}' is not a definition"
  let meas : Measurement := if b.getNat == 0 then .heartbeats else .nanos

  let (_, dt_kernel) ← timedSection "kernel" meas do
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

  let env ← getEnv
  let ((l, T, t), dt_translate) ← timedSection "translation" meas do
    let (l, T) ← translateAsTp d.type |>.run env
    let (_, t) ← translateAsTm d.value |>.run env
    pure (l, T, t)

  let axioms : Q(Axioms Name) := q(Axioms.empty Name)
  have wf_axioms : Q(($axioms).Wf) := q(Axioms.empty_wf Name)

  let ((value, vT, wf_nfTp, wf_val), dt_typecheck) ← timedSection "typechecking" meas do
    TypecheckerM.run do
      let Twf ← checkTp q($axioms) q($wf_axioms) q([]) q($l) q($T)
      let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Lean.Name from []) q($T)
      let twf ← checkTm q($axioms) q($wf_axioms) q([]) q($l) q($vT) q($t)
      have wf_nfTp := q($vTeq .nil <| $Twf .nil)
      have wf_val := q($twf .nil $wf_nfTp)
      let value : Q(CheckedDef $axioms) := q(
        { l := $l
          tp := $T
          nfTp := $vT
          wf_nfTp := $wf_nfTp
          val := $t
          wf_val := $wf_val
        }
      )
      pure (value, vT, wf_nfTp, wf_val)

  let (_, dt_rkernel) ← timedSection "rkernel" meas do
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

  let (_, dt_rkernel_shared) ← timedSection "rkernel (shared)" meas do
    -- Important option: ensures that addDecl will wait for the kernel.
    withOptions (fun opts => Elab.async.set opts false) do
    withoutModifyingEnv <| addDecl <| .defnDecl {
      name := d.name ++ `benchl
      levelParams := []
      type := q(CheckedDef $axioms)
      value := ShareCommon.shareCommon' value
      hints := .regular 0 -- TODO: what height?
      safety := .safe
    }

  -- Note: size with full sharing is `(ShareCommon.shareCommon' e).numObjs`
  IO.FS.withFile f.getString .append fun fTimes => do
    let j : Json := json%
      { name : $(d.name),
        sz_tp: $(← d.type.numObjs),
        sz_val: $(← d.value.numObjs),
        sz_deep_tp: $(← T.numObjs),
        sz_deep_tp_shared: $(← (ShareCommon.shareCommon' T).numObjs),
        sz_deep_nfTp: $(← vT.numObjs),
        sz_deep_wf_nfTp: $(← wf_nfTp.numObjs),
        sz_deep_val: $(← t.numObjs),
        sz_deep_val_shared: $(← (ShareCommon.shareCommon' t).numObjs),
        sz_deep_wf_val: $(← wf_val.numObjs),
        sz_deep_wf_val_shared: $(← (ShareCommon.shareCommon' wf_val).numObjs),
        sz_nfTp_deep: $(← T.numObjs),
        t_kernel: $dt_kernel,
        t_translate: $dt_translate,
        t_typecheck: $dt_typecheck,
        t_rkernel: $dt_rkernel,
        t_rkernel_shared: $dt_rkernel_shared
      }
    fTimes.putStrLn j.compress
    fTimes.flush
