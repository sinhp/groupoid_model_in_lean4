import Lean
import Mathlib.Tactic.MoveAdd
import Std
import Qq
import Lean.Elab.Command
import GroupoidModel.Syntax.Frontend.Commands

-- 1. Load the .olean file with samples into the environment
import bench.sample_llm


-- 2. Read all the `benchDef.n constants from the environment

open Lean Elab Meta Term Leanternal Command
open Qq

open Char
def isSampleBenchDef (n : Name) : Bool :=
  match n with
  | .str (.str _ s1) s2 =>
    -- components come as: ... → "sample<n>" (s1) ← "benchDef_<m>" (s2) ← _ (rest)
    let ok1 := s1.startsWith "sample"
      && isDigit ((s1.drop 6).get 0)
    let ok2 := s2.startsWith "benchDef_"
      && isDigit ((s2.drop 9).get 0)
    ok1 && ok2
  | _ => false

open Name
def name_string (n : Name) : String :=
  match n with
  | .anonymous => ""
  | .str (pre : Name) (s : String) => (name_string pre).append s
  | .num (pre : Name) (i : Nat) => (name_string pre).append (toString i)

elab "#measure_rkernel" : command => liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants do
    if !isSampleBenchDef n then continue
    let .defnInfo d := ci | continue
    try
      let term := d.value
      let type := d.type
      /- then it's a sample; so translate, typecheck
      measure time taken by:
      - t_translate: the translation
      - t_tpchk: checkTp/checkTm
      - t_rkernel: addDecl of a CheckedDef (see elabDeclaration in Commands.lean)
      - t_kernel: addDecl of the original, untranslated type+value
        (note: the definition has already been added before, so add it with a new name;
        can also use withoutModifyingEnv) -/

      let env ← getEnv

      --translation
      let (dt_translate, l, T, t) ← try
          let t_translate0 ← IO.monoNanosNow
          let (l, T) ← translateAsTp type |>.run env
          let (_, t) ← translateAsTm term |>.run env
          let t_translate1 ← IO.monoNanosNow
          -- use pure instead of return
          pure (t_translate1 - t_translate0, l, T, t)
        catch ex =>
          throwError "translation failed: {ex.toMessageData}"

      --typechecking
      let axioms : Q(Axioms Name) := q(Axioms.empty Name)
      have wf_axioms : Q(($axioms).Wf) := q(.empty Name)
      have : Q(Fact ($axioms).Wf) := q(⟨$wf_axioms⟩)

      -- let t_tpchk0 ← IO.monoNanosNow
      -- let Twf ← checkTp q($axioms) q(⟨$wf_axioms⟩) q([]) q($l) q($T)
      -- let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Lean.Name from []) q($T)
      -- let twf ← checkTm q($axioms) q(⟨$wf_axioms⟩) q([]) q($l) q($vT) q($t)
      -- let t_tpchk1 ← IO.monoNanosNow

      let (dt_tpchk, value) ← try
          let t_tpchk0 ← IO.monoNanosNow
          let Twf ← checkTp q($axioms) q(⟨$wf_axioms⟩) q([]) q($l) q($T)
          let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Lean.Name from []) q($T)
          let twf ← checkTm q($axioms) q(⟨$wf_axioms⟩) q([]) q($l) q($vT) q($t)
          let t_tpchk1 ← IO.monoNanosNow
          let value : Q(CheckedDef $axioms) := q(
            { l := $l
              tp := $T
              nfTp := $vT
              wf_nfTp := $vTeq .nil <| $Twf .nil
              val := $t
              wf_val := $twf .nil <| $vTeq .nil <| $Twf .nil
            }
          )
          pure (t_tpchk1 - t_tpchk0, value)
        catch ex =>
          throwError "typecheck failed: {ex.toMessageData}"

      let dt_rkernel ← try
          --addDecl of a CheckedDef
          let t_rkernel0 ← IO.monoNanosNow
          withoutModifyingEnv <| addDecl <| .defnDecl {
            name := ci.name ++ `benchl
            levelParams := []
            type := q(CheckedDef $axioms)
            value
            hints := .regular 0 -- TODO: what height?
            safety := .safe
          }
          let t_rkernel1 ← IO.monoNanosNow
          pure (t_rkernel1 - t_rkernel0)
        catch ex =>
          throwError "rkernel failed: {ex.toMessageData}"

      -- now store the name + times in a JSON file
      -- (sz is the size of the term)
      let sz := ci.value!.size
      IO.FS.withFile "sampletimes_rkernel.json" .append fun fTimes => do
        let j : Json := json%
          { name : $n,
            sz: $sz,
            t_translate: $dt_translate,
            t_tpchck: $dt_tpchk,
            t_rkernel: $dt_rkernel }
        fTimes.putStrLn j.compress
        fTimes.flush
    catch ex =>
      let s := name_string n
      logInfo m!"measure error on {s}:\n{ex.toMessageData}"
      continue

set_option maxHeartbeats 0
#measure_rkernel

-- def main : IO Unit := do
--   IO.println "Benchmarking completed"
