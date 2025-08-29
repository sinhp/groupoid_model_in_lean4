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
  | .str (.str _ s2) s1 =>
    -- components come as: ... → "sample<n>" (s1) ← "benchDef_<m>" (s2) ← _ (rest)
    let ok1 := s1.startsWith "sample"
      && isDigit ((s1.drop 6).get 0)
    let ok2 := s2.startsWith "benchDef_"
      && isDigit ((s2.drop 9).get 0)
    ok1 && ok2
  | _ => false

elab "measure" : command => liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants do
    if !isSampleBenchDef n then continue
    let .defnInfo d := ci | continue

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

    let thyData ← getTheoryData `mltt
    let env ← getEnv

    --translation
    let t_translate0 ← IO.monoMsNow
    let (l, T) ← withEnv thyData.env <| translateAsTp type |>.run env
    let (_, t) ← withEnv thyData.env <| translateAsTm term |>.run env
    let t_translate1 ← IO.monoMsNow

    --typechecking
    have axioms : Q(Axioms Name) := thyData.axioms
    have wf_axioms : Q(($axioms).Wf) := thyData.wf_axioms
    let t_tpchk0 ← IO.monoMsNow
    let Twf ← checkTp q($axioms) q(⟨$wf_axioms⟩) q([]) q($l) q($T)
    let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Lean.Name from []) q($T)
    let twf ← checkTm q($axioms) q(⟨$wf_axioms⟩) q([]) q($l) q($vT) q($t)
    let t_tpchk1 ← IO.monoMsNow

    let value : Q(CheckedDef $axioms) := q(
      have : Fact ($axioms).Wf := ⟨$wf_axioms⟩
      { l := $l
        tp := $T
        nfTp := $vT
        wf_nfTp := $vTeq .nil <| $Twf .nil
        val := $t
        wf_val := $twf .nil <| $vTeq .nil <| $Twf .nil
      }
    )

    --addDecl of the original, untranslated type+value
    let t_rkernel0 ← IO.monoMsNow
    withoutModifyingEnv <| addDecl <| .defnDecl {
      name := ci.name ++ `benchr
      levelParams := []
      type := type
      value := term
      hints := .regular 0 -- TODO: what height?
      safety := .safe
    }
    let t_rkernel1 ← IO.monoMsNow

    --addDecl of a CheckedDef
    let t_kernel0 ← IO.monoMsNow
    withoutModifyingEnv <| addDecl <| .defnDecl {
      name := ci.name ++ `benchl
      levelParams := []
      type := q(CheckedDef $axioms)
      value
      hints := .regular 0 -- TODO: what height?
      safety := .safe
    }
    let t_kernel1 ← IO.monoMsNow

    -- now store the name + times in a JSON file
    -- (sz is the size of the term)
    let sz := ci.value!.size
    IO.FS.withFile "sampletimes.json" .append fun fTimes => do
      let j : Json := json%
        { name : $n,
          sz: $sz,
          t_kernel: $(t_kernel1 - t_kernel0),
          t_translate: $(t_translate1 - t_translate0),
          t_tpchck: $(t_tpchk1 - t_tpchk0),
          t_rkernel: $(t_rkernel1 - t_rkernel0) }
      fTimes.putStrLn j.compress
      fTimes.flush
