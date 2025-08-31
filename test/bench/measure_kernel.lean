import Lean
import Mathlib.Tactic.MoveAdd
import Std
import GroupoidModel.Syntax.Frontend.Commands

-- 1. Load the .olean file with samples into the environment
import bench.sample_id



-- 2. Read all the `benchDef.n constants from the environment

open Lean Elab Meta Term Leanternal Command
open System
open Qq

open Char
-- def isSampleBenchDefId (n : Name) : Bool :=
--   match n with
--   | .str (.str (.str _ s1) s2) s3=>
--     -- components come as: ... → "sample<n>" (s1) ← "benchDef_<m>" (s2) ← _ (rest)
--     let ok1 := s1.startsWith "sample"
--       && isDigit ((s1.drop 6).get 0)
--     let ok2 := s2.startsWith "benchDef_"
--       && isDigit ((s2.drop 9).get 0)
--     let ok3 := s3.startsWith "id_"
--     ok1 && ok2 && ok3
--   | _ => false

def isSampleBenchDefId (n : Name) : Bool :=
  match n with
  | .str .anonymous s1=>
    s1.startsWith "BenchDef_id_" && isDigit ((s1.drop 12).get 0)
  | _ => false

open Name
def name_string (n : Name) : String :=
  match n with
  | .anonymous => ""
  | .str (pre : Name) (s : String) => (name_string pre).append s
  | .num (pre : Name) (i : Nat) => (name_string pre).append (toString i)

elab "#measure_kernel" : command => liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants do
    if !isSampleBenchDefId n then continue
    let .defnInfo d := ci | continue
    try
      let term := d.value
      let type := d.type

      --addDecl of the original, untranslated type+value
      let t_kernel0 ← IO.monoNanosNow
      withoutModifyingEnv <| addDecl <| .defnDecl {
        name := ci.name ++ `benchr
        levelParams := []
        type := type
        value := term
        hints := .regular 0 -- TODO: what height?
        safety := .safe
      }
      let t_kernel1 ← IO.monoNanosNow


      -- now store the name + times in a JSON file
      -- (sz is the size of the term)
      let sz := ci.value!.size
      let base : FilePath := "test" / "bench"
      let file := base / "sampletimes_kernel.json"
      IO.FS.withFile file .append fun fTimes => do
        let j : Json := json%
          { name : $n,
            sz: $sz,
            t_kernel: $(t_kernel1 - t_kernel0)}
        fTimes.putStrLn j.compress
        fTimes.flush
    catch ex =>
      let s := name_string n
      logInfo m!"measure error on {s}:\n{ex.toMessageData}"
      continue

set_option maxHeartbeats 0
#measure_kernel
