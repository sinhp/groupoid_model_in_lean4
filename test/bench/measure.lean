import Lean
import Mathlib.Tactic.MoveAdd
-- 1. Load the .olean file with samples into the environment
-- import sample

-- 2. Read all the `benchDef.n constants from the environment

open Lean Elab Meta Term

run_meta do
  let env ← getEnv
  IO.FS.withFile "sampletimes.json" .append fun fTimes =>
    for (n, ci) in env.constants do
      if !Name.isPrefixOf `benchDef n then continue

      /- then it's a sample; so translate, typecheck
      measure time taken by:
      - t_translate: the translation
      - t_tpchk: checkTp/checkTm
      - t_rkernel: addDecl of a CheckedDef (see elabDeclaration in Commands.lean)
      - t_kernel: addDecl of the original, untranslated type+value
        (note: the definition has already been added before, so add it with a new name;
        can also use withoutModifyingEnv) -/

      -- now store the name + times in a JSON file
      -- (sz is the size of the term)
      let sz := ci.value!.size
      let j : Json := json% { name : $n, sz: $sz, t_kernel: 10, t_translate: 10 }
      fTimes.putStrLn j.compress
      fTimes.flush
