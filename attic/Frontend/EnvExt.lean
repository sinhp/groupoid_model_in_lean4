import Lean
import Qq
import HoTTLean.Frontend.Checked

/-!
For all definitions added to a given theory, we must keep track of both
- a shallowly embedded representation of the term/type as a Lean expression,
  for use when working internally; and
- a deeply embedded representation as a `SynthLean.Expr` + correctness proofs,
  for use when working externally.

We store theory-definitions in deep form in the ordinary Lean environment,
and annotate each such definition with its shallow representation.
This module introduces a persistent environment extension, `TheoryExt`,
to keep track of theories and these annotations.

Q: we may be able to recover shallow representations from deep ones without annotations,
but it may take a long time to import modules then.
-/

open Lean in
instance : MonadOptions ImportM where
  getOptions := ImportM.Context.opts <$> read

namespace SynthLean
open Lean Qq

variable {m : Type → Type} [Monad m] [MonadLiftT IO m]
  [MonadOptions m] [MonadEnv m] [MonadError m] [MonadQuotation m]

/-- A theory-updating entry.

These form the persistent part of `TheoryExt`, i.e., are saved in `.olean` files. -/
private inductive TheoryEntry
  /-- Declare a new theory with the given name. -/
  | thy (thyNm : Name)
  /-- Append a constant to the given theory.

  This is a shallow representation of the constant.
  The deep representation is stored in the ordinary Lean environment,
  under the same name. -/
  | const (thyNm : Name) (ci : ConstantInfo)

/-- A cache for theory-specific data.

Used for elaboration but not persisted in `.olean`s:
the ephemeral part of `TheoryExt`.

`TheoryData` introduces a potential infinite regress:
environments contain `TheoryExt`s
which contain dictionaries of environments;
but theory environments have empty `TheoryExt`s,
so there is only one level of recursion. -/
structure TheoryData where
  /-- The module in which this theory was declared.
  May equal the current module. -/
  modNm : Name
  /-- The shallowly embedded theory environment.
  It contains axioms and definitions
  that have been added to the theory so far.

  New definitions and axioms are elaborated in this environment. -/
  env : Environment

private abbrev TheoryExt := SimplePersistentEnvExtension TheoryEntry (NameMap TheoryData)

/-- Form the initial data for a theory declared in module `modNm`.

For the initial shallow environment,
we pull in a custom prelude with `Type`-valued identity types. -/
def mkInitTheoryData (modNm mainModule : Name) : m TheoryData := do
  -- TODO: check if the `.olean` exists and print a better error if not.
  let mut thyEnv ← importModules #[{ module := `HoTTLean.Prelude }]
    (← getOptions) (leakEnv := true) (loadExts := true)
  thyEnv := thyEnv.setMainModule mainModule
  return {
    modNm
    env := thyEnv
  }

private initialize theoryExt : TheoryExt ←
  -- We cannot use `registerSimplePersistent..` because `addImportedFn` is pure there.
  registerPersistentEnvExtension {
    mkInitial := return ([], .empty)
    addImportedFn mods := do
      let mut thyMap : NameMap TheoryData := .empty
      let env := (← read).env
      for _h : iMod in [0:mods.size] do
        let mod := mods[iMod]
        -- We assume `mods` is ordered by `ModuleIdx`.
        let modNm := env.header.moduleNames[iMod]!
        for h : iEntry in [0:mod.size] do
          -- See comment on `exportEntriesFnEx`.
          let entry := mod[mod.size - iEntry - 1]'(by have := h.upper; grind)
          match entry with
          | .thy thyNm =>
            if let some thyData := thyMap.find? thyNm then
              throwThe IO.Error
                s!"theory '{thyNm}' has already been declared in module '{thyData.modNm}'"
            let thyData ← mkInitTheoryData modNm env.mainModule
            thyMap := thyMap.insert thyNm thyData
          | .const thyNm ci =>
            let some thyData := thyMap.find? thyNm
              | throwThe IO.Error
                  s!"corrupt olean: appending '{ci.name}' to non-existent theory '{thyNm}'"
            let decl ← match ci with
              | .axiomInfo i => pure <| .axiomDecl i | .defnInfo i => pure <| .defnDecl i
              | _ => throwThe IO.Error s!"unsupported constant kind at '{ci.name}'"
            -- Q: no extension entries added after the prelude; will this break elaboration?
            let .ok thyEnv := thyData.env.addDeclCore 0 decl none (doCheck := false)
              | throwThe IO.Error "internal error" /- cannot happen with `doCheck := false` -/
            thyMap := thyMap.insert thyNm { thyData with env := thyEnv }
      return ([], thyMap)
    /- We update only the list of entries; theory data needs a monadic computation to update. -/
    addEntryFn s e := (e :: s.1, s.2)
    -- Note: because we `cons` local entries onto the list,
    -- this array has the latest entry first
    -- and has to be read in reverse order when imported.
    exportEntriesFnEx _ s _ := s.1.toArray
    -- TODO: statsFn, asyncMode, replay?
  }

/-- Initialize the data of a new theory,
importing `Frontend.Prelude` into the initial shallow environment,
and persistently store the theory declaration. -/
def saveTheoryDecl (thyNm : Name) : m Unit := do
  let mut env ← getEnv
  let st := PersistentEnvExtension.getState theoryExt env
  if st.2.contains thyNm then
    throwError "theory '{thyNm}' has already been declared"
  let thyData ← mkInitTheoryData env.mainModule env.mainModule
  setEnv <| PersistentEnvExtension.setState theoryExt env <|
    ((.thy thyNm) :: st.1, st.2.insert thyNm thyData)

/-- Persistently store the shallow representation of a theory-definition.
The theory must already have been declared.

⚠️ This does _not_ update the theory data; you must also use `setTheoryData`. -/
def saveShallowTheoryConst (thyNm : Name) (ci : ConstantInfo) : m Unit := do
  let env ← getEnv
  if !(theoryExt.getState env).contains thyNm then
    throwError "trying to modify non-existent theory '{thyNm}'"
  setEnv <| theoryExt.addEntry env (.const thyNm ci)

def getTheoryData (thyNm : Name) : m TheoryData := do
  let env ← getEnv
  let thyMap := theoryExt.getState env
  let some thyData := thyMap.find? thyNm
    | throwError "trying to read non-existent theory '{thyNm}'"
  return thyData

def setTheoryData (thyNm : Name) (thyData : TheoryData) : m Unit := do
  let env ← getEnv
  let thyMap := theoryExt.getState env
  if !thyMap.contains thyNm then
    throwError "trying to write non-existent theory '{thyNm}'"
  setEnv <| theoryExt.modifyState env fun ds => ds.insert thyNm thyData

end SynthLean
