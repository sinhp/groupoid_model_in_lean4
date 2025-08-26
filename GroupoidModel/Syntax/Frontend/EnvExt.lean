import Lean
import Qq
import GroupoidModel.Syntax.Axioms

/-!
For all definitions added to a given theory, we must keep track of both
- a shallowly embedded representation of the term/type as a Lean expression,
  for use when working internally; and
- a deeply embedded representation as a `Leanternal.Expr` + correctness proofs,
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

namespace Leanternal
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
  /-- The deeply embedded set of theory axioms.

  Equivalently, a cache for something like
  `env.filter (·.isAxiom) |>.fold q(Env.empty Name) fun acc ax => q($acc.snoc ax)`. -/
  axioms : Q(Axioms Name)
  wf_axioms : Q(($axioms).Wf)

private abbrev TheoryExt := SimplePersistentEnvExtension TheoryEntry (NameMap TheoryData)

/-- Form the initial data for a theory declared in module `modNm`.

For the initial shallow environment,
we pull in a custom prelude with `Type`-valued identity types. -/
private def mkInitTheoryData (modNm mainModule : Name) : m TheoryData := do
  -- TODO: check if the `.olean` exists and print a better error if not.
  let mut thyEnv ← importModules #[{ module := `GroupoidModel.Syntax.Frontend.Prelude }]
    (← getOptions) (leakEnv := true) (loadExts := true)
  thyEnv := thyEnv.setMainModule mainModule
  return {
    modNm
    env := thyEnv
    axioms := q(.empty Name)
    wf_axioms := q(.empty Name)
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
        for entry in mod do
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
            match ci with
            | .defnInfo i =>
              -- Q: no extension entries added after the prelude; will this break elaboration?
              let .ok thyEnv := thyData.env.addDeclCore 0 (.defnDecl i) none (doCheck := false)
                | throwThe IO.Error "internal error" /- cannot happen with `doCheck := false` -/

              thyMap := thyMap.insert thyNm { thyData with env := thyEnv }
            | .axiomInfo i =>
              let .ok thyEnv := thyData.env.addDeclCore 0 (.axiomDecl i) none (doCheck := false)
                | throwThe IO.Error "internal error" /- cannot happen with `doCheck := false` -/

              have axioms : Q(Axioms Name) := thyData.axioms
              have wf_axioms : Q(($axioms).Wf) := thyData.wf_axioms
              have a : Q(CheckedAx $axioms) := .const ci.name []
              thyMap := thyMap.insert thyNm { thyData with
                env := thyEnv,
                axioms := q(
                  have : Fact ($axioms).Wf := ⟨$wf_axioms⟩
                  ($a).snocEnv
                )
                wf_axioms := q(
                  have : Fact ($axioms).Wf := ⟨$wf_axioms⟩
                  ($a).wf_snocEnv
                )
              }
            | _ => throwThe IO.Error s!"unexpected constant info kind at '{ci.name}'"
      return ([], thyMap)
    /- We update only the list of entries; theory data needs a monadic computation to update. -/
    addEntryFn s e := (e :: s.1, s.2)
    exportEntriesFnEx _ s _ := s.1.toArray
    -- TODO: statsFn, asyncMode, replay?
  }

/-- Persistently store a new theory declaration. -/
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

/-- Retrieve cached data for the given theory. -/
def getTheoryData (thyNm : Name) : m TheoryData := do
  let env ← getEnv
  let thyMap := theoryExt.getState env
  let some thyData := thyMap.find? thyNm
    | throwError "trying to read non-existent theory '{thyNm}'"
  return thyData

/-- Set cached data for the given theory. -/
def setTheoryData (thyNm : Name) (thyData : TheoryData) : m Unit := do
  let env ← getEnv
  let thyMap := theoryExt.getState env
  if !thyMap.contains thyNm then
    throwError "trying to write non-existent theory '{thyNm}'"
  setEnv <| theoryExt.modifyState env fun ds => ds.insert thyNm thyData

end Leanternal
