-- import GroupoidModel.Syntax.Basic
import GroupoidModel.Syntax.Frontend.Prelude
import Canonical.Main

universe u

axiom app {A : Type} {B : A → Type} (f : (a : A) → B a) (a : A) : B a
axiom fst {A : Type} {B : A → Type} (p : (a : A) × B a) : A
axiom snd {A : Type} {B : A → Type} (p : (a : A) × B a) : B (fst p)
axiom idRec {A : Type} (t : A) (M : (y : A) → Identity t y → Type) (r : M t (.refl t)) (u : A)
    (h : Identity t u) : M u h

open Canonical Lean Elab Term Command Meta in
/-- Samples n terms of the given type from Canonical. -/
elab "#test_canonical" n:num m:num tp:term : command => do
  liftTermElabM <| do
    let tp ← elabTerm tp (Expr.sort 1) /- .sort 1 is `Type` -/
    if tp.hasSorry then return
    let config := { count := n.getNat.toUSize }
    let premises := #[``Canonical.Pi, ``Canonical.Pi.f,
      ``app, ``fst, ``snd, ``idRec, ``Sigma.mk]
    let typ ← toCanonical tp premises config
    -- TODO: can we skip `Eq` in `typ`
    dbg_trace typ
    let result ← canonical typ config.count.toUInt64 config.count
    let tps ← result.terms.mapM fun term => fromCanonical term tp
    let mut name : Nat := 0
    for tp in tps do
      let config := { config with count := m.getNat.toUSize }
      let typ ← toCanonical tp premises config
      -- TODO: smaller timeout
      let result ← canonical typ config.count.toUInt64 config.count
      let tms ← result.terms.mapM fun term => fromCanonical term tp
      logInfo m!"{tp} : {repr tms}"
      for tm in tms do
        name := name + 1
        let mut mvars := tp.collectMVars {}
        mvars := tm.collectMVars mvars
        logInfo m!"{mvars.result}"
        addDecl <| .defnDecl {
          name := Name.num `benchDef name
          levelParams := mvars.result.toList.map (·.name)
          type := tp
          value := tm
          hints := default
          safety := default
        }


-- #test_canonical 100 (Tp 0 0)


-- #test_canonical 1 2 (Type)
-- #test_canonical 10 (Type → Type)
