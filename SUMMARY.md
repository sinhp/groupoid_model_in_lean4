# HoTTLean — project summary

## What the project is

HoTTLean is a Lean 4 formalization of categorical semantics of Martin-Löf type theory, with two complementary tracks running in parallel:

1. **External, semantic mathematics**: natural models of MLTT in presheaf categories, and a concrete `sorry`-free construction of the groupoid model with Π, Σ, and Id types.
2. **Internal, synthetic mathematics**: a deep embedding of MLTT syntax together with a custom proof-assistant frontend, *SynthLean*, that lets users write definitions and axioms inside a chosen object theory (e.g. `hott0`) and have them mechanically translated and certified by an internal typechecker.

The two tracks are tied together by a soundness theorem (`ofType_ofTerm_sound` in `HoTTLean/Model/Natural/Interpretation.lean`) which interprets the deep syntax into any natural model. The eventual goal stated in the README is to interpret synthetic HoTT theorems (in the spirit of GroundZero) into classical Mathlib models. The code base lives at about 19.5 kLoC under `HoTTLean/`.

## Mathematical content

**Syntax (`HoTTLean/Syntax`, ~2.7 kLoC).** A single inductive type `Expr χ` of MLTT expressions with axiom names `χ`, dependent product, sigma, identity, universes `univ l`, `el`/`code` for the Russell/Tarski coding, plus type-annotated elimination forms. De Bruijn indices throughout, with a separate σ-calculus of substitutions (`Autosubst.lean`) registered as a `simp` rewrite system. Typing is given as four mutually inductive `Prop`-valued judgments (`WfCtx`, `WfTp`, `EqTp`, `WfTm`, `EqTm` in `Typing.lean`), with both "primed" rules carrying redundant presuppositions and "unprimed" derived rules used in practice. Universe levels are bounded by a hard-wired `univMax := 3`. There are substantial inversion (`Inversion.lean`, `InversionLemmas.lean`), substitution, and equation-congruence lemmas.

**Natural-model semantics (`HoTTLean/Model/Natural`).** A `Universe` is a natural transformation `tp : Tm ⟶ Ty` of presheaves with chosen representable fibers (`ext`, `disp`, `var`, `disp_pullback`). Sequences `UHomSeq` encode the universe hierarchy; the file builds the Π, Σ, Id structure abstractly using polynomial functors (`UvPoly`) imported from the `Poly` library, and culminates in the soundness theorem against the syntax.

**Unstructured (π-clan) semantics (`HoTTLean/Model/Unstructured`).** A second axis of generalization: a `UnstructuredUniverse` drops representability and works with morphisms in an arbitrary category. `Hurewicz.lean` develops cylinders, Hurewicz fibrations, uniform/normal fibrations, and uses them to build identity-type structure via a path/cylinder construction — this is the "Path types in algebraic type theory" approach of the cited paper.

**Groupoid model (`HoTTLean/Groupoids`, ~4.7 kLoC).** The concrete model: contexts are small groupoids (`Ctx := Grpd`), types over `Γ` are functors `Γ ⥤ Grpd` (encoded through `coreAsSmall`), terms are pointed groupoids `PGrpd`, and context extension is the groupoidal Grothendieck construction `∫`. The model is assembled in `UHom.lean`, which packages a 4-level universe tower (`length := 3`, matching `univMax`) and produces `PiSeq`, `SigSeq`, and `IdSeq` instances. The identity types are defined fibrewise as the discrete category on isomorphism sets; elimination uses the cloven-isofibration / Hurewicz machinery (`ClovenIsofibration.lean`, plus the `Hurewicz.lean` infrastructure).

**Supporting libraries.** `HoTTLean/ForMathlib` and `HoTTLean/Grothendieck` extend Mathlib with `Core` (the groupoid core of a category), free groupoids, wide subcategories, the bicategorical Grothendieck construction, representable pullback cones, etc.; the README says these are being upstreamed. `HoTTLean/Pointed` develops pointed (groupoid) categories. `HoTTLean/ForPoly.lean` adds lemmas to the `Poly` library.

**SynthLean frontend (`HoTTLean/Frontend`, `HoTTLean/Typechecker`).** This is the most user-facing layer. `declare_theory hott0` creates a fresh theory namespace; subsequent `hott0 def …` and `hott0 axiom …` commands first elaborate the body as ordinary Lean (in an isolated environment), then `Translation.lean` rewrites the resulting Lean `Expr` into a SynthLean `Expr`, and the certifying typechecker (`Typechecker/{Evaluate,Equate,Synth}.lean`) re-checks it against the deep typing relation. The result is stored as a `CheckedDef`/`CheckedAx` carrying a proof of `WfTm`. The typechecker uses normalization by evaluation with closures (`Value.lean`, ~700 LoC) and is implemented in `Qq` so that the proofs it constructs are themselves checked by the kernel. `test/hott0.lean` shows the result: synthetic statements about function extensionality, `isProp`, `isSet`, set-univalence, etc., all checked into deep terms.

## Formalization style

- Pervasive `noncomputable section` (expected, the semantics is classical).
- Deep dependence on Mathlib's category theory, plus the `Poly` library for `UvPoly`/π-clans.
- Mutual inductive definitions of judgments; many statements proved by a single `mutual_induction WfCtx` invocation, which keeps the soundness theorem proof remarkably compact (about sixty short cases).
- The internal proof assistant relies on `Qq` quotations and Lean metaprogramming (`run_meta`, custom `elab` macros) — including a perceptive trick that reflects every prelude definition (`Identity.rfl₀`/`trans₀`/`sorryAx₀`, …) as a `CheckedAx`/`CheckedDef` so user theories start non-empty.
- Files are large but coherent: many of the bigger ones (`Groupoids/Pi.lean` 1.7 kLoC, `Model/Natural/{NaturalModel,Interpretation}.lean` ≈1.3 kLoC each) follow a "structure then operations then lemmas" template.
- A `Tactic/` subfolder adds a `mutual_induction` tactic and a `grind_cases` helper, and there's a custom `FunctorMap` tactic in `ForMathlib/Tactic/`.
- An `attic/` directory holds earlier iterations (display-map style models, a Russell-PER-MS treatment, an older `NaturalModelBase`).

## What is unfinished or could be improved

- **`sorry`s.** Only three real `sorry`s remain, all in `HoTTLean/ForPoly.lean` (`fst_verticalNatTrans_app`, `snd'_verticalNatTrans_app`, `mk'_comp_verticalNatTrans_app`). These are naturality lemmas for `UvPoly.verticalNatTrans` and look upstreamable to the `Poly` library. The Groupoids and Model directories are genuinely `sorry`-free.
- **`test/unitt.lean` is broken.** It imports `HoTTLean.Model.Interpretation` and `HoTTLean.Groupoids.NaturalModelBase`, which no longer exist (only attic copies survive), and contains an `instance : uHomSeq.IdSeq := sorry`. Either the test needs porting to `Model.Unstructured.Interpretation` + `Groupoids.UHom`, or `HoTTLean.lean` should pull it in so this rots gets noticed.
- **Hard-coded universe ladder.** `univMax = 3` (`Syntax/Typing.lean`) and `uHomSeq` (`Groupoids/UHom.lean`) are manually unrolled four cases; the `PiSeq`/`SigSeq`/`IdSeq` instances enumerate all 16 `(i,j)` cases by hand. A small helper would replace ~80 lines with one. The same applies to `sorryAx₀`/`sorryAx₁`/`sorryAx₂` and `Identity.rfl₀`/`rfl₁` in `Prelude.lean` (already flagged with a FIXME).
- **Blueprint outdated.** README says so explicitly. The PDF in `.Notes (outdated)/` likewise.
- **No higher inductive types.** Acknowledged in the README; this is what prevents interpreting full HoTT.
- **Coverage gap in the model layer.** The natural-model path develops Π/Σ/Id and the soundness theorem, but the groupoid universes are assembled against the *unstructured* universe interface (`Groupoids/UHom.lean` uses `Model.UnstructuredUniverse`), not the natural-model `Universe`. There is no end-to-end chain that takes a `hott0` term, sends it through `ofType_ofTerm_sound`, and lands in the groupoid model — that's the natural next milestone and explains why `test/unitt.lean` is the way it is.
- **`erw` / `FIXME simp failed` clusters.** `Model/Unstructured/Hurewicz.lean` and `Groupoids/Id.lean` each carry ~5 `erw … -- FIXME` lines — symptoms of `simp` lemmas that should be added (or `@[simp]` reformulated) so the definitional unfoldings line up. There are also a few `-- FIXME: transparency := .default` notes in `Model/Natural/NaturalModel.lean`.
- **Performance hints.** `Frontend/Commands.lean` has `hints := .regular 0 -- TODO: what height?` and `ShareCommon.shareCommon'` is used to force maximal sharing. The bench/ directory exists but doesn't seem to be wired into CI.
- **Documentation.** Only the README is end-user facing; module-level doc-comments are good in places (e.g. `Syntax/Typing.lean`, `Model/Natural/NaturalModel.lean`) but the Frontend modules would benefit from a one-page "how SynthLean works" walkthrough, since the trick of running Lean elaboration in an isolated environment then translating to deep syntax is unusual and would be the first thing a reader has to reconstruct.

Overall the project is in a strong intermediate state: the syntactic theory, the typechecker, and the groupoid model with Π/Σ/Id are all genuinely complete and `sorry`-free; what is missing is the last bridge that wires the soundness theorem to the concrete groupoid model and resurrects the `unitt`/`hott0` end-to-end examples, plus cleanup of the universe-ladder boilerplate and the three polynomial-functor lemmas in `ForPoly.lean`.
