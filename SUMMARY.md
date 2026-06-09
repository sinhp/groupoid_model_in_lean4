# Neut.def WIP — handoff notes

## Goal

Reduce the size of certifying-typechecker witnesses in HoTTLean. Measured baseline (with current `neut-def` work-in-progress instrumentation in `Frontend/Commands.lean`):

| `hott0 def` | unique nodes (post-`ShareCommon`) |
|---|---|
| `pointedType` | 1 400 |
| `pointedType.carrier` | 1 057 |
| `pointedType.point` | 1 577 |
| `pointedType_equiv` | 15 411 |
| **`pointedType_carrier_eq`** | **647 282** |

The last one is a one-line definition. The blow-up is because `Frontend/Translation.lean:194-204` translates every reference to a `hott0 def` as `mkAppM ``CheckedDef.val #[.const i.name []]`, and that projection is unfolded by `whnf` during typechecking — inlining the entire deep body at every reference site.

## Approach

Add a `Neut.def c tp body` constructor in `HoTTLean/Typechecker/Value.lean` to tag values with the constant they came from. Then:

1. **Evaluate.lean** detects `CheckedDef.val (.const c [])` *before* `whnf` and emits `Val.neut (Neut.def c tp body) tp` using cached fields from the `CheckedDef`, instead of unfolding the body.
2. **Equate.lean** short-circuits on same-name `Neut.def` heads (refl without comparing bodies).
3. The deep theory is **not** extended — `NeutEqTm.def` is a transparent wrapper, relating `Neut.def c tp body` to the same deep `Expr` that `body` relates to. No new `WfTm`/`EqTm`/`WfTp`/`EqTp` rule.

`synthTm` (`HoTTLean/Typechecker/Synth.lean:196`) **already has** a fast path for bare `CheckedDef.val`, so a plain `def y := x` already produces a tiny witness. The remaining wins are for *nested* def references (e.g. `M.carrier` inside an `.app`/`.fst`/`.snd`), which currently flow through `evalTm`/`equate*` and inline.

## Branch / commits

- Branch: **`neut-def`**, off **`magma-sip-pr172`** (which is PR #172 from PradCoder + earlier session work).
- Origin: `git@github.com:andrejbauer/HoTTLean.git` (your fork). Upstream `sinhp/HoTTLean` is added as `upstream`.
- This file (`SUMMARY.md`) replaces an earlier project-overview SUMMARY.md (preserved in git history).

## What's done (compiles)

1. **`HoTTLean/Typechecker/Value.lean`** — `Neut.def (c : Lean.Name) (tp body : Val)` added to the `Neut` inductive. `NeutEqTm.def` rule added (currently a strict transparent wrapper with `ValEqTp`+`ValEqTm` premises — see "Open design question" below).
2. **`HoTTLean/Frontend/Checked.lean`** — `CheckedDef` extended with `nfVal : Val χ` and `wf_nfVal : ValEqTm E [] l nfVal val tp`. Three lift helpers added: `wf_nfTp_lift_le`, `wf_nfVal_lift_le`, `wf_val_lift_le`, which lift the cached fields from empty context (in `E`) to any well-formed context in a possibly-larger axiom env `E'`, using `Expr.subst_of_isClosed` to discharge the substitution.
3. **`HoTTLean/Frontend/Commands.lean`** — `addCheckedDef` populates `nfVal`/`wf_nfVal` via a call to `evalTmId`. Also (left over from earlier session work) carries a `numUniqueNodes` instrumentation that logs witness size, and a few `Lean.profileitM` wrappers around phases.

## What's broken (does NOT compile)

4. **`HoTTLean/Typechecker/Evaluate.lean`** — Step 3c attempt. Two issues:
   - At lines ~14-70: `lookupAxiom` and `checkAxiomsLe` were *moved* here from `Synth.lean` during a symptomatic fix attempt. **Mario said to undo this move** — these functions belong in `Synth.lean`. They use Qq-matching on axiom-env structure and depend on `Frontend.Checked`, which is fine in `Synth.lean`.
   - At lines ~150-178: a fast-path match block was added at the top of `evalTm` that pattern-matches on `~q(@CheckedDef.val _ $E' $defn)`. The proof body references `$E` (the current axiom env) via `checkAxiomsLe q($E') q($E)`, but `$E` is **not in scope** at meta time in `evalTm` (see "The blocker" below).

5. **`HoTTLean/Typechecker/Synth.lean`** — `lookupAxiom` and `checkAxiomsLe` are missing because of the move above. Restore them from git history.

## The blocker (read carefully — this is the architectural issue)

`synthTm` lives in a `mutual` block declared with `variable (E : Q(Axioms Lean.Name)) (Ewf : Q(($E).Wf))` (`Synth.lean:103`), so `E` is a *meta-level value* while it runs. Its existing fast path for `CheckedDef.val` calls `checkAxiomsLe q($E') q($E)` at meta time to build a `Q($E' ≤ $E)` proof, then embeds that proof in the witness so the cached `wf_nfTp`/`wf_val` can be lifted via `of_axioms_le`.

`evalTm`'s `mutual` block does **not** have `variable (E …)`. The axiom env `E` shows up only *inside* the universally-quantified witness type:

```lean
∀ {E Γ Δ σ A l}, EnvEqSb E Δ $env σ Γ → (E ∣ Γ ⊢[l] ($t') : A) →
    ValEqTm E Δ l $v (($t').subst σ) (A.subst σ)
```

So there is no concrete `E` to feed `checkAxiomsLe`, and no `$E' ≤ E` proof can be constructed at meta time. (`evalTm` is also more polymorphic than `synthTm` — variable in `χ`, not specialised to `Lean.Name`.)

## Mario's suggested fix (in `Evaluate.lean` line 159 comment)

> "claude: use t' to construct the desired typing derivation, don't try to reconstruct it from E' and defn."

Interpretation that survived discussion: in the witness proof body, don't try to lift cached `wf_nfVal`/`wf_nfTp` from `E'` to `E` — instead, use the typing hypothesis `t : E ∣ Γ ⊢[l] (CheckedDef.val _ $E' $defn) : A` (which after Lean defeq is `t : E ∣ Γ ⊢[l] ($defn).val : A`) as our source of well-formedness in `E`.

For this to work, **`NeutEqTm.def`'s premises must be weakened** from `ValEqTp Γ l tp T` and `ValEqTm Γ l body bodyExpr T` to just `E ∣ Γ ⊢[l] T` (`WfTp`) and `E ∣ Γ ⊢[l] bodyExpr : T` (`WfTm`). With the weakened constructor, the fast-path proof is essentially one line:

```lean
introv env t
have t' := t.subst env.wf_sb   -- WfTm at outer E, in Δ ctx
apply ValEqTm.neut_tm ?_  -- still need ValEqTp here (see below)
apply NeutEqTm.def
· exact t'.wf_tp
· exact t'
```

**Outstanding wrinkle:** even with `NeutEqTm.def` weakened, the wrapping `ValEqTm.neut_tm` still requires a `ValEqTp Γ l tp T`. Two ways forward:

- (a) Weaken `ValEqTm.neut_tm` only for the `Neut.def` case (intrusive — would need a new ValEqTm constructor specifically for the def case).
- (b) **Promote `Neut.def` to `Val.def`** (a top-level `Val` constructor instead of going through `Val.neut`). Then it gets its own `ValEqTm.def` rule with `WfTp`/`WfTm` premises and no `Val.neut` wrapping.

(b) is cleaner. It means every `Val`-pattern-match in the codebase that wants to "see through" a `Val.neut` needs a parallel `Val.def` case (and the existing `Neut.def` plus `NeutEqTm.def` would be replaced or removed). Trade-off: more pattern-match sites to touch, but the proof structure is clean.

**Soundness consequence to be careful about:** with the weakened premises, the `Val` tag (`body` field of `Val.def` or `Neut.def`) is essentially unconstrained at the deep-theory level — it's a *trusted runtime cache*, not a *verified* correspondence to the deep term. This is OK as long as we maintain the meta-level invariant "the only producer of `Val.def` is the evaluate fast path, which always uses the genuine `nfVal` from `CheckedDef`". The deep theory's `WfTm`/`WfTp` parts of the witness remain sound; only the Val-correspondence is trusted.

## Stash

`stash@{0}` holds an earlier abandoned `profileitM`-based instrumentation attempt in `Commands.lean`. Probably safe to drop (`git stash drop`).

## Open follow-ups (record only)

- **`wf_val` can be derived from `wf_nfVal`.** `ValEqTm.wf_tm` (`Value.lean:362`) already proves `ValEqTm → WfTm`. So `wf_val := wf_nfVal.wf_tm`. The `wf_val` field of `CheckedDef` can be removed and added back as a theorem. Saves one proof construction at definition time.
- **Double walk in `addCheckedDef`.** `checkTm` (to build `WfTm`) and `evalTmId` (to build `ValEqTm` for `nfVal`) each independently walk the body. Subterm Vals are shared via the `evalTm` cache, but proof construction runs twice. Could `synthTm` be modified to also return the term Val, sharing the work?
- **Profiling instrumentation.** `Commands.lean` has `numUniqueNodes` + `Lean.profileitM` left in. Keep for measurement, or strip before merging.
- **`test/pointed.lean`** has profiling options enabled and the final SIP definition is commented out. Restore once `Neut.def` lands and `lake env lean test/pointed.lean` is fast.

## Recommended pickup procedure

1. Read this file. Read the existing plan at `~/.claude/plans/effervescent-jingling-garden.md` (lengthy, has the full design history).
2. `git status` to see the WIP changes. `git log --oneline master..HEAD` for the commit graph.
3. Restore `lookupAxiom`/`checkAxiomsLe` to `Synth.lean` from git history; remove from `Evaluate.lean`.
4. Decide between (a) weakening `ValEqTm.neut_tm` for defs or (b) promoting to `Val.def`. (b) is recommended.
5. If (b): change `Neut.def` to `Val.def`. Update `NeutEqTm.def` → `ValEqTm.def` with `WfTp`/`WfTm` premises. Audit `Val`-pattern-match sites (Equate, Evaluate, ValueInversion) and add `Val.def` cases where needed.
6. Write `evalTm`'s fast path using `t.subst env.wf_sb` as outlined above.
7. Add `equate` short-circuit on same-name `Val.def`.
8. Measure: rebuild and check `pointedType_carrier_eq`'s witness size. Target: significant drop toward `pointedType_equiv`'s ~15 K node count.
