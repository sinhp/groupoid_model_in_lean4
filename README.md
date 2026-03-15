# **HoTTLean**: Semantics of HoTT in Lean

**HoTTLean** is a Lean formalization of the groupoid model of homotopy type theory,
as well as of category-theoretic models of Martin-Löf type theories in general,
together with a proof mode for developing mathematics synthetically in those type theories.
HoTTLean is work-in-progress.

It currently contains the following components:
- A deep embedding of MLTT syntax with Π, Σ, Id types, and base constants (`HoTTLean.Syntax`).
- **SynthLean**, a proof assistant for these deeply embedded theories
  (`HoTTLean.Frontend`).
  It includes a certifying typechecker (`HoTTLean.Typechecker`).
- Natural model semantics of MLTT in presheaf categories (`HoTTLean.Model`)
  and a proof that this semantics is sound for the syntax (`ofType_ofTerm_sound`).

- A `sorry`-free construction of the groupoid model of type theory with Π, Σ, Id types (`HoTTLean.Groupoids`).
- Pieces of general mathematics and category theory
  such as the Grothendieck construction for groupoids
  (`HoTTLean.ForMathlib`, `HoTTLean.Grothendieck`, `HoTTLean.Pointed`).
  These are being upstreamed to Mathlib.

Documentation of the Lean code can be found
[here](https://sinhp.github.io/HoTTLean/docs/).
(We also have [a blueprint](https://sinhp.github.io/HoTTLean/),
but it is very outdated.)
Relevant papers to this project are listed below
- [A Certifying Proof Assistant for Synthetic
Mathematics in Lean](https://voidma.in/assets/papers/2026nawrocki_certifying_proof_assistant_synthetic_mathematics_lean.pdf)
- [Path Types in Algebraic Type Theory](https://arxiv.org/abs/2601.06567v1)
- [Polynomial Functors in π-clans for the Semantics of Type Theory](https://arxiv.org/pdf/2602.05689)

### Dependencies

We rely on [Mathlib](https://github.com/leanprover-community/mathlib4)
and [Poly](https://github.com/sinhp/Poly/),
a formalization of polynomial functors.

### How can I try out HoTTLean?

First make sure that [Lean is installed](https://lean-lang.org/install/).
Clone this repository,
then in a terminal execute

```shell
# Fetch pre-built Mathlib cache
lake exe cache get
# Build the project
lake build
# Run tests (optional)
lake test
```

Examples demonstrating the usage of SynthLean (for internal reasoning)
and of our model definitions (for external reasoning)
can be found under `test/`:
- `test/unitt` specifies a type theory with a unit type.
- `test/hott0` defines HoTT0,
  a version of HoTT where univalence only holds for h-sets.

### Can I contribute to HoTTLean?

Contributions are very welcome!
We use GitHub issues to organize the project and track formalization progress.
New contributors should pay attention to issues marked with `O-help` (help wanted)
and `D-low` (low difficulty).
You can also reach out to us on the [Lean Zulip](https://leanprover.zulipchat.com/).

### How does this differ from [GroundZero](https://github.com/rzrn/ground_zero/)?

GroundZero is a purely synthetic development of HoTT,
whereas HoTTLean focuses on showing that synthetic results in HoTT
can be interpreted as theorems about classical models that use definitions from Mathlib.
A target for HoTTLean is to eventually allow interpreting theorems of GroundZero
(as well as other HoTT libraries)
in such a way.
This is not quite feasible _yet_
because HoTTLean does not currently support (higher) inductive types,
and our model construction is not yet complete.
