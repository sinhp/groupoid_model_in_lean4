# SynthLean: *A Certifying Proof Assistant for Synthetic Mathematics in Lean*

This repository accompanies the paper submission on **SynthLean**,
a proof assistant that connects synthetic proofs in Martin-Löf type theory (MLTT) with their categorical semantics.

It provides:

* A formalization of the syntax of MLTT with $\Pi$, $\Sigma$, and identity types.
* A certified typechecker and soundness proof for natural model semantics.
* Lean code that demonstrates both internal reasoning (within MLTT) and external reasoning (about models).

This submission also includes incomplete work for the larger **HoTTLean** project,
which includes many `sorry` results involving the groupoid model.

* The main theorem of the paper, theorem 3.1, is `ofType_ofTerm_sound` in
[`GroupoidModel/Syntax/Interpretation.lean`](GroupoidModel/Syntax/Interpretation.lean#L1212), which can be validated to be `sorry`-free using

  ```
  #print axioms NaturalModel.Universe.Interpretation.ofType_ofTerm_sound
  ```
  at the end of the file.

* [`test/unitt.lean`](test/unitt.lean) contains the examples from section 5. (The interpretation section depends on some unproved work on the groupoid model.)

* [`test/hott0.lean`](test/hott0.lean) is another example theory.

A web version of the mathematics, Lean documentation, and a dependency graph on the progress of formalization can be found [here](https://sinhp.github.io/groupoid_model_in_lean4/).

## Building the project

This project uses [Lean 4](https://github.com/leanprover/lean4) with its built-in build system *lake*. To build the project:

1. Clone this repository and open it in VSCode.

2. Fetch mathlib cached `.olean` files for faster builds:

   ```bash
   lake exe cache get
   ```

3. Build the project:

   ```bash
   lake build
   ```

## Acknowledgments

This work builds on the Lean community's [mathlib](https://github.com/leanprover-community/mathlib4) and the [Polynomial Functors project](https://github.com/sinhp/Poly/tree/master).
