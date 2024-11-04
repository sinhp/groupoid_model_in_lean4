
/- There should be at least three separate files here for three separate developments:
  1. the basic development of the category Grpd of groupoids
  2. the intermediate natural model of HoTT which is constructed out of Gpds
  3. the metaprogram level HoTT 0 for interacting with the model
  -/

/-
# 1. The category Grpd of small groupoids
We need at least the following, some of which is already in MathLib:
  - the category of small groupoids and their homomorphisms
  - (discrete and split) fibrations of groupoids
  - pullbacks of (discrete and split) fibrations exist in Grpd and are again (such) fibrations
  - set- and groupoid-valued presheaves on groupoids
  - the Grothendieck construction relating the previous two
  - the equivalence between (split) fibrations and presheaves of groupoids
  - Σ and Π-types for (split) fibrations
  - path groupoids
  - the universe of (small) discrete groupoids (aka sets)
  - polynomial functors of groupoids
  - maybe some W-types
  - eventually we will want some groupoid quotients as well
  -/

/-
# 2. The natural model of HoTT in Grpd
We will need at least the following:
  - the category Ctx (to be interpreted as small groupoids)
  - the display maps of contexts, arising from iterated context extensions
  - the presheaf category 𝓔 = Psh(Ctx) in which the model lives
  - the presheaf Type : Ctxᵒᵖ → Set of types in context
  - the presheaf Term : Ctxᵒᵖ → Set of terms in context
  - the typing natural transformation t : Term ⟶ Type
  - the proof that t is (re)presentable
  - the polynomial endofunctor Pₜ : 𝓔 ⥤ 𝓔
  - the type-formers Σ, Π, Id as operations on polynomials over 𝓔
  - the universe Set of (small) discrete groupoids,
      along with its discrete (op-)fibration Set* ⟶ Set
  It would also be useful to have:
  - the proof that presentable natural transformations are tiny maps
  - the proof that Pₜ is therefore cocontinuous, since t is tiny
  -/

  /-
# 3. HoTT_0
No idea how to do this in practice!
But it would be nice if the user could:
- interact with types, terms, and type families, rather than
    groupoids, homomorphisms, and fibrations
- have the usual Lean rules for the Σ- and Π-types
- have path-induction for the general identity types
- define the sets as the 0-types
- use Lean's normal infrastructure like rewriting, tactics, mathlib, etc.
  for equality on sets.
-/

/-
# Targets
Here are some things that should be doable in HoTT_0:
- HoTT Book real numbers and cumulative hierarchy,
- univalent set theory,
- structure identity principle for general algebraic structures,
- propositional truncation ||A|| ,
- set-truncation ||X||₀ = π₀(X) ,
- groupoid quotients,
- Eilenberg-MacLane spaces K(G,1), and some basic cohomology,
- classifying spaces BG, and the theory of covering spaces,
- calculation of π₁(S¹) = Z using univalence and circle induction,
- Joyal’s combinatorial species,
- Lawvere's objective number theory,
- Egbert’s univalent combinatorics,
- Rezk completion of a small category,
- univalent category theory: equivalences, etc.
-/
