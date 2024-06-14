-- This module serves as the root of the `GroupoidModelInLean4` library.
-- Import modules here that should be built as part of the library.
import «GroupoidModelInLean4».Basic

/- There should be at least three separate files here for three separate developments:
  1. the basic development of the category Grpd of groupoids
  2. the intermediate natural model of HoTT which is constructed out of Gpds
  3. the metaprogram level HoTT 0 for interacting with the model
  -/

/-
# 1. The category Grpd of small groupoids
We will need at least the following:
  - discrete fibrations of groupoids
  - set-valued functors on groupoids (presheaves)
  - the Grothendieck construction relating the previous two
  - Σ- and Π-types for discrete fibrations
  - path groupoids
  - the universe of (small) discrete groupoids
  - polynomial functors of groupoids
  - maybe some W-types
  -/

/-
# 2. The natural model of HoTT in Grpd
We will need at least the following:
  - category Ctx of all small groupoids
  - the presheaf category 𝓔 = Psh(Ctx) in which the model lives
  - the presheaf Type : Ctxᵒᵖ → Set of types in context
  - the presheaf Term : Ctxᵒᵖ → Set of terms in context
  - the typing natural transformation t : Term ⟶ Type
  - the proof that t is (re)presentable
  - the polynomial endofunctor Pₜ : 𝓔 ⥤ 𝓔
  - the type-formers Σ, Π, Id as operations on polynomials
  - the universe Set of (small) discrete groupoids,
      along with its discrete (op-)fibration Set* ⟶ Set
  It might also be useful to have:
  - the proof that presentable natural transformations are tiny maps
  - the proof that Pₜ is therefore cocontinuous, since t is tiny
  -/

  /-
# 3. HoTT 0
No idea!
But it would be nice if the user could:
- interact with types, terms, and type families rather than
    groupoids, homomorphisms, and fibrations
- have the usual Lean rules for the Σ- and Π-types
- have path-induction for the general identity types
- define the sets as the 0-types
- use Lean's normal infrastructure like rewriting, tactics, mathlib, etc.
  for equality on sets.
