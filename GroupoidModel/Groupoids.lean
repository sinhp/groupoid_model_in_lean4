/-
The category Grpd of (small) groupoids, as needed for the groupoid model of HoTT.
See the thesis of Jakob Vidmar:
https://etheses.whiterose.ac.uk/22517/1/Vidmar_J_Mathematics_PhD_2018.pdf
for a modern exposition of the groupoid model, including polynomial functors and W-types.
-/
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Category.Grpd

universe u v

namespace CategoryTheory

#check Grpd
-- See Mathlib/CategoryTheory/Category/Grpd.lean

noncomputable section

/-!
# The category Grpd of groupoids
Need at least the following, some of which is already in MathLib:
  - the category of small groupoids and their homomorphisms
  - discrete fibrations of groupoids
  - set-valued functors on groupoids (presheaves)
  - the Grothendieck construction relating the previous two
  - Σ and Π-types for discrete fibrations
  - path groupoids
  - the universe of (small) discrete groupoids (aka sets)
  - polynomial functors of groupoids and of presheaves on Grpd
  - maybe some W-types
  -/
