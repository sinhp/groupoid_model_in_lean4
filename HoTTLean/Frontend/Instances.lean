import HoTTLean.Model.Unstructured.InternalTheory
import HoTTLean.Frontend.Reflected

/-! Classes used by the typechecker to combine expressions from different theories. -/

namespace SynthLean

variable {χ : Type*}

/-! ## Theory inclusions -/

namespace Axioms

variable (𝕋 𝕋' : Axioms χ)

-- High priority to prove `𝕋.snoc 𝕋c Awf ≤ 𝕋.snoc 𝕋c Awf` without going through `snoc_le_snoc`.
instance (priority := high) : Fact (𝕋 ≤ 𝕋) := ⟨Std.Refl.refl _⟩

/-! The rules below prove `Fact (𝕋 ≤ 𝕋')` whenever both are theories are `.empty`/`.snoc` lists,
and `𝕋` is a sublist of `𝕋'` (without reordering). -/

instance : Fact (.empty χ ≤ 𝕋) := ⟨empty_le _⟩

instance [DecidableEq χ] [Fact (𝕋 ≤ 𝕋')]
    {c A l} (𝕋'c : 𝕋' c = none) (Awf : 𝕋' ∣ [] ⊢[l] A) :
    Fact (𝕋 ≤ 𝕋'.snoc 𝕋'c Awf) :=
  ⟨le_snoc Fact.out ..⟩

instance [DecidableEq χ] [Fact (𝕋 ≤ 𝕋')]
    {c A l} (𝕋c : 𝕋 c = none) (𝕋'c : 𝕋' c = none)
    (Awf : 𝕋 ∣ [] ⊢[l] A) (Awf' : 𝕋' ∣ [] ⊢[l] A) :
    Fact (𝕋.snoc 𝕋c Awf ≤ 𝕋'.snoc 𝕋'c Awf') :=
  ⟨snoc_le_snoc Fact.out ..⟩

end Axioms

/-! ## Theory maps -/

variable {χ' : Type*}

/-- Provides a well-formed translation from theory `𝕋` to theory `𝕋'`.

This is a class because when such a translation exists,
it is convenient to directly use `𝕋`-expressions in `𝕋'`-expressions.
We automatically insert the instance in such cases. -/
class HasTheoryMap (𝕋 : Axioms χ) (𝕋' : Axioms χ') where
  map : χ → χ'
  map_wf (𝕋 𝕋') : WfTheoryMap 𝕋 map 𝕋'

instance (𝕋 𝕋' : Axioms χ) [Fact (𝕋 ≤ 𝕋')] : HasTheoryMap 𝕋 𝕋' where
  map := id
  map_wf := WfTheoryMap.of_le Fact.out

/-! ## Well-formed theories -/

instance (χ) : Fact (Axioms.empty χ).Wf :=
  ⟨Axioms.empty_wf χ⟩

instance [DecidableEq χ] (𝕋 : Axioms χ) [Fact 𝕋.Wf] (a : ReflectedAx 𝕋) : Fact a.snocAxioms.Wf :=
  ⟨a.wf_snocAxioms Fact.out⟩

instance [DecidableEq χ] (𝕋 : Axioms χ) [Fact 𝕋.Wf]
    {c A l} (𝕋c : 𝕋 c = none) (Awf : 𝕋 ∣ [] ⊢[l] A) :
    Fact (𝕋.snoc 𝕋c Awf).Wf :=
  ⟨(Fact.out : 𝕋.Wf).snoc 𝕋c Awf⟩

open CategoryTheory
open Model UnstructuredUniverse
universe v u

instance {𝒞 : Type u} [Category.{v,u} 𝒞] [ChosenTerminal 𝒞] (s : UHomSeq 𝒞) : Fact s.thyInt.Wf :=
  ⟨s.thyInt_wf⟩

end SynthLean
