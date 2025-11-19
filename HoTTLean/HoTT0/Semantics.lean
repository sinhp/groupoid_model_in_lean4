import HoTTLean.HoTT0.Theory
import HoTTLean.Model.Unstructured.Interpretation
import HoTTLean.Groupoids.UHom

noncomputable section

namespace GroupoidModel

open SynthLean
open Model UnstructuredUniverse Interpretation
open CategoryTheory ChosenTerminal

theorem uHomSeq.slen : univMax ≤ uHomSeq.length := by
  simp [univMax, uHomSeq]

def emptyInterp : Interpretation Lean.Name uHomSeq where
  ax _ _ _ := none

instance : Fact (emptyInterp.Wf uHomSeq.slen (.empty _)) := by
  constructor; constructor; simp [emptyInterp, Axioms.empty]

abbrev isGrpd₀_all_tp : 𝟭_ Ctx.{4} ⟶ uHomSeq[1].Ty :=
  emptyInterp.interpTy HoTT0.isGrpd₀_all.wf_tp

def isGrpd₀_all_witness : 𝟭_ Ctx.{4} ⟶ uHomSeq[1].Tm :=
  sorry

theorem isGrpd₀_all_witness_tp : isGrpd₀_all_witness ⋙ uHomSeq[1].tp = isGrpd₀_all_tp :=
  sorry

def hott₀Interp : Interpretation Lean.Name uHomSeq where
  ax := fun
    | ``HoTT0.isGrpd₀_all, 1, _ => isGrpd₀_all_witness
    | _, _, _ => none

instance : Fact (hott₀Interp.Wf uHomSeq.slen HoTT0.isGrpd₀_all.snocAxioms) := by
  constructor; constructor
  intro c _ eq
  simp [HoTT0.isGrpd₀_all, CheckedAx.snocAxioms, Axioms.snoc] at eq
  split_ifs at eq
  . cases eq
    subst_vars
    use isGrpd₀_all_witness
    simp [hott₀Interp, isGrpd₀_all_witness_tp]
    apply emptyInterp.interpTy_mem HoTT0.isGrpd₀_all.wf_tp
  . cases eq
