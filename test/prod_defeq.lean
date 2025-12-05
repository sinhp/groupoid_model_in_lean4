import HoTTLean.Frontend.Commands
import HoTTLean.Model.Unstructured.Interpretation

/-!
Example requested by B. Mehta at
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Lean4Less.20discussion.20thread/near/561924413
-/

namespace SynthLean
open Qq

/-- Helper to check judgmental term equality. -/
partial def equateWfTms (E : Q(Axioms Lean.Name))
    (vΓ : Q(TpEnv Lean.Name)) (l : Q(Nat))
    (a b T : Q(Expr Lean.Name)) :
    TypecheckerM Q(∀ {Γ}, TpEnvEqCtx $E $vΓ Γ →
      $E ∣ Γ ⊢[$l] ($a) : $T → $E ∣ Γ ⊢[$l] ($b) : $T →
      $E ∣ Γ ⊢[$l] ($a) ≡ ($b) : $T) := do
  let ⟨vT, vTeq⟩ ← evalTpId q($vΓ) q($T)
  let ⟨va, vaeq⟩ ← evalTmId q($vΓ) q($a)
  let ⟨vb, vbeq⟩ ← evalTmId q($vΓ) q($b)
  let eq ← equateTm q(($vΓ).length) q($l) q($vT) q($va) q($vb)
  return q(by as_aux_lemma =>
    introv vΓ aT bT
    apply $eq vΓ.length_eq ($vTeq vΓ aT.wf_tp) ($vaeq vΓ aT) ($vbeq vΓ bT)
  )

end SynthLean

noncomputable section

-- The empty theory has no axioms.
declare_theory empty

empty def MyProd (A B : Type) := Sigma fun (_ : A) => B

empty def myFunc {A B C : Type} : (MyProd A B → C) → A → B → C :=
  fun f a b ↦ f ⟨a, b⟩

empty def myPi {A B : Type} : MyProd A B → A := fun x ↦ x.1
empty def myPair {A B : Type} : A → B → MyProd A B := myFunc (fun x ↦ x)

empty def aux1 {A B : Type} (x : A) (y : B) := myPi (myPair x y)
empty def aux2 {A B : Type} (x : A) (y : B) := x

empty def myPi_myPair {A B : Type} (x : A) (y : B) : Identity (aux1 x y) (aux2 x y) :=
  Identity.refl _

open SynthLean
open Model UnstructuredUniverse Interpretation
open CategoryTheory

variable {𝒞 : Type} [Category 𝒞] [ChosenTerminal 𝒞] (s : UHomSeq 𝒞)
  [s.PiSeq] [s.SigSeq] [s.IdSeq]

def emptyInterp : Interpretation Lean.Name s where
  ax _ _ _ := none

instance : Fact ((emptyInterp s).Wf (.empty _)) := by
  constructor; constructor; simp [emptyInterp, Axioms.empty]

open Qq in
example :
    (emptyInterp s).interpTm aux1.wf_val =
    (emptyInterp s).interpTm aux2.wf_val := by
  apply interpTm_eq -- Reduce to internal judgmental equality
  run_tac do -- Run the typechecker
    let pf ← TypecheckerM.run <| equateWfTms
      q(Axioms.empty Lean.Name) q([]) q(aux1.l) q(aux1.val) q(aux2.val) q(aux1.tp)
    Lean.Elab.Tactic.closeMainGoal `equateTms q($pf TpEnvEqCtx.nil aux1.wf_val aux2.wf_val)
