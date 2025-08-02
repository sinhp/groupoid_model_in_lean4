import Batteries.Util.ProofWanted
import GroupoidModel.Syntax.EqCtx

/-! ## Injectivity of type formers -/

/-- Injectivity of Π types. -/
axiom EqTp.inv_pi {Γ A B A' B' l₀ l₁ l₂ l₁' l₂'} : Γ ⊢[l₀] .pi l₁ l₂ A B ≡ .pi l₁' l₂' A' B' →
    l₀ = max l₁ l₂ ∧ l₁ = l₁' ∧ l₂ = l₂' ∧
    (Γ ⊢[l₁] A ≡ A') ∧ ((A, l₁) :: Γ ⊢[l₂] B ≡ B')

/-- Injectivity of Σ types. -/
axiom EqTp.inv_sigma {Γ A B A' B' l₀ l₁ l₂ l₁' l₂'} :
    Γ ⊢[l₀] .sigma l₁ l₂ A B ≡ .sigma l₁' l₂' A' B' →
    l₀ = max l₁ l₂ ∧ l₁ = l₁' ∧ l₂ = l₂' ∧
    (Γ ⊢[l₁] A ≡ A') ∧ ((A, l₁) :: Γ ⊢[l₂] B ≡ B')
