import GroupoidModel.Syntax.Synth

variable {χ : Type*} {E : Axioms χ}

theorem isClosed_all :
    (∀ {Γ l A}, E ∣ Γ ⊢[l] A → A.isClosed Γ.length) ∧
    (∀ {Γ l A t}, E ∣ Γ ⊢[l] t : A → t.isClosed Γ.length) := by
  mutual_induction WfTp
  case bvar =>
    intros; rename_i lk _
    simp [Expr.isClosed, lk.lt_length]
  all_goals grind [Expr.isClosed]

theorem WfTp.isClosed {l A} : E ∣ [] ⊢[l] A → A.isClosed := isClosed_all.1
theorem WfTm.isClosed {l A t} : E ∣ [] ⊢[l] t : A → t.isClosed := isClosed_all.2

/-! ## Axiom environments -/

namespace Axioms

def empty (χ) : Axioms χ := fun _ => none

theorem empty_wf (χ) : (empty χ).Wf := nofun

open Classical

instance : LE (Axioms χ) where
  le E E' := ∀ ⦃c p⦄, (E c) = some p → (E' c) = some p

instance : IsRefl (Axioms χ) (· ≤ ·) where
  refl _ _ _ := id

instance : IsTrans (Axioms χ) (· ≤ ·) where
  trans _ _ _ h h' _ _ Ec := h' (h Ec)

theorem empty_le (E : Axioms χ) : empty χ ≤ E := nofun

noncomputable def snoc (E : Axioms χ)
    (l : Nat) (c : χ) (A : Expr χ)
    (l_le : l ≤ univMax) (A_cl : A.isClosed) : Axioms χ :=
  fun d => if d = c then some ⟨(A, l), ⟨A_cl, l_le⟩⟩ else E d

@[simp]
theorem snoc_get (E : Axioms χ) (l c A l_le A_cl) :
    E.snoc l c A l_le A_cl c = some ⟨(A, l), ⟨A_cl, l_le⟩⟩ := by
  simp [snoc]

theorem le_snoc {E E' : Axioms χ} (le : E ≤ E') (l c A l_le A_cl) (Ec : E c = none) :
    E ≤ E'.snoc l c A l_le A_cl := by
  intro d Al Ed
  have : d ≠ c := by grind
  simpa [snoc, this, ↓reduceIte] using le Ed

theorem le_snoc_self (E : Axioms χ) (l c A l_le A_cl) (Ec : E c = none) :
    E ≤ E.snoc l c A l_le A_cl :=
  le_snoc (refl _) l c A l_le A_cl Ec

theorem snoc_le {E E' : Axioms χ} (le : E ≤ E') (l c A l_le A_cl)
    (E'c : E' c = some ⟨(A, l), ⟨A_cl, l_le⟩⟩) :
    E.snoc l c A l_le A_cl ≤ E' := by
  intro d Al Ed
  by_cases eq : d = c
  . cases eq; convert E'c using 2; simpa [snoc] using Ed.symm
  . simp only [snoc, eq, ↓reduceIte] at Ed; exact le Ed

theorem of_le_all {E E' : Axioms χ} (le : E ≤ E') :
    (∀ {Γ}, WfCtx E Γ → WfCtx E' Γ) ∧
    (∀ {Γ l A}, E ∣ Γ ⊢[l] A → E' ∣ Γ ⊢[l] A) ∧
    (∀ {Γ l A B}, E ∣ Γ ⊢[l] A ≡ B → E' ∣ Γ ⊢[l] A ≡ B) ∧
    (∀ {Γ l A t}, E ∣ Γ ⊢[l] t : A → E' ∣ Γ ⊢[l] t : A) ∧
    (∀ {Γ l A t u}, E ∣ Γ ⊢[l] t ≡ u : A → E' ∣ Γ ⊢[l] t ≡ u : A) := by
  mutual_induction WfCtx
  case ax =>
    intros; rename_i Ec _ Γ ihA
    apply WfTm.ax Γ (le Ec) ihA
  grind_cases

end Axioms

theorem WfCtx.of_axioms_le {E E' : Axioms χ} {Γ} (le : E ≤ E') (Γwf : WfCtx E Γ) :
    WfCtx E' Γ :=
  Axioms.of_le_all le |>.1 Γwf

theorem WfTp.of_axioms_le {E E' : Axioms χ} {Γ A l} (le : E ≤ E') (ΓA : E ∣ Γ ⊢[l] A) :
    E' ∣ Γ ⊢[l] A :=
  Axioms.of_le_all le |>.2.1 ΓA

theorem EqTp.of_axioms_le {E E' : Axioms χ} {Γ A B l} (le : E ≤ E') (ΓAB : E ∣ Γ ⊢[l] A ≡ B) :
    E' ∣ Γ ⊢[l] A ≡ B :=
  Axioms.of_le_all le |>.2.2.1 ΓAB

theorem WfTm.of_axioms_le {E E' : Axioms χ} {Γ A t l} (le : E ≤ E') (Γt : E ∣ Γ ⊢[l] t : A) :
    E' ∣ Γ ⊢[l] t : A :=
  Axioms.of_le_all le |>.2.2.2.1 Γt

theorem EqTm.of_axioms_le {E E' : Axioms χ} {Γ A t u l} (le : E ≤ E') (Γtu : E ∣ Γ ⊢[l] t ≡ u : A) :
    E' ∣ Γ ⊢[l] t ≡ u : A :=
  Axioms.of_le_all le |>.2.2.2.2 Γtu

theorem Axioms.Wf.snoc {E : Axioms χ} {A l}
    (Ewf : E.Wf) (c : χ) (Awf : E ∣ [] ⊢[l] A) (Ec : E c = none) :
    (E.snoc l c A Awf.le_univMax Awf.isClosed).Wf := by
  intro d Al Ed
  simp only [Axioms.snoc] at Ed
  have le := E.le_snoc_self l c A Awf.le_univMax Awf.isClosed Ec
  by_cases eq : d = c <;> simp only [eq, ↓reduceIte] at Ed
  . cases Ed
    exact Awf.of_axioms_le le
  . exact (Ewf Ed).of_axioms_le le
