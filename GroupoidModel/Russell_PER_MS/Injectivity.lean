import GroupoidModel.Russell_PER_MS.EqCtx

/-! ## Injectivity of Π -/

/- This property, lifted from a system where it is _not_ true
(https://github.com/TheoWinterhalter/formal-type-theory/blob/93ac197dfde912d77af9b0f4fd9f7d2422ba7dfc/src/concise_uniqueness.v#L159)
is actually true of our system, but for stupid reasons:
we have no non-trivial type equalities.
As soon as we add `el code A ≡ A`, it will break;
however, injectivity of Π types as stated below should remain true. -/
private theorem strong_piInj :
    ∀ {Γ l₀ C C'}, Γ ⊢[l₀] C ≡ C' →
      ∀ {A B l l'},
        (C = .pi l l' A B →
          ∃ A' B', l₀ = max l l' ∧ C' = .pi l l' A' B' ∧
            (Γ ⊢[l] A ≡ A') ∧ ((A, l) :: Γ ⊢[l'] B ≡ B')) ∧
        (C' = .pi l l' A B →
          ∃ A' B', l₀ = max l l' ∧ C = .pi l l' A' B' ∧
            (Γ ⊢[l] A ≡ A') ∧ ((A, l) :: Γ ⊢[l'] B ≡ B')) := by
  mutual_induction EqTp
  all_goals intros; try exact True.intro
  all_goals constructor
  all_goals intro eq; cases eq
  . exact ⟨_, _, rfl, rfl, ‹_›, ‹_›⟩
  . rename_i Aeq Beq _ _ _ _
    exact ⟨_, _, rfl, rfl, EqTp.symm_tp ‹_›, Beq.symm_tp.conv_ctx (Aeq.wf_ctx.eq_self.snoc Aeq)⟩
  . rename_i pi
    have := pi.inv_pi
    exact ⟨_, _, this.1, rfl, EqTp.refl_tp this.2.wf_ctx.inv_snoc, EqTp.refl_tp this.2⟩
  . rename_i pi
    have := pi.inv_pi
    exact ⟨_, _, this.1, rfl, EqTp.refl_tp this.2.wf_ctx.inv_snoc, EqTp.refl_tp this.2⟩
  . grind
  . grind
  . rename_i ih _ _ _ _ _ ih'
    obtain ⟨_, _, rfl, rfl, eq₁, eq₂⟩ := ih'.1 rfl
    obtain ⟨_, _, _, rfl, _, eq₃⟩ := ih.1 rfl
    refine ⟨_, _, rfl, rfl, ?_, ?_⟩
    . grind [EqTp.trans_tp]
    . apply eq₂.trans_tp (eq₃.conv_ctx <| eq₁.wf_ctx.eq_self.snoc _)
      grind [EqTp.trans_tp]
  . rename_i ih _ _ _ _ _ ih'
    obtain ⟨_, _, rfl, rfl, eq₁, eq₂⟩ := ih'.2 rfl
    obtain ⟨_, _, _, rfl, _, eq₃⟩ := ih.2 rfl
    refine ⟨_, _, rfl, rfl, ?_, ?_⟩
    . grind [EqTp.trans_tp]
    . apply eq₂.trans_tp (eq₃.conv_ctx <| eq₁.wf_ctx.eq_self.snoc _)
      grind [EqTp.trans_tp]

/-- Injectivity of Π types. -/
theorem EqTp.inv_pi {Γ A B A' B' l₀ l₁ l₂ l₁' l₂'} : Γ ⊢[l₀] .pi l₁ l₂ A B ≡ .pi l₁' l₂' A' B' →
    l₀ = max l₁ l₂ ∧ l₁ = l₁' ∧ l₂ = l₂' ∧
    (Γ ⊢[l₁] A ≡ A') ∧ ((A, l₁) :: Γ ⊢[l₂] B ≡ B') := by
  grind [strong_piInj]

/-! ## Injectivity of Σ -/

private theorem strong_sigmaInj :
    ∀ {Γ l₀ C C'}, Γ ⊢[l₀] C ≡ C' →
      ∀ {A B l l'},
        (C = .sigma l l' A B →
          ∃ A' B', l₀ = max l l' ∧ C' = .sigma l l' A' B' ∧
            (Γ ⊢[l] A ≡ A') ∧ ((A, l) :: Γ ⊢[l'] B ≡ B')) ∧
        (C' = .sigma l l' A B →
          ∃ A' B', l₀ = max l l' ∧ C = .sigma l l' A' B' ∧
            (Γ ⊢[l] A ≡ A') ∧ ((A, l) :: Γ ⊢[l'] B ≡ B')) := by
  mutual_induction EqTp
  all_goals intros; try exact True.intro
  all_goals constructor
  all_goals intro eq; cases eq
  . exact ⟨_, _, rfl, rfl, ‹_›, ‹_›⟩
  . rename_i Aeq Beq _ _ _ _
    exact ⟨_, _, rfl, rfl, EqTp.symm_tp ‹_›, Beq.symm_tp.conv_ctx (Aeq.wf_ctx.eq_self.snoc Aeq)⟩
  . rename_i s
    have := s.inv_sigma
    exact ⟨_, _, this.1, rfl, EqTp.refl_tp this.2.wf_ctx.inv_snoc, EqTp.refl_tp this.2⟩
  . rename_i s
    have := s.inv_sigma
    exact ⟨_, _, this.1, rfl, EqTp.refl_tp this.2.wf_ctx.inv_snoc, EqTp.refl_tp this.2⟩
  . grind
  . grind
  . rename_i ih _ _ _ _ _ ih'
    obtain ⟨_, _, rfl, rfl, eq₁, eq₂⟩ := ih'.1 rfl
    obtain ⟨_, _, _, rfl, _, eq₃⟩ := ih.1 rfl
    refine ⟨_, _, rfl, rfl, ?_, ?_⟩
    . grind [EqTp.trans_tp]
    . apply eq₂.trans_tp (eq₃.conv_ctx <| eq₁.wf_ctx.eq_self.snoc _)
      grind [EqTp.trans_tp]
  . rename_i ih _ _ _ _ _ ih'
    obtain ⟨_, _, rfl, rfl, eq₁, eq₂⟩ := ih'.2 rfl
    obtain ⟨_, _, _, rfl, _, eq₃⟩ := ih.2 rfl
    refine ⟨_, _, rfl, rfl, ?_, ?_⟩
    . grind [EqTp.trans_tp]
    . apply eq₂.trans_tp (eq₃.conv_ctx <| eq₁.wf_ctx.eq_self.snoc _)
      grind [EqTp.trans_tp]

/-- Injectivity of Σ types. -/
theorem EqTp.inv_sigma {Γ A B A' B' l₀ l₁ l₂ l₁' l₂'} :
    Γ ⊢[l₀] .sigma l₁ l₂ A B ≡ .sigma l₁' l₂' A' B' →
    l₀ = max l₁ l₂ ∧ l₁ = l₁' ∧ l₂ = l₂' ∧
    (Γ ⊢[l₁] A ≡ A') ∧ ((A, l₁) :: Γ ⊢[l₂] B ≡ B') := by
  grind [strong_sigmaInj]
