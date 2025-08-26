import GroupoidModel.Syntax.Inversion

variable {χ : Type*} {E : Axioms χ} {Δ Δ' Γ Γ' Γ'' : Ctx χ}
  {A A' B B' t t' u : Expr χ} {σ : Nat → Expr χ}
  {i l l' : Nat}

/-! ## Context equality -/

variable (E : Axioms χ) in
/-- The two contexts are judgmentally equal. -/
inductive EqCtx : Ctx χ → Ctx χ → Prop
  | nil : EqCtx [] []
  /-- Prefer using `EqCtx.snoc`. -/
  | snoc' {Γ Γ' A A' l} :
    EqCtx Γ Γ' → E ∣ Γ ⊢[l] A ≡ A' → E ∣ Γ' ⊢[l] A ≡ A' → EqCtx ((A, l) :: Γ) ((A', l) :: Γ')

theorem EqCtx.refl : WfCtx E Γ → EqCtx E Γ Γ := by
  revert Γ; mutual_induction WfCtx <;> grind [EqCtx.nil, EqCtx.snoc', EqTp.refl_tp]

theorem WfCtx.eq_self : WfCtx E Γ → EqCtx E Γ Γ := EqCtx.refl

theorem WfCtx.sb_self : WfCtx E Γ → WfSb E Γ Expr.bvar Γ := WfSb.id

theorem EqCtx.symm : EqCtx E Γ Γ' → EqCtx E Γ' Γ := by
  intro h; induction h <;> grind [EqCtx.nil, EqCtx.snoc', EqTp.symm_tp]

theorem EqCtx.length_eq : EqCtx E Γ Γ' → Γ.length = Γ'.length := by
  intro eq; induction eq <;> simp [*]

theorem EqCtx.inv_snoc {A l} : EqCtx E ((A, l) :: Γ) Γ' →
    ∃ Γ'' A', Γ' = ((A', l) :: Γ'') ∧ EqCtx E Γ Γ'' ∧ (E ∣ Γ ⊢[l] A ≡ A') := by
  grind [cases EqCtx]

variable [Fact E.Wf]

theorem EqCtx.wf_left : EqCtx E Γ Γ' → WfCtx E Γ := by
  intro eq; induction eq <;> grind [WfCtx.nil, WfCtx.snoc, EqTp.wf_ctx, EqTp.wf_left]

theorem EqCtx.wf_right : EqCtx E Γ Γ' → WfCtx E Γ' := by
  intro eq; induction eq <;> grind [WfCtx.nil, WfCtx.snoc, EqTp.wf_ctx, EqTp.wf_right]

theorem EqCtx.wf_sb : EqCtx E Γ Γ' → WfSb E Γ Expr.bvar Γ' := by
  intro h
  induction h
  case nil => exact WfSb.id WfCtx.nil
  case snoc' Γ Γ' A A' l _ eq eq' sb =>
    have wk : WfSb E ((A, l) :: Γ) Expr.wk Γ := WfSb.wk eq.wf_left
    have wk' : WfSb E ((A, l) :: Γ) Expr.wk Γ' := WfSb.comp wk sb
    have : WfSb E ((A, l) :: Γ) (Expr.snoc Expr.wk (Expr.bvar 0)) ((A', l) :: Γ') := by
      apply WfSb.snoc wk' eq'.wf_right
      have := WfTm.bvar (eq.wf_ctx.snoc eq.wf_left) (Lookup.zero ..)
      exact this.conv (eq.subst wk)
    convert this using 1; autosubst

theorem WfTp.conv_ctx : EqCtx E Γ Γ' → E ∣ Γ ⊢[l] A → E ∣ Γ' ⊢[l] A := by
  intro eq A
  convert A.subst eq.symm.wf_sb using 1 <;> autosubst

theorem WfTm.conv_ctx : EqCtx E Γ Γ' → E ∣ Γ ⊢[l] t : A → E ∣ Γ' ⊢[l] t : A := by
  intro eq t
  convert t.subst eq.symm.wf_sb using 1 <;> autosubst

theorem EqTp.conv_ctx : EqCtx E Γ Γ' → E ∣ Γ ⊢[l] A ≡ B → E ∣ Γ' ⊢[l] A ≡ B := by
  intro eq AB
  convert AB.subst eq.symm.wf_sb using 1 <;> autosubst

theorem EqTm.conv_ctx : EqCtx E Γ Γ' → E ∣ Γ ⊢[l] t ≡ u : A → E ∣ Γ' ⊢[l] t ≡ u : A := by
  intro eq tu
  convert tu.subst eq.symm.wf_sb using 1 <;> autosubst

theorem WfSb.conv_dom : EqCtx E Δ Δ' → WfSb E Δ σ Γ → WfSb E Δ' σ Γ := by
  intro eq σ
  convert eq.symm.wf_sb.comp σ using 1 <;> autosubst

theorem WfSb.conv_cod : EqCtx E Γ Γ' → WfSb E Δ σ Γ → WfSb E Δ σ Γ' := by
  intro eq σ
  exact σ.comp eq.wf_sb

theorem EqCtx.snoc : EqCtx E Γ Γ' → E ∣ Γ ⊢[l] A ≡ A' → EqCtx E ((A, l) :: Γ) ((A', l) :: Γ') :=
  fun Γ A => .snoc' Γ A (A.conv_ctx Γ)

theorem EqCtx.trans : EqCtx E Γ Γ' → EqCtx E Γ' Γ'' → EqCtx E Γ Γ'' := by
  intro h h'; induction h generalizing Γ''
  . assumption
  . have := h'.inv_snoc
    grind [EqCtx.snoc, EqCtx.symm, EqTp.trans_tp, EqTp.conv_ctx]

theorem EqCtx.lookup_eq : EqCtx E Γ Γ' →
    Lookup Γ i A l → Lookup Γ' i A' l' → l = l' ∧ (E ∣ Γ ⊢[l] A ≡ A') := by
  intro eq lk lk'
  induction lk generalizing Γ' A'
  . cases lk'
    have ⟨_, _, _, _, eqA⟩ := eq.inv_snoc
    have := eqA.subst (WfSb.wk eqA.wf_left)
    grind
  . rename_i ih
    rcases lk' with _ | ⟨_, _, lk'⟩
    have ⟨_, _, h, eq, eqB⟩ := eq.inv_snoc
    cases h
    have := (ih eq lk').2.subst (WfSb.wk eqB.wf_left)
    grind

/-! ## Single-binder conversion -/

theorem WfTp.conv_binder : E ∣ (A, l) :: Γ ⊢[l'] B → E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A', l) :: Γ ⊢[l'] B :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem WfTm.conv_binder : E ∣ (A, l) :: Γ ⊢[l'] t : B → E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A', l) :: Γ ⊢[l'] t : B :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem EqTp.conv_binder : E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' → E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A', l) :: Γ ⊢[l'] B ≡ B' :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem EqTm.conv_binder : E ∣ (A, l) :: Γ ⊢[l'] t ≡ t' : B → E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A', l) :: Γ ⊢[l'] t ≡ t' : B :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem WfSb.conv_dom_binder : WfSb E ((A, l) :: Γ) σ Δ → E ∣ Γ ⊢[l] A ≡ A' →
    WfSb E ((A', l) :: Γ) σ Δ :=
  fun h eq => h.conv_dom (eq.wf_ctx.eq_self.snoc eq)

theorem WfSb.conv_cod_binder : WfSb E Γ σ ((A, l) :: Δ) → E ∣ Δ ⊢[l] A ≡ A' →
    WfSb E Γ σ ((A', l) :: Δ) :=
  fun h eq => h.conv_cod (eq.wf_ctx.eq_self.snoc eq)
