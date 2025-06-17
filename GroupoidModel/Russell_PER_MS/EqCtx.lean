import GroupoidModel.Russell_PER_MS.Inversion

/-! ## Context equality -/

/-- The two contexts are judgmentally equal. -/
inductive EqCtx : Ctx → Ctx → Prop
  | nil : EqCtx [] []
  /-- Prefer using `EqCtx.snoc`. -/
  | snoc' {Γ Γ' A A' l} :
    EqCtx Γ Γ' → Γ ⊢[l] A ≡ A' → Γ' ⊢[l] A ≡ A' → EqCtx ((A, l) :: Γ) ((A', l) :: Γ')

theorem EqCtx.refl {Γ} : WfCtx Γ → EqCtx Γ Γ := by
  revert Γ; mutual_induction WfCtx <;> grind [EqCtx.nil, EqCtx.snoc', EqTp.refl_tp]

theorem WfCtx.eq_self {Γ} : WfCtx Γ → EqCtx Γ Γ := EqCtx.refl

theorem EqCtx.symm {Γ Γ'} : EqCtx Γ Γ' → EqCtx Γ' Γ := by
  intro h; induction h <;> grind [EqCtx.nil, EqCtx.snoc', EqTp.symm_tp]

theorem EqCtx.wf_left {Γ Γ'} : EqCtx Γ Γ' → WfCtx Γ := by
  intro eq; induction eq <;> grind [WfCtx.nil, WfCtx.snoc, EqTp.wf_ctx, EqTp.wf_left]

theorem EqCtx.wf_right {Γ Γ'} : EqCtx Γ Γ' → WfCtx Γ' := by
  intro eq; induction eq <;> grind [WfCtx.nil, WfCtx.snoc, EqTp.wf_ctx, EqTp.wf_right]

theorem EqCtx.length_eq {Γ Γ'} : EqCtx Γ Γ' → Γ.length = Γ'.length := by
  intro eq; induction eq <;> simp [*]

theorem EqCtx.inv_snoc {Γ Γ' A l} : EqCtx ((A, l) :: Γ) Γ' →
    ∃ Γ'' A', Γ' = ((A', l) :: Γ'') ∧ EqCtx Γ Γ'' ∧ (Γ ⊢[l] A ≡ A') := by
  grind [cases EqCtx]

theorem EqCtx.wf_sb {Γ Γ'} : EqCtx Γ Γ' → WfSb Γ Expr.bvar Γ' := by
  intro h
  induction h
  case nil => exact WfSb.id WfCtx.nil
  case snoc' Γ Γ' A A' l _ eq eq' sb =>
    have wk : WfSb ((A, l) :: Γ) Expr.wk Γ := WfSb.wk eq.wf_left
    have wk' : WfSb ((A, l) :: Γ) Expr.wk Γ' := WfSb.comp wk sb
    have : WfSb ((A, l) :: Γ) (Expr.snoc Expr.wk (Expr.bvar 0)) ((A', l) :: Γ') := by
      apply WfSb.snoc wk' eq'.wf_right
      have := WfTm.bvar (eq.wf_ctx.snoc eq.wf_left) (Lookup.zero ..)
      exact this.conv (eq.subst wk)
    convert this using 1; autosubst

theorem WfTp.conv_ctx {Γ Γ' A l} : EqCtx Γ Γ' → Γ ⊢[l] A → Γ' ⊢[l] A := by
  intro eq A
  convert A.subst eq.symm.wf_sb using 1 <;> autosubst

theorem WfTm.conv_ctx {Γ Γ' t A l} : EqCtx Γ Γ' → Γ ⊢[l] t : A → Γ' ⊢[l] t : A := by
  intro eq t
  convert t.subst eq.symm.wf_sb using 1 <;> autosubst

theorem EqTp.conv_ctx {Γ Γ' A B l} : EqCtx Γ Γ' → Γ ⊢[l] A ≡ B → Γ' ⊢[l] A ≡ B := by
  intro eq AB
  convert AB.subst eq.symm.wf_sb using 1 <;> autosubst

theorem EqTm.conv_ctx {Γ Γ' t u A l} : EqCtx Γ Γ' → Γ ⊢[l] t ≡ u : A → Γ' ⊢[l] t ≡ u : A := by
  intro eq tu
  convert tu.subst eq.symm.wf_sb using 1 <;> autosubst

theorem WfSb.conv_dom {Δ Δ' Γ σ} : EqCtx Δ Δ' → WfSb Δ σ Γ → WfSb Δ' σ Γ := by
  intro eq σ
  convert eq.symm.wf_sb.comp σ using 1 <;> autosubst

theorem WfSb.conv_cod {Δ Γ Γ' σ} : EqCtx Γ Γ' → WfSb Δ σ Γ → WfSb Δ σ Γ' := by
  intro eq σ
  exact σ.comp eq.wf_sb

theorem EqCtx.snoc {Γ Γ' A A' l} :
    EqCtx Γ Γ' → Γ ⊢[l] A ≡ A' → EqCtx ((A, l) :: Γ) ((A', l) :: Γ') :=
  fun Γ A => .snoc' Γ A (A.conv_ctx Γ)

theorem EqCtx.trans {Γ Γ' Γ''} : EqCtx Γ Γ' → EqCtx Γ' Γ'' → EqCtx Γ Γ'' := by
  intro h h'; induction h generalizing Γ'' <;>
    grind [EqCtx.snoc, EqCtx.symm, EqTp.trans_tp, EqTp.conv_ctx, EqCtx.inv_snoc]

theorem EqCtx.lookup_eq {Γ Γ' A A' i l l'} : EqCtx Γ Γ' →
    Lookup Γ i A l → Lookup Γ' i A' l' → l = l' ∧ (Γ ⊢[l] A ≡ A') := by
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

theorem WfTp.conv_binder {Γ A A' B l} : (A, l) :: Γ ⊢[l] B → Γ ⊢[l] A ≡ A' →
    (A', l) :: Γ ⊢[l] B :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem WfTm.conv_binder {Γ A A' B t l} : (A, l) :: Γ ⊢[l] t : B → Γ ⊢[l] A ≡ A' →
    (A', l) :: Γ ⊢[l] t : B :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem EqTp.conv_binder {Γ A A' B B' l} : (A, l) :: Γ ⊢[l] B ≡ B' → Γ ⊢[l] A ≡ A' →
    (A', l) :: Γ ⊢[l] B ≡ B' :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem EqTm.conv_binder {Γ A A' B t t' l} : (A, l) :: Γ ⊢[l] t ≡ t' : B → Γ ⊢[l] A ≡ A' →
    (A', l) :: Γ ⊢[l] t ≡ t' : B :=
  fun h eq => h.conv_ctx (eq.wf_ctx.eq_self.snoc eq)

theorem WfSb.conv_dom_binder {Δ Γ A A' σ l} : WfSb ((A, l) :: Γ) σ Δ → Γ ⊢[l] A ≡ A' →
    WfSb ((A', l) :: Γ) σ Δ :=
  fun h eq => h.conv_dom (eq.wf_ctx.eq_self.snoc eq)

theorem WfSb.conv_cod_binder {Δ Γ A A' σ l} : WfSb Γ σ ((A, l) :: Δ) → Δ ⊢[l] A ≡ A' →
    WfSb Γ σ ((A', l) :: Δ) :=
  fun h eq => h.conv_cod (eq.wf_ctx.eq_self.snoc eq)
