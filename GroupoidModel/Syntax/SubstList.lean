import GroupoidModel.Syntax.Substitution

/-! # Substitutions from lists of terms -/

/-- The action of substitutions is determined by their action on bound variables. -/
/- This has stronger assumptions than necessary:
only well-scopedness or `i < maxBvar` is actually needed;
but I can't be bothered defining either. -/
theorem sb_irrel :
    (∀ {Γ l A}, Γ ⊢[l] A →
      ∀ (σ σ'), (∀ i < Γ.length, σ i = σ' i) → A.subst σ = A.subst σ') ∧
    (∀ {Γ l A t}, Γ ⊢[l] t : A →
      ∀ (σ σ'), (∀ i < Γ.length, σ i = σ' i) → t.subst σ = t.subst σ') := by
  have helper {σ σ' n} (h : ∀ i < n, σ i = σ' i) : ∀ i < n + 1, Expr.up σ i = Expr.up σ' i := by
    intro i lt
    rw [Expr.up_eq_snoc, Expr.up_eq_snoc]
    cases i
    . simp
    . simp [Expr.comp, h _ (Nat.succ_lt_succ_iff.mp lt)]
  mutual_induction WfTp
  all_goals intros; try exact True.intro
  case bvar lk _ _ _ h =>
    have := h _ lk.lt_length
    simp [Expr.subst, this]
  case conv => solve_by_elim
  all_goals dsimp [Expr.subst, List.length_cons] at *; try congr 1 <;> solve_by_elim

/-! ## Substitutions from lists of expressions -/

/-- The substitution `Δ ⊢ sbOfTms ts 0 : Aₙ.….A₁` corresponds to a list of terms
`Δ ⊢ ts[ts.length - 1] : Aₙ`
`Δ ⊢ ts[ts.length - 2] : Aₙ₋₁[ts[ts.length - 1]]`
⋮
`Δ ⊢ ts[0] : A₁[…]`.

The shift parameter `k` is just a formal device to obtain nicer lemmas. -/
def sbOfTms (ts : List Expr) (k := 0) : Nat → Expr :=
  fun i => ts[i]?.getD (Expr.bvar <| i + k)

@[autosubst]
theorem sbOfTms_nil : sbOfTms [] = Expr.bvar := by
  ext i; simp [sbOfTms]

@[autosubst]
theorem sbOfTms_cons (t ts k) :
    sbOfTms (t :: ts) k = Expr.snoc (sbOfTms ts (k + 1)) t := by
  ext i; cases i
  . simp [sbOfTms]
  . dsimp [sbOfTms]; congr 2; omega

@[autosubst]
theorem sbOfTms_map_wk (ts k) :
    sbOfTms (ts.map (·.subst Expr.wk)) (k+1) = Expr.comp Expr.wk (sbOfTms ts k) := by
  ext i
  unfold sbOfTms
  rw [show (Expr.bvar (i + (k + 1))) = (Expr.bvar (i + k)).subst Expr.wk from rfl]
  simp [Expr.comp]

theorem up_sbOfTms (ts k) :
    Expr.up (sbOfTms ts k) = sbOfTms (.bvar 0 :: ts.map (·.subst Expr.wk)) k := by
  autosubst

theorem sbOfTms_get_eq (ts k i) : i < ts.length → sbOfTms ts k i = sbOfTms ts 0 i := by
  intro
  rw [sbOfTms, sbOfTms, List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩]
  simp

/-- When the list of terms covers all variables, the shift `k` is irrelevant. -/
theorem WfTp.sbOfTms_irrel {Γ l A ts} (wf : Γ ⊢[l] A) (le : Γ.length ≤ ts.length) (k) :
    A.subst (sbOfTms ts k) = A.subst (sbOfTms ts 0) :=
  sb_irrel.1 wf (sbOfTms ts k) (sbOfTms ts 0) fun i _ => sbOfTms_get_eq ts k i (by omega)

/-- When the list of terms covers all variables, the shift `k` is irrelevant. -/
theorem WfTm.sbOfTms_irrel {Γ l A t ts} (wf : Γ ⊢[l] t : A) (le : Γ.length ≤ ts.length) (k) :
    t.subst (sbOfTms ts k) = t.subst (sbOfTms ts 0) :=
  sb_irrel.2 wf (sbOfTms ts k) (sbOfTms ts 0) fun i _ => sbOfTms_get_eq ts k i (by omega)
