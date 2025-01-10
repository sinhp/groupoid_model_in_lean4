import GroupoidModel.TypeTheory.Russell_PER_ES.Basic

/-! Syntactic metatheory. -/

theorem EqSubst.wf_left {Δ Γ σ σ'} : Δ ⊢ₛ σ ≡ σ' : Γ → Δ ⊢ₛ σ : Γ :=
  fun h => .trans h (.symm h)

theorem EqSubst.wf_right {Δ Γ σ σ'} : Δ ⊢ₛ σ ≡ σ' : Γ → Δ ⊢ₛ σ' : Γ :=
  fun h => .trans (.symm h) h

theorem EqExpr.le_univMax {Γ A t u l} : Γ ⊢[l] t ≡ u : A → l ≤ univMax + 1 := by
  apply @EqExpr.rec (fun _ _ _ _ _ => True) (fun _ l _ _ _ _ => l ≤ univMax + 1)
  all_goals intros; first| trivial | omega

theorem EqExpr.wf_left {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] t : A :=
  fun h => .trans h (.symm h)

theorem EqExpr.wf_right {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] u : A :=
  fun h => .trans (.symm h) h

theorem EqExpr.sb_id {Γ A t l} : Γ ⊢[l] t : A → Γ ⊢[l] t.sb .id ≡ t : A := by
  apply @EqExpr.rec
    (fun _ _ _ _ _ => True)
    (fun Γ l t _ A _ => Γ ⊢[l] t.sb .id ≡ t : A)
  all_goals intros; try exact True.intro
  case cong_bvar AUl l _ =>
    exact .bvar_id (.cong_bvar AUl l)
  case cong_pi Γ A _ _ _ _ _ AUl BUl' _ _ =>
    apply EqExpr.trans (.pi_sb .cong_id AUl.wf_left BUl'.wf_left)
    apply EqExpr.cong_pi
    assumption
    have : A :: Γ ⊢ₛ ((Subst.wk A).ext (Expr.bvar 0)) ≡ .id : A :: Γ :=
      -- I am not sure that this is provable.
      -- In Abadi '91, it is suggested as an additional rule VarShift.
      sorry
    sorry
  all_goals sorry

theorem EqExpr.cong_univ {Γ l} : l < univMax → Γ ⊢[l+2] .univ l : .univ (l+1) :=
  fun h =>
    have : Γ ⊢ₛ .id : Γ := .cong_id
    have := .univ_sb this h
    .trans (.symm this) this

theorem EqExpr.cong_sb_univ {Δ Γ σ σ' A A' l} :
    Γ ⊢[l+1] A ≡ A' : .univ l → Δ ⊢ₛ σ ≡ σ' : Γ →
    Δ ⊢[l+1] A.sb σ ≡ A'.sb σ' : .univ l := by
  intro AUl σΓ
  have Aσ : Δ ⊢[l + 1] A.sb σ ≡ A'.sb σ' : (Expr.univ l).sb σ :=
    .cong_sb AUl σΓ
  by_cases l_eq : l = univMax
  . cases l_eq
    exact .conv_univMax Aσ
  . have := Aσ.le_univMax
    exact .conv (.univ_sb σΓ.wf_left (by omega)) Aσ

theorem EqExpr.sb_sb_univ {Θ Δ Γ ρ σ A l} :
    Θ ⊢ₛ ρ : Δ →
    Δ ⊢ₛ σ : Γ →
    Γ ⊢[l+1] A : .univ l →
    Θ ⊢[l+1] .sb (.sb A σ) ρ ≡ .sb A (.comp ρ σ) : .univ l := by
  intro ρΔ σΓ Al
  have eq := EqExpr.sb_sb ρΔ σΓ Al
  by_cases l_eq : l = univMax
  . cases l_eq
    exact .conv_univMax eq
  . have := eq.le_univMax
    exact .conv (.univ_sb (.cong_comp ρΔ σΓ) (by omega)) eq

theorem EqExpr.id_ext {Γ A a a' l} :
    Γ ⊢[l] a ≡ a' : A →
  -- This casing is scuffed. We ought to do something more uniform.
    (Γ ⊢[l+1] A : .univ l) ∨ (l = univMax + 1) →
    Γ ⊢ₛ Subst.id.ext a ≡ Subst.id.ext a' : A :: Γ := by
  intro aA Atp
  cases Atp with
  | inl AUl =>
    exact .cong_ext .cong_id <|
      .conv (.symm <| sb_id AUl) aA
  | inr l_eq =>
    cases l_eq
    exact .cong_ext_univMax .cong_id (.conv_univMax aA)

theorem EqExpr.wfTp {Γ A t u l} :
    Γ ⊢[l] t ≡ u : A → (Γ ⊢[l+1] A : .univ l) ∨ (l = univMax + 1) := by
  apply @EqExpr.rec
    (fun _ _ _ _ _ => True)
    (fun Γ l _ _ A _ => (Γ ⊢[l+1] A : .univ l) ∨ (l = univMax + 1))
  all_goals intros; try trivial
  case cong_bvar h _ _ => exact .inl h
  case cong_pi l l' Ul Ul' _ _ | pi_sb l l' _ Ul Ul' _ _ _ =>
    -- TODO: is there a tactic like `by_decide`?
    by_cases h : max l l' = univMax
    . apply Or.inr; rw [h]
    . have := Ul.le_univMax
      have := Ul'.le_univMax
      exact .inl <| .cong_univ <| by omega
  case cong_lam AUl _ _ tB_ih =>
    cases tB_ih with
    | inl h => exact .inl <| .cong_pi AUl.wf_left h
    | inr => have := AUl.le_univMax; omega
  case cong_app Γ A _ _ _ _ a _ _ _ BUl' _ aA _ _ aA_ih =>
    exact .inl <| .cong_sb_univ BUl'.wf_left <|
      id_ext aA.wf_left aA_ih
  case conv AUl _ _ _ => exact .inl AUl.wf_right
  case cong_sb σΓ tA_ih _ =>
    cases tA_ih with
    | inr h => exact .inr h
    | inl AUl => exact .inl <| .cong_sb_univ AUl σΓ.wf_left
  case conv_univMax => exact .inr rfl
  case app_lam BUl' _ uA _ _ uA_ih =>
    exact .inl <| .cong_sb_univ BUl'.wf_left <| id_ext uA uA_ih
  case bvar_wk AUl BUl' _ _ _ _ =>
    exact .inl <| .cong_sb_univ AUl.wf_left <| .cong_wk BUl'
  case lam_sb Δ Γ σ A B t l l' σΓ AUl BUl' _ _ _ _ tB_ih =>
    have AσUl : Δ ⊢[l+1] A.sb σ : .univ l :=
      .cong_sb_univ AUl σΓ
    have wkΔ : A.sb σ :: Δ ⊢ₛ (Subst.wk (A.sb σ)) : Δ :=
      .cong_wk AσUl
    have wkCompΓ : A.sb σ :: Δ ⊢ₛ (Subst.wk (A.sb σ)).comp σ : Γ :=
      .cong_comp wkΔ σΓ
    have bv0 : A.sb σ :: Δ ⊢[l] Expr.bvar 0 : ((A.sb σ).sb (Subst.wk (A.sb σ))) :=
      .cong_bvar (.cong_sb_univ (.cong_sb_univ AUl σΓ) wkΔ) .zero
    have bv0' : A.sb σ :: Δ ⊢[l] Expr.bvar 0 : A.sb ((Subst.wk (A.sb σ)).comp σ) :=
      .conv (.sb_sb_univ wkΔ σΓ AUl) bv0
    have : A.sb σ :: Δ ⊢ₛ ((Subst.wk (A.sb σ)).comp σ).ext (Expr.bvar 0) : A :: Γ :=
      .cong_ext (l := l) wkCompΓ bv0'
    exact .inl <| .cong_pi AσUl (.cong_sb_univ BUl' this)
  case app_sb σΓ BUl _ aA _ _ _ _ =>
    exact .inl <| .cong_sb_univ BUl <| .cong_ext σΓ <| .cong_sb aA σΓ
  case univ_sb l _ _ _ =>
    by_cases l_eq : l + 1 = univMax
    . omega
    . exact Or.inl <| cong_univ (by omega)
  case sb_sb ρΔ σΓ _ _ _ tA_ih =>
    cases tA_ih with
    | inr h => exact .inr h
    | inl AUl => exact .inl <| .cong_sb_univ AUl (.cong_comp ρΔ σΓ)

-- Q: is this hard?
-- theorem EqExpr.eq_of_univMax {Γ A t u} : Γ ⊢[univMax+1] t ≡ u : A → A = .univ univMax :=
--   sorry
