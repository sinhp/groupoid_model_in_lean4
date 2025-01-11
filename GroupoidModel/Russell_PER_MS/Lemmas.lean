import GroupoidModel.Russell_PER_MS.Typing

/-! Basic syntactic metatheory. -/

theorem EqTp.le_univMax {Γ A B l} : Γ ⊢[l] A ≡ B → l ≤ univMax := by
  apply @EqTp.rec (fun _ l _ _ _ => l ≤ univMax) (fun _ l _ _ _ _ => l ≤ univMax)
  all_goals intros; first| trivial | omega

theorem EqTm.le_univMax {Γ A t u l} : Γ ⊢[l] t ≡ u : A → l ≤ univMax := by
  apply @EqTm.rec (fun _ l _ _ _ => l ≤ univMax) (fun _ l _ _ _ _ => l ≤ univMax)
  all_goals intros; first| trivial | omega

theorem EqTp.wf_left {Γ A B l} : Γ ⊢[l] A ≡ B → Γ ⊢[l] A :=
  fun h => .trans h (.symm h)

theorem EqTp.wf_right {Γ A B l} : Γ ⊢[l] A ≡ B → Γ ⊢[l] B :=
  fun h => .trans (.symm h) h

theorem EqTm.wf_left {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] t : A :=
  fun h => .trans h (.symm h)

theorem EqTm.wf_right {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] u : A :=
  fun h => .trans (.symm h) h

theorem EqTm.wf_tp {Γ A t u l} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] A := by
  apply @EqTm.rec
    (fun _ _ _ _ _ => True)
    (fun Γ l _ _ A _ => Γ ⊢[l] A)
  all_goals intros; try trivial
  case cong_lam A_eq _ _ B_wf =>
    exact .cong_pi A_eq.wf_left B_wf
  case cong_app B_eq _ a_eq _ _ _ =>
    exact (EqTp.inst B_eq a_eq).wf_left
  case cong_code =>
    apply EqTp.cong_univ; assumption
  case inst a_eq B_wf _ =>
    exact (EqTp.inst B_wf a_eq).wf_left
  case app_lam u_wf B_wf _ =>
    exact EqTp.inst B_wf u_wf
  case conv A_eq _ _ _ =>
    exact A_eq.wf_right
