import Mathlib.Tactic.Convert
import GroupoidModel.Russell_PER_MS.Typing

/-! # Syntactic metatheory

This version uses `Autosubst.lean`. -/

set_option grind.warning false

/-- Proof by mutual induction on typing judgments. -/
local macro "mutual_induction" : tactic =>
  `(tactic| (
    refine ⟨
      -- beautiful
      @WfCtx.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi ?sigma ?univ ?el
        ?cong_pi ?cong_sigma ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam ?app ?pair ?fst ?snd ?code ?conv
        ?cong_lam ?cong_app ?cong_pair ?cong_fst ?cong_snd ?cong_code
        ?app_lam ?fst_pair ?snd_pair ?lam_app ?pair_fst_snd ?conv_tm ?refl_tm ?symm_tm ?trans_tm,
      @WfTp.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi ?sigma ?univ ?el
        ?cong_pi ?cong_sigma ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam ?app ?pair ?fst ?snd ?code ?conv
        ?cong_lam ?cong_app ?cong_pair ?cong_fst ?cong_snd ?cong_code
        ?app_lam ?fst_pair ?snd_pair ?lam_app ?pair_fst_snd ?conv_tm ?refl_tm ?symm_tm ?trans_tm,
      @EqTp.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi ?sigma ?univ ?el
        ?cong_pi ?cong_sigma ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam ?app ?pair ?fst ?snd ?code ?conv
        ?cong_lam ?cong_app ?cong_pair ?cong_fst ?cong_snd ?cong_code
        ?app_lam ?fst_pair ?snd_pair ?lam_app ?pair_fst_snd ?conv_tm ?refl_tm ?symm_tm ?trans_tm,
      @WfTm.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi ?sigma ?univ ?el
        ?cong_pi ?cong_sigma ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam ?app ?pair ?fst ?snd ?code ?conv
        ?cong_lam ?cong_app ?cong_pair ?cong_fst ?cong_snd ?cong_code
        ?app_lam ?fst_pair ?snd_pair ?lam_app ?pair_fst_snd ?conv_tm ?refl_tm ?symm_tm ?trans_tm,
      @EqTm.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi ?sigma ?univ ?el
        ?cong_pi ?cong_sigma ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam ?app ?pair ?fst ?snd ?code ?conv
        ?cong_lam ?cong_app ?cong_pair ?cong_fst ?cong_snd ?cong_code
        ?app_lam ?fst_pair ?snd_pair ?lam_app ?pair_fst_snd ?conv_tm ?refl_tm ?symm_tm ?trans_tm
    ⟩
    all_goals dsimp only; try intros
  ))

/-- Try solving each inductive case by its respective constructor passed to `grind`. -/
-- TODO: can the script be shortened? metaprogram a generator for the cases?
local macro "grind_cases" : tactic =>
  `(tactic| (
    try case pi => grind [WfTp.pi]
    try case sigma => grind [WfTp.sigma]
    try case univ => grind [WfTp.univ]
    try case el => grind [WfTp.el]
    try case cong_pi => grind [EqTp.cong_pi]
    try case cong_sigma => grind [EqTp.cong_sigma]
    try case cong_el => grind [EqTp.cong_el]
    try case refl_tp => grind [EqTp.refl_tp]
    try case symm_tp => grind [EqTp.symm_tp]
    try case trans_tp => grind [EqTp.trans_tp]
    try case lam => grind [WfTm.lam]
    try case app => grind [WfTm.app]
    try case pair => grind [WfTm.pair]
    try case fst => grind [WfTm.fst]
    try case snd => grind [WfTm.snd]
    try case code => grind [WfTm.code]
    try case conv => grind [WfTm.conv]
    try case cong_lam => grind [EqTm.cong_lam]
    try case cong_app => grind [EqTm.cong_app]
    try case cong_pair => grind [EqTm.cong_pair]
    try case cong_fst => grind [EqTm.cong_fst]
    try case cong_snd => grind [EqTm.cong_snd]
    try case cong_code => grind [EqTm.cong_code]
    try case app_lam => grind [EqTm.app_lam]
    try case fst_pair => grind [EqTm.fst_pair]
    try case snd_pair => grind [EqTm.snd_pair]
    try case pair_fst_snd => grind [EqTm.pair_fst_snd]
    try case conv_tm => grind [EqTm.conv_tm]
    try case refl_tm => grind [EqTm.refl_tm]
    try case symm_tm => grind [EqTm.symm_tm]
    try case trans_tm => grind [EqTm.trans_tm]
    try case lam_app => grind [EqTm.lam_app]
  ))

/-! ## Universe level bounds -/

attribute [local grind cases] Lookup in
theorem le_univMax_all :
    (∀ {Γ}, WfCtx Γ → ∀ {A i l}, Lookup Γ i A l → l ≤ univMax) ∧
    (∀ {Γ l A}, Γ ⊢[l] A → l ≤ univMax) ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B → l ≤ univMax) ∧
    (∀ {Γ l t A}, Γ ⊢[l] t : A → l ≤ univMax) ∧
    (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A → l ≤ univMax) := by
  mutual_induction
  -- I ❤ grind and omega
  all_goals first | omega | grind

theorem WfCtx.le_univMax {Γ i A l} : WfCtx Γ → Lookup Γ i A l → l ≤ univMax :=
  fun h h' => le_univMax_all.1 h h'

theorem EqTp.le_univMax {Γ A B l} : Γ ⊢[l] A ≡ B → l ≤ univMax :=
  le_univMax_all.2.2.1

theorem WfTp.le_univMax {Γ A l} : Γ ⊢[l] A → l ≤ univMax :=
  le_univMax_all.2.1

theorem WfTm.le_univMax {Γ t A l} : Γ ⊢[l] t : A → l ≤ univMax :=
  le_univMax_all.2.2.2.1

theorem EqTm.le_univMax {Γ t u A l} : Γ ⊢[l] t ≡ u : A → l ≤ univMax :=
  le_univMax_all.2.2.2.2

/-! ## Admissibility of renaming -/

/-- The renaming `ξ : Δ ⟶ Γ` is well-formed. See `WfSb` for general substitutions. -/
def WfRen (Δ : Ctx) (ξ : Nat → Nat) (Γ : Ctx) :=
  ∀ {i A l}, Lookup Γ i A l → Lookup Δ (ξ i) (A.rename ξ) l

namespace WfRen

theorem wk (Γ A l) : WfRen ((A,l) :: Γ) Nat.succ Γ := by
  intro _ _ _ lk
  convert Lookup.succ _ _ lk
  autosubst

theorem up {Δ Γ A ξ l} : WfRen Δ ξ Γ → Γ ⊢[l] A →
    WfRen ((A.rename ξ, l) :: Δ) (Expr.upr ξ) ((A, l) :: Γ) := by
  intro wf _ _ _ _ lk
  cases lk
  . rw [show (A.subst Expr.wk).rename (Expr.upr ξ) = (A.rename ξ).subst Expr.wk by autosubst]
    apply Lookup.zero
  . rename_i A _ lk
    rw [show (A.subst Expr.wk).rename (Expr.upr ξ) = (A.rename ξ).subst Expr.wk by autosubst]
    apply Lookup.succ _ _ (wf lk)

attribute [local grind] WfCtx.snoc in
attribute [local grind] WfRen.up in
theorem rename_all :
    (∀ {Γ}, WfCtx Γ → True) ∧
    (∀ {Γ l A}, Γ ⊢[l] A →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] A.rename ξ) ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] A.rename ξ ≡ B.rename ξ) ∧
    (∀ {Γ l t A}, Γ ⊢[l] t : A →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] t.rename ξ : A.rename ξ) ∧
    (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] t.rename ξ ≡ u.rename ξ : A.rename ξ) := by
  -- `grind` will pick this up to simplify goals.
  have ih_subst (B a : Expr) (ξ) :
      (B.subst a.toSb).rename ξ = (B.rename (Expr.upr ξ)).subst (a.rename ξ).toSb := by autosubst
  mutual_induction
  case snoc => exact True.intro
  all_goals try dsimp [Expr.rename] at *
  case bvar sb => apply WfTm.bvar _ (sb _) <;> assumption
  grind_cases
  -- Cases that didn't go through automatically.
  case snd => rw [ih_subst]; apply WfTm.snd <;> grind
  case cong_snd => rw [ih_subst]; apply EqTm.cong_snd <;> grind
  case lam_app ihf _ _ Δwf ξwf => simpa only [autosubst] using EqTm.lam_app (ihf Δwf ξwf)

end WfRen

/-! ## Admissibility of substitution -/

/-- The substitution `σ : Δ ⟶ Γ` is well-formed.

We use a functional definition as in the Autosubst paper.
A common alternative is to use an inductive characterization. -/
def WfSb (Δ : Ctx) (σ : Nat → Expr) (Γ : Ctx) :=
  ∀ {i A l}, Lookup Γ i A l → Δ ⊢[l] σ i : A.subst σ

namespace WfSb

theorem id {Γ} : WfCtx Γ → WfSb Γ Expr.bvar Γ := by
  intro _ _ _ _ _
  rw [Expr.subst_bvar, id_eq]
  apply WfTm.bvar <;> assumption

theorem snoc {Δ Γ A t σ l} : WfSb Δ σ Γ → Γ ⊢[l] A → Δ ⊢[l] t : A.subst σ →
    WfSb Δ (Expr.snoc σ t) ((A,l) :: Γ) := by
  intro _ _ _ _ _ _ lk
  cases lk <;> (autosubst; grind [WfSb])

-- Note: the premise `Δ ⊢[l] A.subst σ` is needed to prove this before `subst_all`,
-- but is eliminated after. See `up`.
theorem up' {Δ Γ A σ l} : WfCtx Δ → WfSb Δ σ Γ → Γ ⊢[l] A → Δ ⊢[l] A.subst σ →
    WfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) := by
  intro Δwf ΔσΓ _ ΔAσ _ _ _ lk
  have ΔAσwf := WfCtx.snoc Δwf ΔAσ
  cases lk
  . apply WfTm.bvar ΔAσwf
    convert Lookup.zero .. using 1
    autosubst
  . rename_i lk
    convert WfRen.rename_all.2.2.2.1 (ΔσΓ lk) ΔAσwf (@WfRen.wk Δ (A.subst σ) l) using 1
    autosubst

attribute [local grind] WfCtx.snoc in
attribute [local grind] WfSb.up' in
theorem subst_all :
    (∀ {Γ}, WfCtx Γ → True) ∧
    (∀ {Γ l A}, Γ ⊢[l] A →
      ∀ {Δ σ}, WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] A.subst σ) ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      ∀ {Δ σ}, WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] A.subst σ ≡ B.subst σ) ∧
    (∀ {Γ l t A}, Γ ⊢[l] t : A →
      ∀ {Δ σ}, WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] t.subst σ : A.subst σ) ∧
    (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A →
      ∀ {Δ σ}, WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] t.subst σ ≡ u.subst σ : A.subst σ) := by
  -- This goes through using the same proof as renaming!
  have ih_subst (B a : Expr) (σ) :
      (B.subst a.toSb).subst σ = (B.subst (Expr.up σ)).subst (a.subst σ).toSb := by autosubst
  mutual_induction
  case snoc => exact True.intro
  all_goals try dsimp [Expr.subst] at *
  case bvar => grind [WfSb]
  grind_cases
  case snd => rw [ih_subst]; apply WfTm.snd <;> grind
  case cong_snd => rw [ih_subst]; apply EqTm.cong_snd <;> grind
  case lam_app ihf _ _ Δwf ξwf => simpa only [autosubst] using EqTm.lam_app (ihf Δwf ξwf)

theorem up {Δ Γ A σ l} : WfCtx Δ → WfSb Δ σ Γ → Γ ⊢[l] A →
    WfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) :=
  fun h₁ h₂ h₃ => up' h₁ h₂ h₃ (subst_all.2.1 h₃ h₁ h₂)

end WfSb

theorem WfTp.subst {Δ Γ A σ l} : Γ ⊢[l] A → WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] A.subst σ :=
  fun h h₁ h₂ => WfSb.subst_all.2.1 h h₁ h₂

theorem EqTp.subst {Δ Γ A B σ l} :
    Γ ⊢[l] A ≡ B → WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] A.subst σ ≡ B.subst σ :=
  fun h h₁ h₂ => WfSb.subst_all.2.2.1 h h₁ h₂

theorem WfTm.subst {Δ Γ A t σ l} :
    Γ ⊢[l] t : A → WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] t.subst σ : A.subst σ :=
  fun h h₁ h₂ => WfSb.subst_all.2.2.2.1 h h₁ h₂

theorem EqTm.subst {Δ Γ A t u σ l} :
    Γ ⊢[l] t ≡ u : A → WfCtx Δ → WfSb Δ σ Γ → Δ ⊢[l] t.subst σ ≡ u.subst σ : A.subst σ :=
  fun h h₁ h₂ => WfSb.subst_all.2.2.2.2 h h₁ h₂

-- TODO: derive context conversion?
