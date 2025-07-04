import Mathlib.Tactic.Convert
import GroupoidModel.Russell_PER_MS.Typing
import GroupoidModel.Tactic.MutualInduction

/-! # Admissibility of substitution -/

/-- Try solving each inductive case by its respective constructor passed to `grind`. -/
-- TODO: can the script be shortened? metaprogram a generator for the cases?
macro "grind_cases" : tactic =>
  `(tactic| (
    try case pi' => grind [WfTp.pi']
    try case sigma' => grind [WfTp.sigma']
    try case univ => grind [WfTp.univ]
    try case el => grind [WfTp.el]
    try case cong_pi' => grind [EqTp.cong_pi']
    try case cong_sigma' => grind [EqTp.cong_sigma']
    try case cong_el => grind [EqTp.cong_el]
    try case refl_tp => grind [EqTp.refl_tp]
    try case symm_tp => grind [EqTp.symm_tp]
    try case trans_tp => grind [EqTp.trans_tp]
    try case lam' => grind [WfTm.lam']
    try case app' => grind [WfTm.app']
    try case pair' => grind [WfTm.pair']
    try case fst' => grind [WfTm.fst']
    try case snd' => grind [WfTm.snd']
    try case code => grind [WfTm.code]
    try case conv => grind [WfTm.conv]
    try case cong_lam' => grind [EqTm.cong_lam']
    try case cong_app' => grind [EqTm.cong_app']
    try case cong_pair' => grind [EqTm.cong_pair']
    try case cong_fst' => grind [EqTm.cong_fst']
    try case cong_snd' => grind [EqTm.cong_snd']
    try case cong_code => grind [EqTm.cong_code]
    try case app_lam' => grind [EqTm.app_lam']
    try case fst_pair' => grind [EqTm.fst_pair']
    try case snd_pair' => grind [EqTm.snd_pair']
    try case lam_app' => grind [EqTm.lam_app']
    try case pair_fst_snd' => grind [EqTm.pair_fst_snd']
    try case conv_eq => grind [EqTm.conv_eq]
    try case refl_tm => grind [EqTm.refl_tm]
    try case symm_tm' => grind [EqTm.symm_tm']
    try case trans_tm' => grind [EqTm.trans_tm']
  ))

/-! ## Universe level bounds -/

attribute [local grind cases] Lookup in
theorem le_univMax_all :
    (∀ {Γ}, WfCtx Γ → ∀ {A i l}, Lookup Γ i A l → l ≤ univMax) ∧
    (∀ {Γ l A}, Γ ⊢[l] A → l ≤ univMax) ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B → l ≤ univMax) ∧
    (∀ {Γ l A t}, Γ ⊢[l] t : A → l ≤ univMax) ∧
    (∀ {Γ l A t u}, Γ ⊢[l] t ≡ u : A → l ≤ univMax) := by
  mutual_induction WfCtx
  -- I ❤ grind and omega
  all_goals first | omega | grind

theorem WfCtx.le_univMax_of_lookup {Γ i A l} : WfCtx Γ → Lookup Γ i A l → l ≤ univMax :=
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

/-- The renaming `ξ : Δ ⟶ Γ` is well-formed.

This notion is only useful as an intermediate step
in establishing admissibility of substitution.
After that, use `WfSb` and `EqSb`. -/
@[irreducible]
def WfRen (Δ : Ctx) (ξ : Nat → Nat) (Γ : Ctx) :=
  ∀ {i A l}, Lookup Γ i A l → Lookup Δ (ξ i) (A.rename ξ) l

namespace WfRen

theorem lookup {Δ Γ A ξ i l} : WfRen Δ ξ Γ → Lookup Γ i A l → Lookup Δ (ξ i) (A.rename ξ) l := by
  unfold WfRen; intro h; exact h

theorem id (Γ) : WfRen Γ id Γ := by
  unfold WfRen; intro _ _ _ lk; convert lk; autosubst

theorem wk (Γ A l) : WfRen ((A,l) :: Γ) Nat.succ Γ := by
  unfold WfRen; intro _ _ _ lk
  convert Lookup.succ _ _ lk
  autosubst

theorem comp {Θ Δ Γ ξ₁ ξ₂} : WfRen Θ ξ₁ Δ → WfRen Δ ξ₂ Γ → WfRen Θ (fun i => ξ₁ (ξ₂ i)) Γ := by
  unfold WfRen; intro wf₁ wf₂ _ _ _ lk
  convert wf₁ <| wf₂ lk using 1
  autosubst
  congr 1

theorem upr {Δ Γ A ξ l} : WfRen Δ ξ Γ →
    WfRen ((A.rename ξ, l) :: Δ) (Expr.upr ξ) ((A, l) :: Γ) := by
  unfold WfRen; intro wf _ _ _ lk
  cases lk
  . rw [show (A.subst Expr.wk).rename (Expr.upr ξ) = (A.rename ξ).subst Expr.wk by autosubst]
    apply Lookup.zero
  . rename_i A _ lk
    rw [show (A.subst Expr.wk).rename (Expr.upr ξ) = (A.rename ξ).subst Expr.wk by autosubst]
    apply Lookup.succ _ _ (wf lk)

end WfRen

attribute [local grind] WfCtx.snoc WfRen.upr in
theorem rename_all :
    (∀ {Γ l A}, Γ ⊢[l] A →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] A.rename ξ) ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] A.rename ξ ≡ B.rename ξ) ∧
    (∀ {Γ l A t}, Γ ⊢[l] t : A →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] t.rename ξ : A.rename ξ) ∧
    (∀ {Γ l A t u}, Γ ⊢[l] t ≡ u : A →
      ∀ {Δ ξ}, WfCtx Δ → WfRen Δ ξ Γ → Δ ⊢[l] t.rename ξ ≡ u.rename ξ : A.rename ξ) := by
  -- `grind` will pick this up to simplify goals.
  have ih_subst (B a : Expr) (ξ) :
      (B.subst a.toSb).rename ξ = (B.rename (Expr.upr ξ)).subst (a.rename ξ).toSb := by autosubst
  mutual_induction WfCtx
  all_goals dsimp only; try intros
  case snoc => exact True.intro
  all_goals try dsimp [Expr.rename] at *
  case bvar ξ => apply WfTm.bvar _ (ξ.lookup _) <;> assumption
  grind_cases
  -- Cases that didn't go through automatically.
  case snd' => rw [ih_subst]; apply WfTm.snd' <;> grind
  case cong_snd' => rw [ih_subst]; apply EqTm.cong_snd' <;> grind
  case lam_app' =>
    convert EqTm.lam_app' .. using 1
    . congr 2 <;> autosubst
    all_goals grind

/-! ## Lookup well-formedness -/

theorem Lookup.lt_length {Γ i A l} : Lookup Γ i A l → i < Γ.length := by
  intro lk; induction lk <;> (dsimp; omega)

theorem Lookup.lvl_eq {Γ i A l} (lk : Lookup Γ i A l) : l = (Γ[i]'lk.lt_length).2 := by
  induction lk <;> grind

theorem Lookup.of_lt_length {Γ i} : i < Γ.length → ∃ A l, Lookup Γ i A l := by
  intro lt
  induction Γ generalizing i
  . cases lt
  . cases i
    . exact ⟨_, _, Lookup.zero ..⟩
    . rename_i ih _
      have ⟨A, l, h⟩ := ih <| Nat.succ_lt_succ_iff.mp lt
      exact ⟨A.subst Expr.wk, l, Lookup.succ _ _ h⟩

theorem WfCtx.lookup_wf {Γ i A l} : WfCtx Γ → Lookup Γ i A l → Γ ⊢[l] A := by
  intro Γwf lk
  induction lk
  . rcases Γwf with _ | ⟨Γ, A⟩
    rw [← Expr.ofRen_succ, ← Expr.rename_eq_subst_ofRen]
    exact rename_all.1 A (Γ.snoc A) (WfRen.wk _ _ _)
  . rename_i ih
    rcases Γwf with _ | ⟨Γ, B⟩
    rw [← Expr.ofRen_succ, ← Expr.rename_eq_subst_ofRen]
    exact rename_all.1 (ih Γ) (Γ.snoc B) (WfRen.wk _ _ _)

/-! ## Admissibility of substitution -/

/-- The substitutions `σ σ' : Δ ⟶ Γ` are judgmentally equal.

This is a functional definition similar to that in the Autosubst paper,
but with a lot of preservation data added
so that we can use this before proving admissibility of substitution and inversion.

The additional data is an implementation detail;
`EqSb` should not be unfolded outside of this module.

A common alternative is to use an inductive characterization. -/
@[irreducible]
def EqSb (Δ : Ctx) (σ σ' : Nat → Expr) (Γ : Ctx) :=
  WfCtx Δ ∧ WfCtx Γ ∧
    ∀ {i A l}, Lookup Γ i A l →
      (Δ ⊢[l] A.subst σ) ∧ (Δ ⊢[l] A.subst σ') ∧ (Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧
      (Δ ⊢[l] σ i : A.subst σ) ∧ (Δ ⊢[l] σ' i : A.subst σ') ∧ (Δ ⊢[l] σ i ≡ σ' i : A.subst σ)

/-- The substitution `σ : Δ ⟶ Γ` is well-formed. -/
@[irreducible]
def WfSb (Δ : Ctx) (σ : Nat → Expr) (Γ : Ctx) := EqSb Δ σ σ Γ

namespace EqSb

theorem refl {Δ Γ σ} : WfSb Δ σ Γ → EqSb Δ σ σ Γ := by
  unfold WfSb EqSb; grind

theorem symm {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → EqSb Δ σ' σ Γ := by
  unfold EqSb; grind [EqTp.symm_tp, EqTm.symm_tm', EqTm.conv_eq]

theorem trans {Δ Γ σ σ' σ''} : EqSb Δ σ σ' Γ → EqSb Δ σ' σ'' Γ → EqSb Δ σ σ'' Γ := by
  unfold EqSb
  intro h h'
  refine ⟨h.1, h.2.1, fun lk => ?_⟩
  replace h := h.2.2 lk
  replace h' := h'.2.2 lk
  grind [EqTp.symm_tp, EqTp.trans_tp, EqTm.trans_tm', EqTm.conv_eq]

theorem lookup {Δ Γ A σ σ' i l} : EqSb Δ σ σ' Γ → Lookup Γ i A l →
    Δ ⊢[l] σ i ≡ σ' i : A.subst σ := by
  unfold EqSb; grind

theorem wf_dom {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → WfCtx Δ := by
  unfold EqSb; intro h; exact h.1

theorem wf_cod {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → WfCtx Γ := by
  unfold EqSb; intro h; exact h.2.1

theorem wf_left {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → WfSb Δ σ Γ := by
  unfold WfSb; intro h; exact h.trans h.symm

theorem wf_right {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → WfSb Δ σ' Γ := by
  unfold WfSb; intro h; exact h.symm.trans h

end EqSb

namespace WfSb

theorem eq_self {Δ Γ σ} : WfSb Δ σ Γ → EqSb Δ σ σ Γ :=
  fun h => .refl h

theorem ofRen {Δ Γ ξ} : WfCtx Δ → WfCtx Γ → WfRen Δ ξ Γ → WfSb Δ (Expr.ofRen ξ) Γ := by
  unfold WfSb EqSb
  intro Δ Γ ξ
  refine ⟨Δ, Γ, fun lk => ?_⟩
  simp only [← Expr.rename_eq_subst_ofRen]
  refine ⟨?A, ?A, EqTp.refl_tp ?A, ?i, ?i, EqTm.refl_tm ?i⟩
  . exact Δ.lookup_wf (ξ.lookup lk)
  . exact WfTm.bvar Δ (ξ.lookup lk)

theorem id {Γ} : WfCtx Γ → WfSb Γ Expr.bvar Γ :=
  fun h => ofRen h h (WfRen.id _)

theorem lookup {Δ Γ A σ i l} : WfSb Δ σ Γ → Lookup Γ i A l → Δ ⊢[l] σ i : A.subst σ := by
  unfold WfSb EqSb; grind

theorem wf_dom {Δ Γ σ} : WfSb Δ σ Γ → WfCtx Δ := by
  unfold WfSb; intro h; exact h.wf_dom

theorem wf_cod {Δ Γ σ} : WfSb Δ σ Γ → WfCtx Γ := by
  unfold WfSb; intro h; exact h.wf_cod

end WfSb

/- Like the primed typing rules,
notions defined in this namespace are suboptimal:
they include tons of redundant assumptions
needed to make the main induction go through.

After substitution and inversion,
we can define better versions with fewer arguments. -/
namespace SubstProof

theorem eqSb_snoc {Δ Γ A t t' σ σ' l} : EqSb Δ σ σ' Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    Δ ⊢[l] t : A.subst σ → Δ ⊢[l] t' : A.subst σ' → Δ ⊢[l] t ≡ t' : A.subst σ →
    EqSb Δ (Expr.snoc σ t) (Expr.snoc σ' t') ((A,l) :: Γ) := by
  unfold EqSb
  intro σσ' A; intros
  refine ⟨σσ'.1, σσ'.2.1.snoc A, fun lk => ?_⟩
  cases lk <;> (autosubst; grind)

theorem wfSb_snoc {Δ Γ A t σ l} : WfSb Δ σ Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] t : A.subst σ →
    WfSb Δ (Expr.snoc σ t) ((A,l) :: Γ) :=
  fun h A Aσ t => eqSb_snoc (EqSb.refl h) A Aσ Aσ (EqTp.refl_tp Aσ) t t (EqTm.refl_tm t) |>.wf_left

theorem eqSb_up {Δ Γ A σ σ' l} : EqSb Δ σ σ' Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    EqSb ((A.subst σ, l) :: Δ) (Expr.up σ) (Expr.up σ') ((A,l) :: Γ) := by
  unfold EqSb
  intro σσ' A Aσ Aσ' Aσeq
  have ΔAσ := σσ'.1.snoc Aσ
  refine ⟨ΔAσ, σσ'.2.1.snoc A, fun lk => ?_⟩
  cases lk
  . rw [Expr.up_eq_snoc σ, Expr.up_eq_snoc σ']; dsimp
    repeat any_goals apply And.intro
    . convert rename_all.1 Aσ ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.1 Aσ' ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.2.1 Aσeq ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert WfTm.bvar ΔAσ (Lookup.zero ..) using 1 <;> autosubst
    . convert WfTm.conv (WfTm.bvar ΔAσ (Lookup.zero ..)) ?_
      convert rename_all.2.1 Aσeq ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert EqTm.refl_tm (WfTm.bvar ΔAσ (Lookup.zero ..)) using 1 <;> autosubst
  next lk =>
    have := σσ'.2.2 lk
    repeat any_goals apply And.intro
    . convert rename_all.1 this.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.1 this.2.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.2.1 this.2.2.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.2.2.1 this.2.2.2.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst; rfl
    . convert rename_all.2.2.1 this.2.2.2.2.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst; rfl
    . rw [Expr.up_eq_snoc σ, Expr.up_eq_snoc σ']
      convert rename_all.2.2.2 this.2.2.2.2.2 ΔAσ (WfRen.wk ..) using 1 <;>
        (autosubst; try rw [Expr.comp])

theorem wfSb_up {Δ Γ A σ l} : WfSb Δ σ Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ →
    WfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) :=
  fun h A Aσ => eqSb_up (EqSb.refl h) A Aσ Aσ (EqTp.refl_tp Aσ) |>.wf_left

attribute [local grind] WfCtx.snoc
  EqTp.refl_tp EqTp.symm_tp EqTp.trans_tp
  EqSb.refl EqSb.wf_left EqSb.wf_right eqSb_up
  wfSb_up in
theorem subst_all :
    (∀ {Γ l A}, Γ ⊢[l] A →
      (∀ {Δ σ}, WfSb Δ σ Γ → Δ ⊢[l] A.subst σ) ∧
        ∀ {Δ σ σ'}, EqSb Δ σ σ' Γ → Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      ∀ {Δ σ σ'}, EqSb Δ σ σ' Γ → Δ ⊢[l] A.subst σ ≡ B.subst σ') ∧
    (∀ {Γ l A t}, Γ ⊢[l] t : A →
      (∀ {Δ σ}, WfSb Δ σ Γ → Δ ⊢[l] t.subst σ : A.subst σ) ∧
        ∀ {Δ σ σ'}, EqSb Δ σ σ' Γ → Δ ⊢[l] t.subst σ ≡ t.subst σ' : A.subst σ) ∧
    (∀ {Γ l A t u}, Γ ⊢[l] t ≡ u : A →
      ∀ {Δ σ σ'}, EqSb Δ σ σ' Γ → Δ ⊢[l] t.subst σ ≡ u.subst σ' : A.subst σ) := by
  have ih_subst (B a : Expr) (σ) :
      (B.subst a.toSb).subst σ = (B.subst (Expr.up σ)).subst (a.subst σ).toSb := by autosubst
  mutual_induction WfCtx
  all_goals dsimp; try intros
  case snoc => exact True.intro
  all_goals try dsimp [Expr.subst] at *
  case bvar => grind [EqSb.lookup, WfSb.lookup]
  grind_cases
  case pi' => grind [WfTp.pi', EqTp.cong_pi']
  case sigma' => grind [WfTp.sigma', EqTp.cong_sigma']
  case univ => grind [WfSb.wf_dom, EqSb.wf_dom, WfTp.univ]
  case el => grind [WfTp.el, EqTp.cong_el]
  case symm_tp => grind [EqSb.symm]
  case lam' => grind [WfTm.lam', EqTm.cong_lam']
  case app' ihA _ _ _ =>
    constructor
    . grind [WfTm.app']
    . intro _ _ _ σ
      rw [ih_subst]
      apply EqTm.cong_app' (ihA.1 σ.wf_left) <;> grind
  case pair' => constructor <;> grind [WfTm.pair', EqTm.cong_pair']
  case fst' => constructor <;> grind [WfTm.fst', EqTm.cong_fst']
  case snd' =>
    constructor
    . intros; rw [ih_subst]; apply WfTm.snd' <;> grind
    . intros; rw [ih_subst]; apply EqTm.cong_snd' <;> grind
  case code => grind [WfTm.code, EqTm.cong_code]
  case conv => constructor <;> grind [WfTm.conv, EqTm.conv_eq]
  case app_lam' =>
    rw [ih_subst, ih_subst]
    apply (EqTm.app_lam' ..).trans_tm'
    . autosubst; grind [eqSb_snoc, wfSb_snoc]
    . autosubst
      rename_i iht _ _ _ _ _
      apply iht.2 <;> grind [eqSb_snoc]
    all_goals grind
  case fst_pair' => apply (EqTm.fst_pair' ..).trans_tm' <;> grind
  case snd_pair' =>
    rw [ih_subst]; apply (EqTm.snd_pair' ..).trans_tm'
    . autosubst; grind [eqSb_snoc, wfSb_snoc]
    all_goals grind
  case lam_app' ihA ihB ihf _ _ _ σσ' =>
    apply (ihf.2 σσ').trans_tm' (by grind [WfTp.pi'])
    have := EqTm.lam_app'
      (ihA.1 <| σσ'.wf_right)
      (ihB.1 <| by grind)
      (ihf.1 <| σσ'.wf_right)
    convert this.conv_eq _ using 3 <;> autosubst
    grind [EqTp.cong_pi', EqSb.symm, Expr.up_eq_snoc]
  case pair_fst_snd' =>
    apply (EqTm.pair_fst_snd' ..).trans_tm' <;>
      grind [WfTp.sigma', EqTm.cong_pair', EqTm.cong_fst', EqTm.cong_snd']
  case symm_tm' => grind [EqTm.symm_tm', EqTm.conv_eq, EqSb.symm]
  case trans_tm' => grind [EqTm.trans_tm', EqTm.conv_eq, EqSb.symm]
  case cong_app' ihA _ _ _ _ _ _ σ =>
    rw [ih_subst]
    apply EqTm.cong_app' (ihA.1 σ.wf_left) <;> grind
  case cong_snd' => rw [ih_subst]; apply EqTm.cong_snd' <;> grind

end SubstProof

/-! ## Substitution helper lemmas -/

open SubstProof

theorem WfTp.subst_eq {Δ Γ A l σ σ'} (h : Γ ⊢[l] A) (hσσ' : EqSb Δ σ σ' Γ) :
    Δ ⊢[l] A.subst σ ≡ A.subst σ' :=
  subst_all.1 h |>.2 hσσ'

theorem EqTp.subst_eq {Δ Γ A B l σ σ'} (h : Γ ⊢[l] A ≡ B) (hσσ' : EqSb Δ σ σ' Γ) :
    Δ ⊢[l] A.subst σ ≡ B.subst σ' :=
  subst_all.2.1 h hσσ'

theorem WfTm.subst_eq {Δ Γ A t σ σ' l} (h : Γ ⊢[l] t : A) (hσσ' : EqSb Δ σ σ' Γ) :
    Δ ⊢[l] t.subst σ ≡ t.subst σ' : A.subst σ :=
  subst_all.2.2.1 h |>.2 hσσ'

theorem EqTm.subst_eq {Δ Γ A t u σ σ' l} (h : Γ ⊢[l] t ≡ u : A) (hσσ' : EqSb Δ σ σ' Γ) :
    Δ ⊢[l] t.subst σ ≡ u.subst σ' : A.subst σ :=
  subst_all.2.2.2 h hσσ'

theorem WfTp.subst {Δ Γ A σ l} (h : Γ ⊢[l] A) (hσ : WfSb Δ σ Γ) : Δ ⊢[l] A.subst σ :=
  subst_all.1 h |>.1 hσ

theorem EqTp.subst {Δ Γ A B σ l} (h : Γ ⊢[l] A ≡ B) (hσ : WfSb Δ σ Γ) :
    Δ ⊢[l] A.subst σ ≡ B.subst σ :=
  h.subst_eq (EqSb.refl hσ)

theorem WfTm.subst {Δ Γ A t σ l} (h : Γ ⊢[l] t : A) (hσ : WfSb Δ σ Γ) :
    Δ ⊢[l] t.subst σ : A.subst σ :=
  subst_all.2.2.1 h |>.1 hσ

theorem EqTm.subst {Δ Γ A t u σ l} (h : Γ ⊢[l] t ≡ u : A) (hσ : WfSb Δ σ Γ) :
    Δ ⊢[l] t.subst σ ≡ u.subst σ : A.subst σ :=
  h.subst_eq (EqSb.refl hσ)
