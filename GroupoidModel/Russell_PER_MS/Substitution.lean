import Mathlib.Tactic.Convert
import GroupoidModel.Russell_PER_MS.Typing

/-! # Admissibility of substitution -/

-- TODO: generalize, or make a namespace and scope this
/-- Proof by mutual induction on typing judgments. -/
macro "mutual_induction" : tactic =>
  `(tactic| (
    refine ⟨
      -- beautiful
      @WfCtx.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi' ?sigma' ?univ ?el
        ?cong_pi' ?cong_sigma' ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam' ?app' ?pair' ?fst' ?snd' ?code ?conv
        ?cong_lam' ?cong_app' ?cong_pair' ?cong_fst' ?cong_snd' ?cong_code
        ?app_lam' ?fst_pair' ?snd_pair' ?lam_app' ?pair_fst_snd' ?conv_tm ?refl_tm ?symm_tm' ?trans_tm',
      @WfTp.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi' ?sigma' ?univ ?el
        ?cong_pi' ?cong_sigma' ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam' ?app' ?pair' ?fst' ?snd' ?code ?conv
        ?cong_lam' ?cong_app' ?cong_pair' ?cong_fst' ?cong_snd' ?cong_code
        ?app_lam' ?fst_pair' ?snd_pair' ?lam_app' ?pair_fst_snd' ?conv_tm ?refl_tm ?symm_tm' ?trans_tm',
      @EqTp.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi' ?sigma' ?univ ?el
        ?cong_pi' ?cong_sigma' ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam' ?app' ?pair' ?fst' ?snd' ?code ?conv
        ?cong_lam' ?cong_app' ?cong_pair' ?cong_fst' ?cong_snd' ?cong_code
        ?app_lam' ?fst_pair' ?snd_pair' ?lam_app' ?pair_fst_snd' ?conv_tm ?refl_tm ?symm_tm' ?trans_tm',
      @WfTm.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi' ?sigma' ?univ ?el
        ?cong_pi' ?cong_sigma' ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam' ?app' ?pair' ?fst' ?snd' ?code ?conv
        ?cong_lam' ?cong_app' ?cong_pair' ?cong_fst' ?cong_snd' ?cong_code
        ?app_lam' ?fst_pair' ?snd_pair' ?lam_app' ?pair_fst_snd' ?conv_tm ?refl_tm ?symm_tm' ?trans_tm',
      @EqTm.rec (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _)
        ?nil ?snoc
        ?pi' ?sigma' ?univ ?el
        ?cong_pi' ?cong_sigma' ?cong_el ?refl_tp ?symm_tp ?trans_tp
        ?bvar ?lam' ?app' ?pair' ?fst' ?snd' ?code ?conv
        ?cong_lam' ?cong_app' ?cong_pair' ?cong_fst' ?cong_snd' ?cong_code
        ?app_lam' ?fst_pair' ?snd_pair' ?lam_app' ?pair_fst_snd' ?conv_tm ?refl_tm ?symm_tm' ?trans_tm'
    ⟩
    all_goals dsimp only; try intros
  ))

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
    try case conv_tm => grind [EqTm.conv_tm]
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
    (∀ {Γ l t A}, Γ ⊢[l] t : A → l ≤ univMax) ∧
    (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A → l ≤ univMax) := by
  mutual_induction
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
After that, always use `WfSb`. -/
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

theorem WfCtx.lookup_wf {Γ i A l} : WfCtx Γ → Lookup Γ i A l → Γ ⊢[l] A := by
  intro Γwf lk
  induction lk
  . rcases Γwf with _ | ⟨Γ, A⟩
    rw [← Expr.ofRen_succ, ← Expr.rename_eq_subst_ofRen]
    exact rename_all.2.1 A (Γ.snoc A) (WfRen.wk _ _ _)
  . rename_i ih
    rcases Γwf with _ | ⟨Γ, B⟩
    rw [← Expr.ofRen_succ, ← Expr.rename_eq_subst_ofRen]
    exact rename_all.2.1 (ih Γ) (Γ.snoc B) (WfRen.wk _ _ _)

/-! ## Admissibility of substitution -/

/-- The substitution `σ : Δ ⟶ Γ` is well-formed.

This is a functional definition as in the Autosubst paper,
but with more preservation data added so that we can use this
before proving admissibility of substitution and inversion.
The additional data is an implementation detail;
`WfSb` should not be unfolded outside of this module.

A common alternative is to use an inductive characterization. -/
@[irreducible]
def WfSb (Δ : Ctx) (σ : Nat → Expr) (Γ : Ctx) :=
  WfCtx Δ ∧ WfCtx Γ ∧ ∀ {i A l}, Lookup Γ i A l → (Δ ⊢[l] A.subst σ) ∧ (Δ ⊢[l] σ i : A.subst σ)

namespace WfSb

theorem wf_dom {Δ Γ σ} : WfSb Δ σ Γ → WfCtx Δ := by
  unfold WfSb; intro h; exact h.1

theorem wf_cod {Δ Γ σ} : WfSb Δ σ Γ → WfCtx Γ := by
  unfold WfSb; intro h; exact h.2.1

theorem lookup {Δ Γ A σ i l} : WfSb Δ σ Γ → Lookup Γ i A l → Δ ⊢[l] σ i : A.subst σ :=
  fun h lk => by unfold WfSb at h; exact h.2.2 lk |>.2

theorem ofRen {Δ Γ ξ} : WfCtx Δ → WfCtx Γ → WfRen Δ ξ Γ → WfSb Δ (Expr.ofRen ξ) Γ := by
  unfold WfSb
  intro Δ Γ ξ
  refine ⟨Δ, Γ, fun lk => ?_⟩
  constructor
  . rw [← Expr.rename_eq_subst_ofRen]
    exact Δ.lookup_wf (ξ.lookup lk)
  . convert WfTm.bvar Δ (ξ.lookup lk) using 1
    autosubst

theorem id {Γ} : WfCtx Γ → WfSb Γ Expr.bvar Γ :=
  fun h => ofRen h h (WfRen.id Γ)

end WfSb

/-- The substitutions `σ σ' : Δ ⟶ Γ` are definitionally equal. -/
@[irreducible]
def EqSb (Δ : Ctx) (σ σ' : Nat → Expr) (Γ : Ctx) :=
  WfCtx Δ ∧ WfCtx Γ ∧
    ∀ {i A l}, Lookup Γ i A l →
      (Δ ⊢[l] A.subst σ) ∧ (Δ ⊢[l] A.subst σ') ∧ (Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧
      (Δ ⊢[l] σ i ≡ σ' i : A.subst σ)

namespace EqSb

theorem wf_dom {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → WfCtx Δ := by
  unfold EqSb; intro h; exact h.1

theorem wf_cod {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → WfCtx Γ := by
  unfold EqSb; intro h; exact h.2.1

theorem lookup {Δ Γ A σ σ' i l} : EqSb Δ σ σ' Γ → Lookup Γ i A l →
    Δ ⊢[l] σ i ≡ σ' i : A.subst σ :=
  fun h lk => by unfold EqSb at h; exact h.2.2 lk |>.2.2.2

theorem refl {Δ Γ σ} : WfSb Δ σ Γ → EqSb Δ σ σ Γ := by
  unfold WfSb EqSb
  intro σ
  refine ⟨σ.1, σ.2.1, fun lk => ?_⟩
  exact ⟨(σ.2.2 lk).1, (σ.2.2 lk).1, EqTp.refl_tp (σ.2.2 lk).1, EqTm.refl_tm (σ.2.2 lk).2⟩

theorem symm {Δ Γ σ σ'} : EqSb Δ σ σ' Γ → EqSb Δ σ' σ Γ := by
  unfold EqSb; grind [EqTp.symm_tp, EqTm.symm_tm', EqTm.conv_tm]

theorem trans {Δ Γ σ σ' σ''} : EqSb Δ σ σ' Γ → EqSb Δ σ' σ'' Γ → EqSb Δ σ σ'' Γ := by
  unfold EqSb
  intro h h'
  refine ⟨h.1, h.2.1, fun lk => ?_⟩
  exact ⟨
    (h.2.2 lk).1,
    (h'.2.2 lk).2.1,
    (h.2.2 lk).2.2.1.trans_tp (h'.2.2 lk).2.2.1,
    (h.2.2 lk).2.2.2.trans_tm'
      (h.2.2 lk).1
      ((h'.2.2 lk).2.2.2.conv_tm (h.2.2 lk).2.2.1.symm_tp)
  ⟩

end EqSb

/- Like the primed typing rules,
notions defined in this namespace are suboptimal:
they include tons of redundant assumptions
needed to make the main induction go through.

After substitution and inversion,
we define better versions with fewer arguments. -/
namespace SubstProof

theorem wfSb_wk {Γ A l} : WfCtx Γ → Γ ⊢[l] A → WfSb ((A,l) :: Γ) Expr.wk Γ :=
  fun h h' => WfSb.ofRen (h.snoc h') h (WfRen.wk ..)

theorem wfSb_snoc {Δ Γ A t σ l} : WfSb Δ σ Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] t : A.subst σ →
    WfSb Δ (Expr.snoc σ t) ((A,l) :: Γ) := by
  unfold WfSb; intro σ A Aσ t
  refine ⟨σ.1, σ.2.1.snoc A, fun lk => ?_⟩
  cases lk
  . constructor
    . convert Aσ using 1; autosubst
    . autosubst; grind
  next lk =>
    constructor
    . convert (σ.2.2 lk).1 using 1; autosubst
    . autosubst; grind

theorem wfSb_up_of_eq {Δ Γ A Aσ σ l} : WfSb Δ σ Γ →
    Γ ⊢[l] A → Δ ⊢[l] Aσ → Δ ⊢[l] A.subst σ → Δ ⊢[l] Aσ ≡ A.subst σ →
    WfSb ((Aσ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) := by
  unfold WfSb; intro σ A Aσ Aσ' Aσeq
  have ΔAσ := σ.1.snoc Aσ
  refine ⟨ΔAσ, σ.2.1.snoc A, fun lk => ?_⟩
  cases lk
  . constructor
    . convert rename_all.2.1 Aσ' ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . apply WfTm.conv (A := Expr.subst Expr.wk _)
      . rw [Expr.up_eq_snoc]
        apply WfTm.bvar ΔAσ
        apply Lookup.zero
      . convert rename_all.2.2.1 Aσeq ΔAσ (WfRen.wk ..) using 1 <;> autosubst
  next lk =>
    constructor
    . convert rename_all.2.1 (σ.2.2 lk).1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . rw [Expr.up_eq_snoc]
      convert rename_all.2.2.2.1 (σ.2.2 lk).2 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
      rw [Expr.comp]

theorem wfSb_up {Δ Γ A σ l} : WfSb Δ σ Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ →
    WfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) :=
  fun ΔσΓ ΓA ΔAσ => wfSb_up_of_eq ΔσΓ ΓA ΔAσ ΔAσ (EqTp.refl_tp ΔAσ)

theorem eqSb_snoc {Δ Γ A t t' σ σ' l} : EqSb Δ σ σ' Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    Δ ⊢[l] t ≡ t' : A.subst σ →
    EqSb Δ (Expr.snoc σ t) (Expr.snoc σ' t') ((A,l) :: Γ) := by
  unfold EqSb
  intro σσ' A Aσ Aσ' AσAσ' tt'
  refine ⟨σσ'.1, σσ'.2.1.snoc A, fun lk => ?_⟩
  cases lk
  . repeat any_goals apply And.intro
    . convert Aσ using 1; autosubst
    . convert Aσ' using 1; autosubst
    . convert AσAσ' using 1 <;> autosubst
    . convert tt' using 1; autosubst
  next lk =>
    repeat any_goals apply And.intro
    . convert (σσ'.2.2 lk).1 using 1; autosubst
    . convert (σσ'.2.2 lk).2.1 using 1; autosubst
    . convert (σσ'.2.2 lk).2.2.1 using 1 <;> autosubst
    . convert (σσ'.2.2 lk).2.2.2 using 1 <;> autosubst

theorem eqSb_up {Δ Γ A σ σ' l} : EqSb Δ σ σ' Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    EqSb ((A.subst σ, l) :: Δ) (Expr.up σ) (Expr.up σ') ((A,l) :: Γ) := by
  unfold EqSb
  intro σσ' A Aσ Aσ' Aσeq
  have ΔAσ := σσ'.1.snoc Aσ
  refine ⟨ΔAσ, σσ'.2.1.snoc A, fun lk => ?_⟩
  cases lk
  . repeat any_goals apply And.intro
    . convert rename_all.2.1 Aσ ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.2.1 Aσ' ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.2.2.1 Aσeq ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . rw [Expr.up_eq_snoc σ, Expr.up_eq_snoc σ']
      apply EqTm.refl_tm
      apply WfTm.bvar ΔAσ
      convert Lookup.zero .. using 1
      autosubst
  next lk =>
    have := σσ'.2.2 lk
    repeat any_goals apply And.intro
    . convert rename_all.2.1 this.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.2.1 this.2.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . convert rename_all.2.2.1 this.2.2.1 ΔAσ (WfRen.wk ..) using 1 <;> autosubst
    . rw [Expr.up_eq_snoc σ, Expr.up_eq_snoc σ']
      convert rename_all.2.2.2.2 this.2.2.2 ΔAσ (WfRen.wk ..) using 1 <;>
        (autosubst; try rw [Expr.comp])

attribute [local grind] WfCtx.snoc wfSb_up_of_eq wfSb_up eqSb_up in
theorem subst_all :
    (∀ {Γ}, WfCtx Γ → True) ∧
    (∀ {Γ l A}, Γ ⊢[l] A →
      ∀ {Δ σ}, WfSb Δ σ Γ →
        (Δ ⊢[l] A.subst σ) ∧
          ∀ {σ'}, WfSb Δ σ' Γ → EqSb Δ σ σ' Γ →
            Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      ∀ {Δ σ σ'}, WfSb Δ σ Γ → WfSb Δ σ' Γ → EqSb Δ σ σ' Γ →
        Δ ⊢[l] A.subst σ ≡ B.subst σ') ∧
    (∀ {Γ l t A}, Γ ⊢[l] t : A →
      ∀ {Δ σ}, WfSb Δ σ Γ →
        (Δ ⊢[l] t.subst σ : A.subst σ) ∧
          ∀ {σ'}, WfSb Δ σ' Γ → EqSb Δ σ σ' Γ →
            Δ ⊢[l] t.subst σ ≡ t.subst σ' : A.subst σ) ∧
    (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A →
      ∀ {Δ σ σ'}, WfSb Δ σ Γ → WfSb Δ σ' Γ → EqSb Δ σ σ' Γ →
        Δ ⊢[l] t.subst σ ≡ u.subst σ' : A.subst σ) := by
  have ih_subst (B a : Expr) (σ) :
      (B.subst a.toSb).subst σ = (B.subst (Expr.up σ)).subst (a.subst σ).toSb := by autosubst
  mutual_induction
  case snoc => exact True.intro
  all_goals try dsimp [Expr.subst] at *
  case bvar => grind [WfSb.lookup, EqSb.lookup]
  grind_cases
  case pi' => grind [WfTp.pi', EqTp.cong_pi']
  case sigma' => grind [WfTp.sigma', EqTp.cong_sigma']
  case univ => grind [WfSb.wf_dom, WfTp.univ, EqTp.refl_tp]
  case el => grind [WfTp.el, EqTp.cong_el]
  case symm_tp => grind [EqSb.symm, EqTp.symm_tp]
  case trans_tp => grind [EqTp.trans_tp, EqSb.trans, EqSb.refl]
  case lam' => grind [WfTm.lam', EqTm.cong_lam']
  case app' => grind [WfTm.app', EqTm.cong_app']
  case pair' => grind [WfTm.pair', EqTm.cong_pair']
  case fst' => grind [WfTm.fst', EqTm.cong_fst']
  case snd' =>
    constructor
    . rw [ih_subst]; apply WfTm.snd' <;> grind
    . intros; rw [ih_subst]; apply EqTm.cong_snd' <;> grind
  case code => grind [WfTm.code, EqTm.cong_code]
  case conv => grind [WfTm.conv, EqTm.conv_tm, EqSb.refl]
  case app_lam' =>
    rw [ih_subst, ih_subst]
    apply (EqTm.app_lam' ..).trans_tm'
    . autosubst; grind [wfSb_snoc]
    . autosubst
      rename_i iht _ _ _ _ _ _ _ _

      sorry
      -- apply (iht _).2 <;> grind [wfSb_snoc, eqSb_snoc]
    all_goals grind
  case fst_pair' => apply (EqTm.fst_pair' ..).trans_tm' <;> grind
  case snd_pair' =>
    rw [ih_subst]; apply (EqTm.snd_pair' ..).trans_tm'
    . autosubst; grind [wfSb_snoc]
    all_goals grind
  case lam_app' ihA ihB ihf _ _ _ Δ σ σ' σσ' =>
    sorry
    -- apply (ihf Δ σ |>.2 σ' σσ').trans_tm' (by grind [WfTp.pi'])
    -- have := EqTm.lam_app'
    --   (ihA Δ σ').1
    --   (ihB (Δ.snoc (by grind))
    --   (wfSb_up Δ σ' (by grind))).1
    --   (ihf Δ σ').1
    -- convert this.conv_tm _ using 3 <;> autosubst
    -- grind [EqTp.cong_pi', EqSb.symm, Expr.up_eq_snoc]
  case pair_fst_snd' =>
    apply (EqTm.pair_fst_snd' ..).trans_tm' <;>
      grind [WfTp.sigma', EqTm.cong_pair', EqTm.cong_fst', EqTm.cong_snd']
  case conv_tm => grind [EqTm.conv_tm, EqSb.refl]
  case symm_tm' => grind [EqTm.symm_tm', EqTm.conv_tm, EqSb.symm]
  case trans_tm' => grind [EqTm.trans_tm', EqTm.conv_tm, EqSb.trans, EqSb.refl]
  case cong_snd' => rw [ih_subst]; apply EqTm.cong_snd' <;> grind

end SubstProof
