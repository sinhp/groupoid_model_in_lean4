import Mathlib.Tactic.Convert
import GroupoidModel.Russell_PER_MS.Typing

/-! # Syntactic metatheory

This version uses `Autosubst.lean`. -/

set_option grind.warning false

-- TODO: generalize, or make a namespace and scope this
/-- Proof by mutual induction on typing judgments. -/
macro "mutual_induction" : tactic =>
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
macro "grind_cases" : tactic =>
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

/-- The renaming `ξ : Δ ⟶ Γ` is well-formed. -/
def WfRen (Δ : Ctx) (ξ : Nat → Nat) (Γ : Ctx) :=
  ∀ {i A l}, Lookup Γ i A l → Lookup Δ (ξ i) (A.rename ξ) l

namespace WfRen

theorem id (Γ) : WfRen Γ id Γ :=
  fun lk => by convert lk; autosubst

theorem wk (Γ A l) : WfRen ((A,l) :: Γ) Nat.succ Γ := by
  intro _ _ _ lk
  convert Lookup.succ _ _ lk
  autosubst

theorem up {Δ Γ A ξ l} : WfRen Δ ξ Γ →
    WfRen ((A.rename ξ, l) :: Δ) (Expr.upr ξ) ((A, l) :: Γ) := by
  intro wf _ _ _ lk
  cases lk
  . rw [show (A.subst Expr.wk).rename (Expr.upr ξ) = (A.rename ξ).subst Expr.wk by autosubst]
    apply Lookup.zero
  . rename_i A _ lk
    rw [show (A.subst Expr.wk).rename (Expr.upr ξ) = (A.rename ξ).subst Expr.wk by autosubst]
    apply Lookup.succ _ _ (wf lk)

end WfRen

attribute [local grind] WfCtx.snoc WfRen.up in
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
  case lam_app =>
    convert EqTm.lam_app .. using 1
    . congr 2 <;> autosubst
    all_goals grind

/-! ## Lookup well-formedness -/

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

/- Warning: notions defined in this namespace are suboptimal:
they include tons of redundant assumptions
needed to make the main induction go through.

After substitution and inversion,
we can define better versions with fewer arguments. -/
namespace SubstProof

/-- The substitution `σ : Δ ⟶ Γ` is well-formed
and preserves bound variables' types.

This is a functional definition as in the Autosubst paper,
but with preservation data added for the inductive argument.

A common alternative is to use an inductive characterization. -/
def IndWfSb (Δ : Ctx) (σ : Nat → Expr) (Γ : Ctx) :=
  ∀ {i A l}, Lookup Γ i A l → (Δ ⊢[l] A.subst σ) ∧ (Δ ⊢[l] σ i : A.subst σ)

namespace IndWfSb

theorem ofRen {Δ Γ ξ} : WfCtx Δ → WfRen Δ ξ Γ → IndWfSb Δ (Expr.ofRen ξ) Γ := by
  intro h h' _ _ _ lk
  constructor
  . rw [← Expr.rename_eq_subst_ofRen]
    exact h.lookup_wf (h' lk)
  . convert WfTm.bvar h (h' lk) using 1
    autosubst

theorem id {Γ} : WfCtx Γ → IndWfSb Γ Expr.bvar Γ :=
  fun h => ofRen h (WfRen.id Γ)

theorem wk {Γ A l} : WfCtx Γ → Γ ⊢[l] A → IndWfSb ((A,l) :: Γ) Expr.wk Γ :=
  fun h h' => ofRen (h.snoc h') (WfRen.wk _ _ _)

theorem snoc {Δ Γ A t σ l} : IndWfSb Δ σ Γ → Δ ⊢[l] A.subst σ → Δ ⊢[l] t : A.subst σ →
    IndWfSb Δ (Expr.snoc σ t) ((A,l) :: Γ) := by
  intro σ Aσ t _ _ _ lk
  cases lk
  . constructor
    . convert Aσ using 1; autosubst
    . autosubst; grind [IndWfSb]
  next lk =>
    constructor
    . convert (σ lk).1 using 1; autosubst
    . autosubst; grind [IndWfSb]

theorem up_of_eq {Δ Γ A Aσ σ l} : WfCtx Δ → IndWfSb Δ σ Γ →
    Δ ⊢[l] Aσ → Δ ⊢[l] A.subst σ → Δ ⊢[l] Aσ ≡ A.subst σ →
    IndWfSb ((Aσ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) := by
  intro Δwf ΔσΓ ΔAσ ΔAσ' ΔAσeq _ _ _ lk
  have ΔAσwf := Δwf.snoc ΔAσ
  cases lk
  . constructor
    . convert rename_all.2.1 ΔAσ' ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . apply WfTm.conv (A := Aσ.subst Expr.wk)
      . apply WfTm.bvar ΔAσwf
        apply Lookup.zero
      . convert rename_all.2.2.1 ΔAσeq ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
  next lk =>
    constructor
    . convert rename_all.2.1 (ΔσΓ lk).1 ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . convert rename_all.2.2.2.1 (ΔσΓ lk).2 ΔAσwf (@WfRen.wk _ _ _) using 1
      autosubst

theorem up {Δ Γ A σ l} : WfCtx Δ → IndWfSb Δ σ Γ → Δ ⊢[l] A.subst σ →
    IndWfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) :=
  fun Δwf ΔσΓ ΔAσ => up_of_eq Δwf ΔσΓ ΔAσ ΔAσ (EqTp.refl_tp ΔAσ)

end IndWfSb

/-- The substitutions `σ σ' : Δ ⟶ Γ` are definitionally equal,
preserve variables' types, and are congruent on those types.
See also `IndWfSb`. -/
def IndEqSb (Δ : Ctx) (σ σ' : Nat → Expr) (Γ : Ctx) :=
  ∀ {i A l}, Lookup Γ i A l →
    (Δ ⊢[l] A.subst σ) ∧ (Δ ⊢[l] A.subst σ') ∧ (Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧
    (Δ ⊢[l] σ i ≡ σ' i : A.subst σ)

namespace IndEqSb

theorem refl {Δ Γ σ} : IndWfSb Δ σ Γ → IndEqSb Δ σ σ Γ :=
  fun h _ _ _ lk => ⟨(h lk).1, (h lk).1, EqTp.refl_tp (h lk).1, EqTm.refl_tm (h lk).2⟩

theorem symm {Δ Γ σ σ'} : IndEqSb Δ σ σ' Γ → IndEqSb Δ σ' σ Γ := by
  grind [IndEqSb, EqTp.symm_tp, EqTm.symm_tm, EqTm.conv_tm]

theorem trans {Δ Γ σ σ' σ''} : IndEqSb Δ σ σ' Γ → IndEqSb Δ σ' σ'' Γ → IndEqSb Δ σ σ'' Γ :=
  fun h h' _ _ _ lk => ⟨
    (h lk).1,
    (h' lk).2.1,
    (h lk).2.2.1.trans_tp (h' lk).2.2.1,
    (h lk).2.2.2.trans_tm (h lk).1 ((h' lk).2.2.2.conv_tm (h lk).2.2.1.symm_tp)
  ⟩

theorem snoc {Δ Γ A t t' σ σ' l} : IndEqSb Δ σ σ' Γ →
    Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    Δ ⊢[l] t ≡ t' : A.subst σ →
    IndEqSb Δ (Expr.snoc σ t) (Expr.snoc σ' t') ((A,l) :: Γ) := by
  intro σσ' Aσ Aσ' AσAσ' tt' _ _ _ lk
  cases lk
  . repeat any_goals apply And.intro
    . convert Aσ using 1; autosubst
    . convert Aσ' using 1; autosubst
    . convert AσAσ' using 1 <;> autosubst
    . convert tt' using 1; autosubst
  next lk =>
    repeat any_goals apply And.intro
    . convert (σσ' lk).1 using 1; autosubst
    . convert (σσ' lk).2.1 using 1; autosubst
    . convert (σσ' lk).2.2.1 using 1 <;> autosubst
    . convert (σσ' lk).2.2.2 using 1 <;> autosubst

theorem up {Δ Γ A σ σ' l} : WfCtx Δ → IndEqSb Δ σ σ' Γ →
    Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    IndEqSb ((A.subst σ, l) :: Δ) (Expr.up σ) (Expr.up σ') ((A,l) :: Γ) := by
  intro Δwf ΔσΓ ΔAσ ΔAσ' ΔAσeq _ _ _ lk
  have ΔAσwf := Δwf.snoc ΔAσ
  cases lk
  . repeat any_goals apply And.intro
    . convert rename_all.2.1 ΔAσ ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . convert rename_all.2.1 ΔAσ' ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . convert rename_all.2.2.1 ΔAσeq ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . apply EqTm.refl_tm
      apply WfTm.bvar ΔAσwf
      convert Lookup.zero .. using 1
      autosubst
  next lk =>
    have := ΔσΓ lk
    repeat any_goals apply And.intro
    . convert rename_all.2.1 this.1 ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . convert rename_all.2.1 this.2.1 ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . convert rename_all.2.2.1 this.2.2.1 ΔAσwf (@WfRen.wk _ _ _) using 1 <;> autosubst
    . convert rename_all.2.2.2.2 this.2.2.2 ΔAσwf (@WfRen.wk Δ (A.subst σ) l) using 1 <;>
        autosubst

end IndEqSb

attribute [local grind] WfCtx.snoc IndWfSb.up_of_eq IndWfSb.up IndEqSb.up in
theorem subst_all :
    (∀ {Γ}, WfCtx Γ → True) ∧
    (∀ {Γ l A}, Γ ⊢[l] A →
      ∀ {Δ σ}, WfCtx Δ → IndWfSb Δ σ Γ →
        (Δ ⊢[l] A.subst σ) ∧
          ∀ {σ'}, IndWfSb Δ σ' Γ → IndEqSb Δ σ σ' Γ →
            Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      ∀ {Δ σ σ'}, WfCtx Δ → IndWfSb Δ σ Γ → IndWfSb Δ σ' Γ → IndEqSb Δ σ σ' Γ →
        Δ ⊢[l] A.subst σ ≡ B.subst σ') ∧
    (∀ {Γ l t A}, Γ ⊢[l] t : A →
      ∀ {Δ σ}, WfCtx Δ → IndWfSb Δ σ Γ →
        (Δ ⊢[l] t.subst σ : A.subst σ) ∧
          ∀ {σ'}, IndWfSb Δ σ' Γ → IndEqSb Δ σ σ' Γ →
            Δ ⊢[l] t.subst σ ≡ t.subst σ' : A.subst σ) ∧
    (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A →
      ∀ {Δ σ σ'}, WfCtx Δ → IndWfSb Δ σ Γ → IndWfSb Δ σ' Γ → IndEqSb Δ σ σ' Γ →
        Δ ⊢[l] t.subst σ ≡ u.subst σ' : A.subst σ) := by
  have ih_subst (B a : Expr) (σ) :
      (B.subst a.toSb).subst σ = (B.subst (Expr.up σ)).subst (a.subst σ).toSb := by autosubst
  mutual_induction
  case snoc => exact True.intro
  all_goals try dsimp [Expr.subst] at *
  case bvar => grind [IndWfSb, IndEqSb]
  grind_cases
  case pi => grind [WfTp.pi, EqTp.cong_pi]
  case sigma => grind [WfTp.sigma, EqTp.cong_sigma]
  case univ => grind [WfTp.univ, EqTp.refl_tp]
  case el => grind [WfTp.el, EqTp.cong_el]
  case symm_tp => grind [IndEqSb.symm, EqTp.symm_tp]
  case trans_tp => grind [EqTp.trans_tp, IndEqSb.trans, IndEqSb.refl]
  case lam => grind [WfTm.lam, EqTm.cong_lam]
  case app => grind [WfTm.app, EqTm.cong_app]
  case pair => grind [WfTm.pair, EqTm.cong_pair]
  case fst => grind [WfTm.fst, EqTm.cong_fst]
  case snd =>
    constructor
    . rw [ih_subst]; apply WfTm.snd <;> grind
    . intros; rw [ih_subst]; apply EqTm.cong_snd <;> grind
  case code => grind [WfTm.code, EqTm.cong_code]
  case conv => grind [WfTm.conv, EqTm.conv_tm, IndEqSb.refl]
  case app_lam =>
    rw [ih_subst, ih_subst]
    apply (EqTm.app_lam ..).trans_tm
    . autosubst; grind [IndWfSb.snoc]
    . autosubst
      rename_i iht _ _ _ _ _ _ _ _
      apply (iht ..).2
      . grind [IndWfSb.snoc]
      . grind [IndEqSb.snoc]
      . grind
      . grind [IndWfSb.snoc]
    all_goals grind
  case fst_pair => apply (EqTm.fst_pair ..).trans_tm <;> grind
  case snd_pair =>
    rw [ih_subst]; apply (EqTm.snd_pair ..).trans_tm
    . autosubst; grind [IndWfSb.snoc]
    all_goals grind
  case lam_app ihA ihB ihf _ _ _ Δ σ σ' σσ' =>
    apply (ihf Δ σ |>.2 σ' σσ').trans_tm (by grind [WfTp.pi])
    have := EqTm.lam_app
      (ihA Δ σ').1
      (ihB (Δ.snoc (by grind))
      (σ'.up Δ (by grind))).1
      (ihf Δ σ').1
    convert this.conv_tm _ using 3 <;> autosubst
    grind [EqTp.cong_pi, IndEqSb.symm, Expr.up_eq_snoc]
  case pair_fst_snd =>
    apply (EqTm.pair_fst_snd ..).trans_tm <;>
      grind [WfTp.sigma, EqTm.cong_pair, EqTm.cong_fst, EqTm.cong_snd]
  case conv_tm => grind [EqTm.conv_tm, IndEqSb.refl]
  case symm_tm => grind [EqTm.symm_tm, EqTm.conv_tm, IndEqSb.symm]
  case trans_tm => grind [EqTm.trans_tm, EqTm.conv_tm, IndEqSb.trans, IndEqSb.refl]
  case cong_snd => rw [ih_subst]; apply EqTm.cong_snd <;> grind

end SubstProof


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
