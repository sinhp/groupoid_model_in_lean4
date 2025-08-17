import Mathlib.Tactic.Convert
import Mathlib.Tactic.SimpRw
import GroupoidModel.Syntax.Typing
import GroupoidModel.Tactic.MutualInduction
import GroupoidModel.Tactic.GrindCases

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
  unfold WfRen; intro _ _ _ lk; exact autosubst% lk

theorem wk (Γ A l) : WfRen ((A,l) :: Γ) Nat.succ Γ := by
  unfold WfRen; intro _ _ _ lk
  exact autosubst% Lookup.succ _ _ lk

theorem comp {Θ Δ Γ ξ₁ ξ₂} : WfRen Θ ξ₁ Δ → WfRen Δ ξ₂ Γ → WfRen Θ (ξ₁ ∘ ξ₂) Γ := by
  unfold WfRen; intro wf₁ wf₂ _ _ _ lk
  exact autosubst% wf₁ <| wf₂ lk

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

attribute [local grind ←] WfCtx.snoc WfRen.upr in
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
  all_goals try simp only [Expr.rename, ih_subst] at *
  case bvar ξ => apply WfTm.bvar _ (ξ.lookup _) <;> assumption
  -- Cases that didn't go through automatically.
  case lam_app' =>
    convert EqTm.lam_app' .. using 1
    . congr 2 <;> autosubst
    all_goals grind
  -- FIXME: automation fails completely on idRec
  case idRec' ihA iht ihC ihr ihu ihh _ _ Δ ξ =>
    have ΔA := ihA Δ ξ
    convert have ΔAI := ?ΔAI; WfTm.idRec' ΔA _ (ihC ΔAI ?ξuu) _ _ _ using 1
    . autosubst
    case ΔAI =>
      have := Δ.snoc ΔA
      apply this.snoc
      have x := WfTm.bvar this (.zero ..)
      exact autosubst% WfTp.Id'
        (ihA this (WfRen.wk .. |>.comp ξ))
        (iht this (WfRen.wk .. |>.comp ξ))
        (autosubst% x)
    case ξuu =>
      convert ξ.upr.upr using 1
      congr 3 <;> autosubst
    . grind
    . exact autosubst% (ihr Δ ξ)
    all_goals grind
  case cong_idRec' ihA iht ihtt ihC ihr ihu ihh _ _ Δ ξ =>
    have ΔA := ihA Δ ξ
    convert have ΔAI := ?ΔAI; EqTm.cong_idRec' ΔA (iht Δ ξ) _ (ihC ΔAI ?ξuu) ?ξr _ _ using 1
    . autosubst
    case ΔAI =>
      have := Δ.snoc ΔA
      apply this.snoc
      have x := WfTm.bvar this (.zero ..)
      exact autosubst% WfTp.Id'
        (ihA this (WfRen.wk .. |>.comp ξ))
        (iht this (WfRen.wk .. |>.comp ξ))
        (autosubst% x)
    case ξuu =>
      convert ξ.upr.upr using 1
      congr 3 <;> autosubst
    case ξr =>
      exact autosubst% (ihr Δ ξ)
    all_goals grind
  case idRec_refl' ihA iht ihC ihr _ _ Δ ξ =>
    have ΔA := ihA Δ ξ
    convert have ΔAI := ?ΔAI; EqTm.idRec_refl' ΔA (iht Δ ξ) (ihC ΔAI ?ξuu) _ using 1
    . autosubst
    case ΔAI =>
      have := Δ.snoc ΔA
      apply this.snoc
      have x := WfTm.bvar this (.zero ..)
      exact autosubst% WfTp.Id'
        (ihA this (WfRen.wk .. |>.comp ξ))
        (iht this (WfRen.wk .. |>.comp ξ))
        (autosubst% x)
    case ξuu =>
      convert ξ.upr.upr using 1
      congr 3 <;> autosubst
    . exact autosubst% (ihr Δ ξ)
  -- Other cases are automatic.
  grind_cases

/-! ## Lookup well-formedness -/

theorem Lookup.lt_length {Γ i A l} : Lookup Γ i A l → i < Γ.length := by
  intro lk; induction lk <;> (dsimp; omega)

theorem Lookup.lvl_eq {Γ i A l} (lk : Lookup Γ i A l) : l = (Γ[i]'lk.lt_length).2 := by
  induction lk <;> grind

theorem Lookup.tp_uniq {Γ i A A' l} (lk : Lookup Γ i A l) (lk' : Lookup Γ i A' l) : A = A' := by
  induction lk generalizing A' <;> grind [cases Lookup]

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

theorem tp_wk {Γ A B l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] B →
    (A, l) :: Γ ⊢[l'] B.subst Expr.wk :=
  fun Γ A B => autosubst% rename_all.1 B (Γ.snoc A) (WfRen.wk ..)

theorem eqTp_wk {Γ A B B' l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] B ≡ B' →
    (A, l) :: Γ ⊢[l'] B.subst Expr.wk ≡ B'.subst Expr.wk :=
  fun Γ A BB' => autosubst% rename_all.2.1 BB' (Γ.snoc A) (WfRen.wk ..)

theorem tm_wk {Γ A B b l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] b : B →
    (A, l) :: Γ ⊢[l'] b.subst Expr.wk : B.subst Expr.wk :=
  fun Γ A b => autosubst% rename_all.2.2.1 b (Γ.snoc A) (WfRen.wk ..)

theorem eqTm_wk {Γ A B b b' l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] b ≡ b' : B →
    (A, l) :: Γ ⊢[l'] b.subst Expr.wk ≡ b'.subst Expr.wk : B.subst Expr.wk :=
  fun Γ A eq => autosubst% rename_all.2.2.2 eq (Γ.snoc A) (WfRen.wk ..)

theorem eqSb_snoc {Δ Γ A t t' σ σ' l} : EqSb Δ σ σ' Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    Δ ⊢[l] t : A.subst σ → Δ ⊢[l] t' : A.subst σ' → Δ ⊢[l] t ≡ t' : A.subst σ →
    EqSb Δ (Expr.snoc σ t) (Expr.snoc σ' t') ((A,l) :: Γ) := by
  unfold EqSb
  intro σσ' A; intros
  refine ⟨σσ'.1, σσ'.2.1.snoc A, fun lk => ?_⟩
  cases lk <;> (autosubst; grind)

theorem eqSb_toSb {Γ A t t' l} : WfCtx Γ → Γ ⊢[l] A →
    Γ ⊢[l] t : A → Γ ⊢[l] t' : A → Γ ⊢[l] t ≡ t' : A →
    EqSb Γ t.toSb t'.toSb ((A,l) :: Γ) := by
  intro Γ A t t' tt'
  apply eqSb_snoc (EqSb.refl <| WfSb.id Γ)
  all_goals (try autosubst); grind [EqTp.refl_tp]

theorem wfSb_snoc {Δ Γ A t σ l} : WfSb Δ σ Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] t : A.subst σ →
    WfSb Δ (Expr.snoc σ t) ((A,l) :: Γ) :=
  fun h A Aσ t => eqSb_snoc (EqSb.refl h) A Aσ Aσ (EqTp.refl_tp Aσ) t t (EqTm.refl_tm t) |>.wf_left

theorem wfSb_toSb {Γ A t l} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] t : A → WfSb Γ t.toSb ((A, l) :: Γ) :=
  fun Γ A t => by unfold WfSb; exact eqSb_toSb Γ A t t (EqTm.refl_tm t)

theorem eqSb_up {Δ Γ A σ σ' l} : EqSb Δ σ σ' Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ → Δ ⊢[l] A.subst σ' → Δ ⊢[l] A.subst σ ≡ A.subst σ' →
    EqSb ((A.subst σ, l) :: Δ) (Expr.up σ) (Expr.up σ') ((A,l) :: Γ) := by
  unfold EqSb
  intro σσ' A Aσ Aσ' Aσeq
  have ΔAσ := σσ'.1.snoc Aσ
  refine ⟨ΔAσ, σσ'.2.1.snoc A, fun lk => ?_⟩
  cases lk
  . rw [Expr.up_eq_snoc σ, Expr.up_eq_snoc σ']
    repeat any_goals apply And.intro
    . exact autosubst% rename_all.1 Aσ ΔAσ (WfRen.wk ..)
    . exact autosubst% rename_all.1 Aσ' ΔAσ (WfRen.wk ..)
    . exact autosubst% rename_all.2.1 Aσeq ΔAσ (WfRen.wk ..)
    . exact autosubst% WfTm.bvar ΔAσ (Lookup.zero ..)
    . dsimp
      convert WfTm.conv (WfTm.bvar ΔAσ (Lookup.zero ..)) ?_
      exact autosubst% rename_all.2.1 Aσeq ΔAσ (WfRen.wk ..)
    . exact autosubst% EqTm.refl_tm (WfTm.bvar ΔAσ (Lookup.zero ..))
  next lk =>
    have := σσ'.2.2 lk
    repeat any_goals apply And.intro
    . exact autosubst% rename_all.1 this.1 ΔAσ (WfRen.wk ..)
    . exact autosubst% rename_all.1 this.2.1 ΔAσ (WfRen.wk ..)
    . exact autosubst% rename_all.2.1 this.2.2.1 ΔAσ (WfRen.wk ..)
    . convert rename_all.2.2.1 this.2.2.2.1 ΔAσ (WfRen.wk ..) using 1 <;>
        autosubst; rfl
    . convert autosubst% rename_all.2.2.1 this.2.2.2.2.1 ΔAσ (WfRen.wk ..) using 1 <;>
        autosubst; rfl
    . rw [Expr.up_eq_snoc σ, Expr.up_eq_snoc σ']
      convert rename_all.2.2.2 this.2.2.2.2.2 ΔAσ (WfRen.wk ..) using 1 <;>
        (autosubst; try rw [Expr.comp])

theorem wfSb_up {Δ Γ A σ l} : WfSb Δ σ Γ →
    Γ ⊢[l] A → Δ ⊢[l] A.subst σ →
    WfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A,l) :: Γ) :=
  fun h A Aσ => eqSb_up (EqSb.refl h) A Aσ Aσ (EqTp.refl_tp Aσ) |>.wf_left

theorem Id_bvar {Γ A t l} :
    WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] t : A →
    (A, l) :: Γ ⊢[l] .Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0) :=
  fun Γ A t => WfTp.Id' (tp_wk Γ A A) (tm_wk Γ A t) (.bvar (Γ.snoc A) (.zero ..))

attribute [local grind ←] WfCtx.snoc eqSb_up wfSb_up in
attribute [local grind →] EqSb.wf_left EqSb.wf_right in
attribute [local grind] -- TODO: fwd or bwd for properties of equality?
  EqTp.refl_tp EqTp.symm_tp EqTp.trans_tp
  EqTm.refl_tm EqTm.symm_tm' EqTm.trans_tm'
  EqSb.refl in
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
  mutual_induction WfCtx
  all_goals dsimp; try intros
  all_goals try simp only [Expr.subst_toSb_subst, Expr.subst_snoc_toSb_subst, Expr.subst] at *
  case bvar => grind [EqSb.lookup, WfSb.lookup]
  case pi' => grind [WfTp.pi', EqTp.cong_pi']
  case sigma' => grind [WfTp.sigma', EqTp.cong_sigma']
  case Id' => grind [WfTp.Id', EqTp.cong_Id]
  case univ => grind [WfSb.wf_dom, EqSb.wf_dom, WfTp.univ]
  case el => grind [WfTp.el, EqTp.cong_el]
  case symm_tp => grind [EqSb.symm]
  case lam' => grind [WfTm.lam', EqTm.cong_lam']
  case app' ihA _ _ _ =>
    constructor
    . grind [WfTm.app']
    . introv σ
      apply EqTm.cong_app' (ihA.1 σ.wf_left) <;> grind
  case pair' => grind [WfTm.pair', EqTm.cong_pair']
  case fst' => grind [WfTm.fst', EqTm.cong_fst']
  case snd' => grind [WfTm.snd', EqTm.cong_snd']
  case refl' => grind [WfTm.refl', EqTm.cong_refl']
  case idRec' A t _ _ _ _ ihA iht ihC _ _ _ =>
    constructor
    . introv σ
      have Γ := σ.wf_cod
      have Δ := σ.wf_dom
      have Aσ := ihA.1 σ
      apply WfTm.idRec' Aσ _ ?C
      case C =>
        apply ihC.1
        convert wfSb_up (wfSb_up σ A Aσ) (Id_bvar Γ A t) _ using 1
        . autosubst
        . exact autosubst% Id_bvar Δ Aσ (iht.1 σ)
      all_goals grind
    . introv σσ'
      have σ := σσ'.wf_left
      have σ' := σσ'.wf_right
      have Γ := σ.wf_cod
      have Δ := σ.wf_dom
      have Aσ := ihA.1 σ
      have Aσ' := ihA.1 σ'
      apply EqTm.cong_idRec' Aσ _ _ ?C
      case C =>
        apply ihC.2
        convert eqSb_up (eqSb_up σσ' A Aσ Aσ' (ihA.2 σσ')) (Id_bvar Γ A t) _ _ _ using 1
        . autosubst
        . exact autosubst% Id_bvar Δ Aσ (iht.1 σ)
        . exact autosubst% WfTp.Id' (tp_wk Δ Aσ Aσ') (tm_wk Δ Aσ (iht.1 σ'))
            (.conv (.bvar (Δ.snoc Aσ) (.zero ..)) (eqTp_wk Δ Aσ (ihA.2 σσ')))
        . have := (eqSb_up σσ' A Aσ Aσ' (ihA.2 σσ')).lookup (.zero ..)
          exact autosubst% EqTp.cong_Id
            (eqTp_wk Δ Aσ (ihA.2 σσ'))
            (eqTm_wk Δ Aσ (iht.2 σσ'))
            (autosubst% this)
      all_goals grind
  case code => grind [WfTm.code, EqTm.cong_code]
  case conv => grind [WfTm.conv, EqTm.conv_eq]
  case cong_idRec' A t _ _ _ _ _ ihA iht ihtt' ihC _ _ _ _ _ σσ' _ =>
    -- Note: copy-pasted from above.
    have σ := σσ'.wf_left
    have σ' := σσ'.wf_right
    have Γ := σ.wf_cod
    have Δ := σ.wf_dom
    have Aσ := ihA.1 σ
    have Aσ' := ihA.1 σ'
    apply EqTm.cong_idRec' Aσ _ _ ?C
    case C =>
      apply ihC
      convert eqSb_up (eqSb_up σσ' A Aσ Aσ' (ihA.2 σσ')) (Id_bvar Γ A t) _ _ _ using 1
      . autosubst
      . exact autosubst% Id_bvar Δ Aσ (iht.1 σ)
      . exact autosubst% WfTp.Id' (tp_wk Δ Aσ Aσ') (tm_wk Δ Aσ (iht.1 σ'))
          (.conv (.bvar (Δ.snoc Aσ) (.zero ..)) (eqTp_wk Δ Aσ (ihA.2 σσ')))
      . have := (eqSb_up σσ' A Aσ Aσ' (ihA.2 σσ')).lookup (.zero ..)
        exact autosubst% EqTp.cong_Id
          (eqTp_wk Δ Aσ (ihA.2 σσ'))
          (eqTm_wk Δ Aσ (iht.2 σσ'))
          (autosubst% this)
    all_goals grind
  case app_lam' =>
    apply (EqTm.app_lam' ..).trans_tm'
    . autosubst; grind [eqSb_snoc, wfSb_snoc]
    . autosubst
      rename_i iht _ _ _ _ _
      apply iht.2 <;> grind [eqSb_snoc]
    all_goals grind
  case fst_pair' => apply (EqTm.fst_pair' ..).trans_tm' <;> grind
  case snd_pair' =>
    apply (EqTm.snd_pair' ..).trans_tm'
    . autosubst; grind [eqSb_snoc, wfSb_snoc]
    all_goals grind
  case idRec_refl' A t _ _ ihA iht ihC _ _ _ σσ' _ =>
    have σ := σσ'.wf_left
    have σ' := σσ'.wf_right
    have Γ := σ.wf_cod
    have Δ := σ.wf_dom
    have Aσ := ihA.1 σ
    have Aσ' := ihA.1 σ'
    have Id := Id_bvar Γ A t
    apply (EqTm.idRec_refl' Aσ _ ?C ..).trans_tm' ?C'
    case C =>
      apply ihC.1
      convert wfSb_up (wfSb_up σ A Aσ) Id _ using 1
      . autosubst
      . exact autosubst% Id_bvar Δ Aσ (iht.1 σ)
    case C' =>
      autosubst; apply ihC.1
      have := wfSb_snoc σ A Aσ (iht.1 σ)
      apply wfSb_snoc this Id
      . exact autosubst% WfTp.Id' Aσ (iht.1 σ) (iht.1 σ)
      . exact autosubst% WfTm.refl' Aσ (iht.1 σ)
    all_goals grind
  case code_el iha _ _ _ eq =>
    have aσ' := iha.1 eq.wf_right
    have := aσ'.le_univMax
    apply (iha.2 eq).trans_tm' (WfTp.univ eq.wf_dom <| by omega)
    apply EqTm.code_el aσ'
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
  case symm_tm' => grind [EqTm.conv_eq, EqSb.symm]
  grind_cases

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

/-! ## Simplified WfSb/EqSb constructors -/

namespace WfSb

theorem snoc {Δ Γ A t σ l} : WfSb Δ σ Γ → Γ ⊢[l] A → Δ ⊢[l] t : A.subst σ →
    WfSb Δ (Expr.snoc σ t) ((A,l) :: Γ) :=
  fun σ A t => wfSb_snoc σ A (A.subst σ) t

theorem up {Δ Γ σ A l} : WfSb Δ σ Γ → Γ ⊢[l] A →
    WfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A, l) :: Γ) :=
  fun σ A => wfSb_up σ A (A.subst σ)

end WfSb

namespace EqSb

theorem up {Δ Γ σ σ' A l} : EqSb Δ σ σ' Γ → Γ ⊢[l] A →
    EqSb ((A.subst σ, l) :: Δ) (Expr.up σ) (Expr.up σ') ((A, l) :: Γ) :=
  fun σσ' A => eqSb_up σσ' A (A.subst σσ'.wf_left) (A.subst σσ'.wf_right) (A.subst_eq σσ')

end EqSb
