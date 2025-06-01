import GroupoidModel.Russell_PER_MS.LemmasAutosubst

set_option grind.warning false

/-! ## Inversion of typing -/

/- We hide proof-specific lemmas in a namespace. -/
namespace InvProof
open SubstProof

/-! ## Context conversion -/

theorem IndWfSb.conv_binder {Γ A A' l} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] A' → Γ ⊢[l] A ≡ A' →
    IndWfSb ((A', l) :: Γ) Expr.bvar ((A, l) :: Γ) := by
  intro Γ A A' AA'
  rw [show Expr.bvar = Expr.up Expr.bvar by autosubst]
  apply IndWfSb.snoc
  . apply IndWfSb.wk <;> assumption
  . convert rename_all.2.1 A (WfCtx.snoc Γ A') (@WfRen.wk _ _ _) using 1; autosubst; rfl
  . apply WfTm.conv (WfTm.bvar (WfCtx.snoc Γ A') (Lookup.zero ..))
    convert rename_all.2.2.1 AA'.symm_tp (WfCtx.snoc Γ A') (@WfRen.wk _ _ _) using 1 <;> autosubst
    rfl

theorem tp_conv_binder {Γ A A' B l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] A' → Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B → (A', l) :: Γ ⊢[l'] B := by
  intro Γ A A' AA' B
  convert (subst_all.2.1 B (WfCtx.snoc Γ A') (IndWfSb.conv_binder Γ A A' AA')).1 using 1
  autosubst

theorem tm_conv_binder {Γ A A' B t l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] A' → Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] t : B → (A', l) :: Γ ⊢[l'] t : B := by
  intro Γ A A' AA' t
  convert (subst_all.2.2.2.1 t (WfCtx.snoc Γ A') (IndWfSb.conv_binder Γ A A' AA')).1 using 1 <;>
    autosubst

/-! ## Weakening -/

-- TODO: weakening helpers could be used in `SubstProof`
theorem tp_wk {Γ A B l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] B →
    (A, l) :: Γ ⊢[l'] B.subst Expr.wk := by
  intro Γ A B
  convert rename_all.2.1 B (WfCtx.snoc Γ A) (@WfRen.wk _ _ _) using 1 <;> autosubst

theorem tm_wk {Γ A B b l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] b : B →
    (A, l) :: Γ ⊢[l'] b.subst Expr.wk : B.subst Expr.wk := by
  intro Γ A b
  convert rename_all.2.2.2.1 b (WfCtx.snoc Γ A) (@WfRen.wk _ _ _) using 1 <;> autosubst

/-! ## Instantiation -/

theorem tp_inst {Γ A B t l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] t : A → (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[l'] B.subst t.toSb :=
  fun Γ A t B =>
    subst_all.2.1 B Γ (IndWfSb.snoc (IndWfSb.id Γ)
      (by convert A; autosubst) (by convert t; autosubst)) |>.1

theorem tm_inst {Γ A B b t l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] t : A →
    (A, l) :: Γ ⊢[l'] b : B →
    Γ ⊢[l'] b.subst t.toSb : B.subst t.toSb :=
  fun Γ A t b =>
    subst_all.2.2.2.1 b Γ (IndWfSb.snoc (IndWfSb.id Γ)
      (by convert A; autosubst) (by convert t; autosubst)) |>.1

theorem eqtp_inst {Γ A B B' t t' l l'} : WfCtx Γ → Γ ⊢[l] A →
    Γ ⊢[l] t : A → Γ ⊢[l] t' : A → Γ ⊢[l] t ≡ t' : A →
    ((A, l) :: Γ) ⊢[l'] B ≡ B' →
    Γ ⊢[l'] B.subst t.toSb ≡ B'.subst t'.toSb := by
  intro Γ A t t' tt' BB'
  apply subst_all.2.2.1 BB' Γ (IndWfSb.snoc _ _ _) (IndWfSb.snoc _ _ _) (IndEqSb.snoc _ _ _ _ _)
  all_goals (try autosubst); grind [IndWfSb.id, IndEqSb.refl, EqTp.refl_tp]

attribute [local grind] tp_conv_binder tm_conv_binder in
theorem inv_all :
    (∀ {Γ}, WfCtx Γ → True) ∧
    (∀ {Γ l A}, Γ ⊢[l] A →
      WfCtx Γ) ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      (WfCtx Γ) ∧ (Γ ⊢[l] A) ∧ (Γ ⊢[l] B)) ∧
    (∀ {Γ l t A}, Γ ⊢[l] t : A →
      (WfCtx Γ) ∧ (Γ ⊢[l] A)) ∧
    (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A →
      (WfCtx Γ) ∧ (Γ ⊢[l] A) ∧ (Γ ⊢[l] t : A) ∧ (Γ ⊢[l] u : A)) := by
  mutual_induction
  case snoc => exact True.intro
  case bvar => grind [WfCtx.lookup_wf]
  grind_cases
  case cong_pi => grind [WfTp.pi]
  case cong_sigma => grind [WfTp.sigma]
  case cong_el => grind [WfTp.el]
  case lam => grind [WfTp.pi]
  case app => grind [tp_inst]
  case pair => grind [WfTp.sigma]
  case snd => grind [tp_inst, WfTm.fst]
  case code => grind [WfTp.univ]
  case cong_lam B _ _ _ _ _ _ _ _ _ _ _ _ =>
    refine ⟨?_, ?_, ?_, WfTm.conv (WfTm.lam (B := B) ?_ ?_) ?_⟩
    all_goals grind [WfTm.lam, EqTp.cong_pi, EqTp.refl_tp, EqTp.symm_tp, WfTp.pi]
  case cong_app Γ ihB ihf iha =>
    refine ⟨Γ, ?_, ?_,
      WfTm.conv
        (WfTm.app iha.2.1 ihB.2.2
          (WfTm.conv ihf.2.2.2 ?_)
          iha.2.2.2)
        ?_⟩
    all_goals grind [EqTp.cong_pi, EqTp.refl_tp, tp_inst, eqtp_inst, EqTp.symm_tp, WfTm.app]
  case cong_pair ihB iht ihu =>
    refine ⟨?_, ?_, ?_,
      WfTm.conv (WfTm.pair iht.2.1 ihB.2.2 ?_ (WfTm.conv ihu.2.2.2 ?_)) ?_⟩
    all_goals grind [WfTp.sigma, EqTp.cong_sigma, WfTm.pair, EqTp.refl_tp, EqTp.symm_tp, eqtp_inst]
  case cong_fst ihA ihB ihp =>
    refine ⟨?_, ?_, ?_, WfTm.conv (WfTm.fst ihA.2.2 ?_ (WfTm.conv ihp.2.2.2 ?_)) ?_⟩
    all_goals grind [WfTm.fst, EqTp.cong_sigma, EqTp.symm_tp]
  case cong_snd ihA ihB ihp =>
    refine ⟨?_, ?_, ?_,
      WfTm.conv (WfTm.snd ihA.2.2 ?_ (WfTm.conv ihp.2.2.2 ?_))
        (eqtp_inst ihA.1 ihA.2.1
          (WfTm.conv (WfTm.fst ihA.2.2 ?_ ?_) ?_)
          ?_ ?_ ?_)⟩
    all_goals grind [tp_inst, WfTm.fst, WfTm.snd, EqTp.cong_sigma, WfTm.conv, EqTp.cong_sigma,
      EqTm.symm_tm, EqTm.cong_fst, EqTp.symm_tp]
  case cong_code => grind [WfTp.univ, WfTm.code]
  case app_lam => grind [WfTm.app, WfTm.lam, tp_inst, tm_inst]
  case fst_pair => grind [WfTm.fst, WfTm.pair]
  case snd_pair A B _ _ _ _ _ _ =>
    refine ⟨?_, ?_, WfTm.conv (WfTm.snd ?_ ?_ ?_) ?_, ?_⟩
    all_goals grind [eqtp_inst, EqTp.refl_tp, EqTm.fst_pair, WfTm.fst, WfTm.pair]
  case lam_app A B _ _ _ Awf Bwf fwf Γwf _ _ =>
    refine ⟨?_, ?_, ?_, WfTm.lam ?_ ?app⟩
    -- TODO: automate this case more
    case app =>
      have : (B.subst (Expr.up Expr.wk)).subst (Expr.bvar 0).toSb = B := by autosubst
      conv => enter [4]; rw [← this]
      apply WfTm.app (A := A.subst Expr.wk)
      . grind [tp_wk]
      . apply (subst_all.2.1 Bwf _ _).1
        . grind [tp_wk, WfCtx.snoc]
        . apply IndWfSb.snoc
          . apply IndWfSb.ofRen
            . grind [tp_wk, WfCtx.snoc]
            . apply @WfRen.comp _ _ _ _ _ (@WfRen.wk _ _ _) (@WfRen.wk _ _ _)
          . convert tp_wk (B := A.subst Expr.wk) _ _ _ using 1
            . autosubst; rfl
            all_goals grind [tp_wk]
          . apply WfTm.bvar _ _
            . grind [WfCtx.snoc, tp_wk]
            . convert Lookup.zero _ _ _ using 1
              autosubst; rfl
      . exact tm_wk Γwf Awf fwf
      . exact WfTm.bvar (by grind) (Lookup.zero ..)
    all_goals grind
  case pair_fst_snd => grind [WfTm.pair, WfTm.fst, WfTm.snd]
  case conv_tm => grind [EqTp.symm_tp, WfTm.conv]

end InvProof

/-! ## Individual inversion lemmas -/

open InvProof
theorem WfTp.wf_ctx {Γ l A} : Γ ⊢[l] A → WfCtx Γ := inv_all.2.1
theorem EqTp.wf_left {Γ l A B} : Γ ⊢[l] A ≡ B → Γ ⊢[l] A := fun h => (inv_all.2.2.1 h).2.1
theorem EqTp.wf_right {Γ l A B} : Γ ⊢[l] A ≡ B → Γ ⊢[l] B := fun h => (inv_all.2.2.1 h).2.2
theorem EqTp.wf_ctx {Γ l A B} : Γ ⊢[l] A ≡ B → WfCtx Γ := fun h => h.wf_left.wf_ctx
theorem WfTm.wf_tp {Γ l t A} : Γ ⊢[l] t : A → Γ ⊢[l] A := fun h => (inv_all.2.2.2.1 h).2
theorem WfTm.wf_ctx {Γ l t A} : Γ ⊢[l] t : A → WfCtx Γ := fun h => h.wf_tp.wf_ctx
theorem EqTm.wf_left {Γ l t u A} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] t : A :=
  fun h => (inv_all.2.2.2.2 h).2.2.1
theorem EqTm.wf_right {Γ l t u A} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] u : A :=
  fun h => (inv_all.2.2.2.2 h).2.2.2
theorem EqTm.wf_tp {Γ l t u A} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] A := fun h => h.wf_left.wf_tp
theorem EqTm.wf_ctx {Γ l t u A} : Γ ⊢[l] t ≡ u : A → WfCtx Γ := fun h => h.wf_tp.wf_ctx

/-! ## Term former inversion -/

theorem WfTm.inv_app {Γ B C f a l l'} : Γ ⊢[l'] .app l l' B f a : C →
    ∃ A,
      (Γ ⊢[max l l'] f : .pi l l' A B) ∧
      (Γ ⊢[l] a : A) ∧
      (Γ ⊢[l'] C ≡ B.subst a.toSb) := by
  suffices
      (∀ {Γ}, WfCtx Γ → True) ∧
      (∀ {Γ l A}, Γ ⊢[l] A → True) ∧
      (∀ {Γ l A B}, Γ ⊢[l] A ≡ B → True) ∧
      (∀ {Γ l t C}, Γ ⊢[l] t : C → ∀ {B f a l₁}, t = .app l₁ l B f a →
        ∃ A,
          (Γ ⊢[max l₁ l] f : .pi l₁ l A B) ∧
          (Γ ⊢[l₁] a : A) ∧
          (Γ ⊢[l] C ≡ B.subst a.toSb)) ∧
      (∀ {Γ l t u A}, Γ ⊢[l] t ≡ u : A → True) from
    fun h => this.2.2.2.1 h rfl
  mutual_induction
  all_goals try exact True.intro
  all_goals rename_i eq; try cases eq
  case app => grind [InvProof.tp_inst, WfTp.wf_ctx, EqTp.refl_tp]
  case conv => grind [EqTp.symm_tp, EqTp.trans_tp]
