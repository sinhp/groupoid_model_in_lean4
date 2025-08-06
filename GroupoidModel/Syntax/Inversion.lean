import GroupoidModel.Syntax.Substitution

/-! ## Inversion of typing -/

/- We hide proof-specific lemmas in a namespace analogous to `SubstProof`. -/
namespace InvProof
open SubstProof

/-! ## Weakening -/

theorem wfSb_wk {Γ A l} : WfCtx Γ → Γ ⊢[l] A → WfSb ((A,l) :: Γ) Expr.wk Γ :=
  fun h h' => WfSb.ofRen (h.snoc h') h (WfRen.wk ..)

theorem tp_wk {Γ A B l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] B →
    (A, l) :: Γ ⊢[l'] B.subst Expr.wk :=
  fun Γ A B => B.subst (wfSb_wk Γ A)

theorem eqTp_wk {Γ A B B' l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] B ≡ B' →
    (A, l) :: Γ ⊢[l'] B.subst Expr.wk ≡ B'.subst Expr.wk :=
  fun Γ A BB' => BB'.subst (wfSb_wk Γ A)

theorem tm_wk {Γ A B b l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l'] b : B →
    (A, l) :: Γ ⊢[l'] b.subst Expr.wk : B.subst Expr.wk :=
  fun Γ A b => b.subst (wfSb_wk Γ A)

/-! ## Context conversion -/

theorem wfSb_conv_binder {Γ A A' l} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] A' → Γ ⊢[l] A ≡ A' →
    WfSb ((A', l) :: Γ) Expr.bvar ((A, l) :: Γ) := by
  intro Γ A A' AA'
  rw [show Expr.bvar = Expr.up Expr.bvar by autosubst, Expr.up_eq_snoc]
  apply wfSb_snoc
  . apply wfSb_wk <;> assumption
  . assumption
  . apply tp_wk Γ A' A
  . apply WfTm.conv (WfTm.bvar (WfCtx.snoc Γ A') (Lookup.zero ..))
    apply eqTp_wk Γ A' AA'.symm_tp

theorem tp_conv_binder {Γ A A' B l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] A' → Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B → (A', l) :: Γ ⊢[l'] B := by
  intro Γ A A' AA' B
  convert B.subst (wfSb_conv_binder Γ A A' AA') using 1
  autosubst

theorem tm_conv_binder {Γ A A' B t l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] A' → Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] t : B → (A', l) :: Γ ⊢[l'] t : B := by
  intro Γ A A' AA' t
  convert t.subst (wfSb_conv_binder Γ A A' AA') using 1 <;>
    autosubst

/-! ## Instantiation -/

theorem tp_inst {Γ A B t l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] t : A → (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[l'] B.subst t.toSb :=
  fun Γ A t B =>
    subst_all.1 B |>.1
      (wfSb_snoc (WfSb.id Γ) A (by convert A; autosubst) (by convert t; autosubst))

theorem tm_inst {Γ A B b t l l'} : WfCtx Γ → Γ ⊢[l] A → Γ ⊢[l] t : A →
    (A, l) :: Γ ⊢[l'] b : B →
    Γ ⊢[l'] b.subst t.toSb : B.subst t.toSb :=
  fun Γ A t b =>
    subst_all.2.2.1 b |>.1
      (wfSb_snoc (WfSb.id Γ) A (by convert A; autosubst) (by convert t; autosubst))

theorem eqtp_inst {Γ A B B' t t' l l'} : WfCtx Γ → Γ ⊢[l] A →
    Γ ⊢[l] t : A → Γ ⊢[l] t' : A → Γ ⊢[l] t ≡ t' : A →
    ((A, l) :: Γ) ⊢[l'] B ≡ B' →
    Γ ⊢[l'] B.subst t.toSb ≡ B'.subst t'.toSb := by
  intro Γ A t t' tt' BB'
  apply subst_all.2.1 BB' (eqSb_snoc ..)
  all_goals (try autosubst); grind [WfSb.id, EqSb.refl, EqTp.refl_tp]

attribute [local grind] tp_conv_binder tm_conv_binder in
theorem inv_all :
    (∀ {Γ l A}, Γ ⊢[l] A →
      WfCtx Γ) ∧
    (∀ {Γ l A B}, Γ ⊢[l] A ≡ B →
      (WfCtx Γ) ∧ (Γ ⊢[l] A) ∧ (Γ ⊢[l] B)) ∧
    (∀ {Γ l A t}, Γ ⊢[l] t : A →
      (WfCtx Γ) ∧ (Γ ⊢[l] A)) ∧
    (∀ {Γ l A t u}, Γ ⊢[l] t ≡ u : A →
      (WfCtx Γ) ∧ (Γ ⊢[l] A) ∧ (Γ ⊢[l] t : A) ∧ (Γ ⊢[l] u : A)) := by
  mutual_induction WfCtx
  all_goals dsimp; try intros
  case snoc => exact True.intro
  case bvar => grind [WfCtx.lookup_wf]
  grind_cases
  case cong_pi' => grind [WfTp.pi']
  case cong_sigma' => grind [WfTp.sigma']
  case cong_el => grind [WfTp.el]
  case el_code => grind [WfTp.el, WfTm.code]
  case lam' => grind [WfTp.pi']
  case app' => grind [tp_inst]
  case pair' => grind [WfTp.sigma']
  case snd' => grind [tp_inst, WfTm.fst']
  case code => grind [WfTp.univ]
  case cong_lam' B _ _ _ _ _ _ _ _ _ _ _ _ =>
    refine ⟨?_, ?_, ?_, WfTm.conv (WfTm.lam' (B := B) ?_ ?_) ?_⟩
    all_goals grind [WfTm.lam', EqTp.cong_pi', EqTp.refl_tp, EqTp.symm_tp, WfTp.pi']
  case cong_app' Γ ihB ihf iha =>
    refine ⟨Γ, ?_, ?_,
      WfTm.conv
        (WfTm.app' iha.2.1 ihB.2.2
          (WfTm.conv ihf.2.2.2 ?_)
          iha.2.2.2)
        ?_⟩
    all_goals grind [EqTp.cong_pi', EqTp.refl_tp, tp_inst, eqtp_inst, EqTp.symm_tp, WfTm.app']
  case cong_pair' ihB iht ihu =>
    refine ⟨?_, ?_, ?_,
      WfTm.conv (WfTm.pair' iht.2.1 ihB.2.2 ?_ (WfTm.conv ihu.2.2.2 ?_)) ?_⟩
    all_goals grind [WfTp.sigma', EqTp.cong_sigma', WfTm.pair', EqTp.refl_tp, EqTp.symm_tp,
      eqtp_inst]
  case cong_fst' ihA ihB ihp =>
    refine ⟨?_, ?_, ?_, WfTm.conv (WfTm.fst' ihA.2.2 ?_ (WfTm.conv ihp.2.2.2 ?_)) ?_⟩
    all_goals grind [WfTm.fst', EqTp.cong_sigma', EqTp.symm_tp]
  case cong_snd' ihA ihB ihp =>
    refine ⟨?_, ?_, ?_,
      WfTm.conv (WfTm.snd' ihA.2.2 ?_ (WfTm.conv ihp.2.2.2 ?_))
        (eqtp_inst ihA.1 ihA.2.1
          (WfTm.conv (WfTm.fst' ihA.2.2 ?_ ?_) ?_)
          ?_ ?_ ?_)⟩
    all_goals grind [tp_inst, WfTm.fst', WfTm.snd', EqTp.cong_sigma', WfTm.conv,
      EqTm.symm_tm', EqTm.cong_fst', EqTp.symm_tp]
  case cong_code => grind [WfTp.univ, WfTm.code]
  case app_lam' => grind [WfTm.app', WfTm.lam', tp_inst, tm_inst]
  case fst_pair' => grind [WfTm.fst', WfTm.pair']
  case snd_pair' A B _ _ _ _ _ _ =>
    refine ⟨?_, ?_, WfTm.conv (WfTm.snd' ?_ ?_ ?_) ?_, ?_⟩
    all_goals grind [eqtp_inst, EqTp.refl_tp, EqTm.fst_pair', WfTm.fst', WfTm.pair']
  case code_el => grind [WfTm.code, WfTp.el, WfTm.le_univMax]
  case lam_app' A B _ _ _ Awf Bwf fwf Γwf _ _ =>
    refine ⟨?_, ?_, ?_, WfTm.lam' ?_ ?app⟩
    -- TODO: automate this case more
    case app =>
      have : (B.subst (Expr.up Expr.wk)).subst (Expr.bvar 0).toSb = B := by autosubst
      conv in B => rw [← this]
      apply WfTm.app' (A := A.subst Expr.wk)
      . grind [tp_wk]
      . apply (subst_all.1 Bwf).1
        . rw [Expr.up_eq_snoc]
          apply wfSb_snoc _ Awf
          . convert tp_wk (B := A.subst Expr.wk) _ _ _ using 1
            . autosubst
            all_goals grind [tp_wk]
          . apply WfTm.bvar _ _
            . grind [WfCtx.snoc, tp_wk]
            . convert Lookup.zero _ _ _ using 1
              autosubst
          . apply WfSb.ofRen
            . grind [tp_wk, WfCtx.snoc]
            . assumption
            . apply WfRen.comp (WfRen.wk ..) (WfRen.wk ..)
      . exact tm_wk Γwf Awf fwf
      . exact WfTm.bvar (by grind) (Lookup.zero ..)
    all_goals grind
  case pair_fst_snd' => grind [WfTm.pair', WfTm.fst', WfTm.snd']
  case conv_eq => grind [EqTp.symm_tp, WfTm.conv]

end InvProof

/-! ## General inversion lemmas -/

open InvProof
theorem WfCtx.inv_snoc {Γ A l} : WfCtx ((A, l) :: Γ) → Γ ⊢[l] A | .snoc _ hA => hA
theorem WfTp.wf_ctx {Γ l A} : Γ ⊢[l] A → WfCtx Γ := inv_all.1
theorem EqTp.wf_left {Γ l A B} : Γ ⊢[l] A ≡ B → Γ ⊢[l] A := fun h => (inv_all.2.1 h).2.1
theorem EqTp.wf_right {Γ l A B} : Γ ⊢[l] A ≡ B → Γ ⊢[l] B := fun h => (inv_all.2.1 h).2.2
theorem EqTp.wf_ctx {Γ l A B} : Γ ⊢[l] A ≡ B → WfCtx Γ := fun h => h.wf_left.wf_ctx
theorem WfTm.wf_tp {Γ l t A} : Γ ⊢[l] t : A → Γ ⊢[l] A := fun h => (inv_all.2.2.1 h).2
theorem WfTm.wf_ctx {Γ l t A} : Γ ⊢[l] t : A → WfCtx Γ := fun h => h.wf_tp.wf_ctx
theorem EqTm.wf_left {Γ l t u A} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] t : A :=
  fun h => (inv_all.2.2.2 h).2.2.1
theorem EqTm.wf_right {Γ l t u A} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] u : A :=
  fun h => (inv_all.2.2.2 h).2.2.2
theorem EqTm.wf_tp {Γ l t u A} : Γ ⊢[l] t ≡ u : A → Γ ⊢[l] A := fun h => h.wf_left.wf_tp
theorem EqTm.wf_ctx {Γ l t u A} : Γ ⊢[l] t ≡ u : A → WfCtx Γ := fun h => h.wf_tp.wf_ctx
theorem WfTp.wf_binder {Γ A B l l'} : (A, l) :: Γ ⊢[l'] B → Γ ⊢[l] A := fun h => h.wf_ctx.inv_snoc
theorem EqTp.wf_binder {Γ A B B' l l'} : (A, l) :: Γ ⊢[l'] B ≡ B' → Γ ⊢[l] A :=
  fun h => h.wf_ctx.inv_snoc
theorem WfTm.wf_binder {Γ A B t l l'} : (A, l) :: Γ ⊢[l'] t : B → Γ ⊢[l] A :=
  fun h => h.wf_ctx.inv_snoc
theorem EqTm.wf_binder {Γ A B t u l l'} : (A, l) :: Γ ⊢[l'] t ≡ u : B → Γ ⊢[l] A :=
  fun h => h.wf_ctx.inv_snoc

/-! ## Substitution -/

namespace WfSb

theorem mk {Δ Γ σ} : WfCtx Δ → WfCtx Γ → (∀ {i A l}, Lookup Γ i A l → Δ ⊢[l] σ i : A.subst σ) →
    WfSb Δ σ Γ := by
  unfold WfSb EqSb
  intro Δ Γ h
  refine ⟨Δ, Γ, fun lk => ?_⟩
  replace h := h lk
  exact ⟨h.wf_tp, h.wf_tp, EqTp.refl_tp h.wf_tp, h, h, EqTm.refl_tm h⟩

theorem wk {Γ A l} : Γ ⊢[l] A → WfSb ((A, l) :: Γ) Expr.wk Γ :=
  fun A => InvProof.wfSb_wk A.wf_ctx A

theorem up {Δ Γ σ A l} : WfSb Δ σ Γ → Γ ⊢[l] A →
    WfSb ((A.subst σ, l) :: Δ) (Expr.up σ) ((A, l) :: Γ) :=
  fun σ A => SubstProof.wfSb_up σ A (A.subst σ)

theorem snoc {Δ Γ A t σ l} : WfSb Δ σ Γ → Γ ⊢[l] A → Δ ⊢[l] t : A.subst σ →
    WfSb Δ (Expr.snoc σ t) ((A,l) :: Γ) :=
  fun σ A t => SubstProof.wfSb_snoc σ A t.wf_tp t

theorem terminal {Δ} (σ) : WfCtx Δ → WfSb Δ σ [] :=
  fun Δ => mk Δ .nil nofun

theorem comp {Θ Δ Γ σ τ} : WfSb Θ σ Δ → WfSb Δ τ Γ → WfSb Θ (Expr.comp σ τ) Γ := by
  intro σ τ
  apply mk σ.wf_dom τ.wf_cod
  intro _ _ _ lk
  convert τ.lookup lk |>.subst σ using 1
  autosubst

theorem toSb {Γ A t l} : Γ ⊢[l] t : A → WfSb Γ t.toSb ((A, l) :: Γ) :=
  fun t => snoc (WfSb.id t.wf_ctx) t.wf_tp (by convert t; autosubst)

end WfSb

namespace EqSb

theorem mk {Δ Γ σ σ'} : WfCtx Δ → WfCtx Γ →
    (∀ {i A l}, Lookup Γ i A l →
      (Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧ (Δ ⊢[l] σ i ≡ σ' i : A.subst σ)) →
    EqSb Δ σ σ' Γ := by
  unfold EqSb
  intro Δ Γ h
  refine ⟨Δ, Γ, fun lk => ?_⟩
  replace h := h lk
  have A := Γ.lookup_wf lk
  exact ⟨h.1.wf_left, h.1.wf_right, h.1, h.2.wf_left, WfTm.conv h.2.wf_right h.1, h.2⟩

theorem up {Δ Γ σ σ' A l} : EqSb Δ σ σ' Γ → Γ ⊢[l] A →
    EqSb ((A.subst σ, l) :: Δ) (Expr.up σ) (Expr.up σ') ((A, l) :: Γ) :=
  fun σσ' A =>
    SubstProof.eqSb_up σσ' A (A.subst σσ'.wf_left) (A.subst σσ'.wf_right) (A.subst_eq σσ')

theorem snoc {Δ Γ A t t' σ σ' l} : EqSb Δ σ σ' Γ → Γ ⊢[l] A → Δ ⊢[l] t ≡ t' : A.subst σ →
    EqSb Δ (Expr.snoc σ t) (Expr.snoc σ' t') ((A,l) :: Γ) := by
  intro σσ' A tt'
  apply SubstProof.eqSb_snoc σσ' A (A.subst σσ'.wf_left) (A.subst σσ'.wf_right)
    (A.subst_eq σσ') tt'.wf_left (tt'.wf_right.conv (A.subst_eq σσ')) tt'

theorem terminal {Δ} (σ σ') : WfCtx Δ → EqSb Δ σ σ' [] :=
  fun Δ => mk Δ .nil nofun

theorem toSb {Γ t t' A l} : Γ ⊢[l] t ≡ t' : A → EqSb Γ t.toSb t'.toSb ((A, l) :: Γ) :=
  fun tt' => snoc (EqSb.refl <| WfSb.id tt'.wf_ctx) tt'.wf_tp (by convert tt'; autosubst)

end EqSb

/-! ## Type former inversion -/

theorem WfTp.inv_pi {Γ A B l₀ l l'} : Γ ⊢[l₀] .pi l l' A B →
    l₀ = max l l' ∧ ((A,l) :: Γ ⊢[l'] B) := by
  suffices
      ∀ {Γ l A}, Γ ⊢[l] A → ∀ {A' B l₁ l₂}, A = .pi l₁ l₂ A' B →
        l = max l₁ l₂ ∧ ((A', l₁) :: Γ ⊢[l₂] B) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

theorem WfTp.inv_sigma {Γ A B l₀ l l'} : Γ ⊢[l₀] .sigma l l' A B →
    l₀ = max l l' ∧ ((A,l) :: Γ ⊢[l'] B) := by
  suffices
      ∀ {Γ l A}, Γ ⊢[l] A → ∀ {A' B l₁ l₂}, A = .sigma l₁ l₂ A' B →
        l = max l₁ l₂ ∧ ((A', l₁) :: Γ ⊢[l₂] B) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

theorem WfTp.inv_univ {Γ l₀ l} : Γ ⊢[l₀] .univ l → l₀ = l+1 := by
  suffices ∀ {Γ l A}, Γ ⊢[l] A → ∀ {l₁}, A = .univ l₁ → l = l₁+1 from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

theorem WfTp.inv_el {Γ a l} : Γ ⊢[l] .el a → Γ ⊢[l+1] a : .univ l := by
  suffices ∀ {Γ l A}, Γ ⊢[l] A → ∀ {a}, A = .el a → Γ ⊢[l+1] a : .univ l from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

/-! ## Smart constructors -/

theorem WfTp.pi {Γ A B l l'} :
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] .pi l l' A B :=
  fun h => WfTp.pi' h.wf_binder h

theorem WfTp.sigma {Γ A B l l'} :
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] .sigma l l' A B :=
  fun h => WfTp.sigma' h.wf_binder h

theorem EqTp.cong_pi {Γ A A' B B' l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A' B' :=
  fun hAA' hBB' => EqTp.cong_pi' hAA'.wf_left hAA'.wf_right hAA' hBB'

theorem EqTp.cong_sigma {Γ A A' B B' l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .sigma l l' A B ≡ .sigma l l' A' B' :=
  fun hAA' hBB' => EqTp.cong_sigma' hAA'.wf_left hAA'.wf_right hAA' hBB'

theorem WfTm.lam {Γ A B t l l'} :
    (A, l) :: Γ ⊢[l'] t : B →
    Γ ⊢[max l l'] .lam l l' A t : .pi l l' A B :=
  fun h => WfTm.lam' h.wf_binder h

theorem WfTm.app {Γ A B f a l l'} :
    Γ ⊢[max l l'] f : .pi l l' A B →
    Γ ⊢[l] a : A →
    Γ ⊢[l'] .app l l' B f a : B.subst a.toSb :=
  fun hf ha =>
    have ⟨_, hB⟩ := hf.wf_tp.inv_pi
    WfTm.app' hB.wf_binder hB hf ha

theorem WfTm.pair {Γ A B t u l l'} :
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[max l l'] .pair l l' B t u : .sigma l l' A B :=
  fun hB ht hu => WfTm.pair' ht.wf_tp hB ht hu

theorem WfTm.fst {Γ A B p l l'} :
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l] .fst l l' A B p : A :=
  fun hp =>
    have ⟨_, hB⟩ := hp.wf_tp.inv_sigma
    WfTm.fst' hB.wf_binder hB hp

theorem WfTm.snd {Γ A B p l l'} :
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l'] .snd l l' A B p : B.subst (Expr.fst l l' A B p).toSb :=
  fun hp =>
    have ⟨_, hB⟩ := hp.wf_tp.inv_sigma
    WfTm.snd' hB.wf_binder hB hp

theorem EqTm.cong_lam {Γ A A' B t t' l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] t ≡ t' : B →
    Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A' t' : .pi l l' A B :=
  fun hAA' htt' => EqTm.cong_lam' hAA'.wf_left hAA'.wf_right hAA' htt'

theorem EqTm.cong_app {Γ A B B' f f' a a' l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] f ≡ f' : .pi l l' A B →
    Γ ⊢[l] a ≡ a' : A →
    Γ ⊢[l'] .app l l' B f a ≡ .app l l' B' f' a' : B.subst a.toSb :=
  fun hBB' hff' haa' => EqTm.cong_app' haa'.wf_tp hBB' hff' haa'

theorem EqTm.cong_pair {Γ A B B' t t' u u' l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l'] u ≡ u' : B.subst t.toSb →
    Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B' t' u' : .sigma l l' A B :=
  fun hBB' htt' huu' => EqTm.cong_pair' htt'.wf_tp hBB' htt' huu'

theorem EqTm.cong_fst {Γ A A' B B' p p' l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A' B' p' : A :=
  fun hAA' hBB' hpp' => EqTm.cong_fst' hAA'.wf_left hAA' hBB' hpp'

theorem EqTm.cong_snd {Γ A A' B B' p p' l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A' B' p' : B.subst (Expr.fst l l' A B p).toSb :=
  fun hAA' hBB' hpp' => EqTm.cong_snd' hAA'.wf_left hAA' hBB' hpp'

theorem EqTm.app_lam {Γ A B t u l l'} :
    (A, l) :: Γ ⊢[l'] t : B →
    Γ ⊢[l] u : A →
    Γ ⊢[l'] .app l l' B (.lam l l' A t) u ≡ t.subst u.toSb : B.subst u.toSb :=
  fun ht hu => EqTm.app_lam' hu.wf_tp ht.wf_tp ht hu

theorem EqTm.fst_pair {Γ A B t u l l'} :
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[l] .fst l l' A B (.pair l l' B t u) ≡ t : A :=
  fun hB ht hu => EqTm.fst_pair' ht.wf_tp hB ht hu

theorem EqTm.snd_pair {Γ A B t u l l'} :
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[l'] .snd l l' A B (.pair l l' B t u) ≡ u : B.subst t.toSb :=
  fun hB ht hu => EqTm.snd_pair' ht.wf_tp hB ht hu

theorem EqTm.lam_app {Γ A B f l l'} :
    Γ ⊢[max l l'] f : .pi l l' A B →
    Γ ⊢[max l l'] f ≡
      .lam l l' A (.app l l' (B.subst (Expr.up Expr.wk)) (f.subst Expr.wk) (.bvar 0)) :
      .pi l l' A B :=
  fun hf =>
    have ⟨_, hB⟩ := hf.wf_tp.inv_pi
    EqTm.lam_app' hB.wf_binder hB hf

theorem EqTm.pair_fst_snd {Γ A B p l l'} :
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[max l l'] p ≡ .pair l l' B (.fst l l' A B p) (.snd l l' A B p) : .sigma l l' A B :=
  fun hp =>
    have ⟨_, hB⟩ := hp.wf_tp.inv_sigma
    EqTm.pair_fst_snd' hB.wf_binder hB hp

theorem EqTm.symm_tm {Γ A t t' l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t : A :=
  fun htt' => EqTm.symm_tm' htt'.wf_tp htt'

theorem EqTm.trans_tm {Γ A t t' t'' l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t'' : A →
    Γ ⊢[l] t ≡ t'' : A :=
  fun htt' ht't'' => EqTm.trans_tm' htt'.wf_tp htt' ht't''

/-! ## Term former inversion -/

theorem WfTm.inv_bvar {Γ A i l} : Γ ⊢[l] .bvar i : A →
  ∃ B, Lookup Γ i B l ∧ (Γ ⊢[l] A ≡ B) := by
  suffices
    ∀ {Γ l C t}, Γ ⊢[l] t : C → ∀ {i}, t = .bvar i → ∃ B, Lookup Γ i B l ∧ (Γ ⊢[l] C ≡ B) from
  fun h => this h rfl
  mutual_induction WfCtx <;>
    grind [EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp, WfCtx.lookup_wf]

theorem WfTm.inv_lam {Γ A C b l₀ l l'} : Γ ⊢[l₀] .lam l l' A b : C →
    l₀ = max l l' ∧ ∃ B,
      ((A, l) :: Γ ⊢[l'] b : B) ∧ (Γ ⊢[max l l'] C ≡ .pi l l' A B) := by
  suffices
      ∀ {Γ l C t}, Γ ⊢[l] t : C → ∀ {A b l₁ l₂}, t = .lam l₁ l₂ A b →
        l = max l₁ l₂ ∧ ∃ B,
          ((A, l₁) :: Γ ⊢[l₂] b : B) ∧ (Γ ⊢[max l₁ l₂] C ≡ .pi l₁ l₂ A B) from
    fun h => this h rfl
  mutual_induction WfCtx <;>
    try grind [WfTp.pi, WfTm.wf_tp, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_app {Γ B C f a l₀ l l'} : Γ ⊢[l₀] .app l l' B f a : C →
    l₀ = l' ∧ ∃ A,
      (Γ ⊢[max l l'] f : .pi l l' A B) ∧ (Γ ⊢[l] a : A) ∧ (Γ ⊢[l'] C ≡ B.subst a.toSb) := by
  suffices
      ∀ {Γ l₀ C t}, Γ ⊢[l₀] t : C → ∀ {B f a l l'}, t = .app l l' B f a →
        l₀ = l' ∧ ∃ A,
          (Γ ⊢[max l l'] f : .pi l l' A B) ∧ (Γ ⊢[l] a : A) ∧ (Γ ⊢[l'] C ≡ B.subst a.toSb) from
    fun h => this h rfl
  mutual_induction WfCtx <;>
    grind [InvProof.tp_inst, WfTp.wf_ctx, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_pair {Γ B C t u l₀ l l'} : Γ ⊢[l₀] .pair l l' B t u : C →
    l₀ = max l l' ∧ ∃ A,
      (Γ ⊢[l] t : A) ∧
      (Γ ⊢[l'] u : B.subst t.toSb) ∧
      (Γ ⊢[l₀] C ≡ .sigma l l' A B) := by
  suffices
    ∀ {Γ l C t}, Γ ⊢[l] t : C → ∀ {B t' u' l₁ l₂}, t = .pair l₁ l₂ B t' u' →
      l = max l₁ l₂ ∧ ∃ A,
        (Γ ⊢[l₁] t' : A) ∧
        (Γ ⊢[l₂] u' : B.subst t'.toSb) ∧
        (Γ ⊢[l] C ≡ .sigma l₁ l₂ A B) from
  fun h => this h rfl
  mutual_induction WfCtx <;> grind [WfTp.sigma, WfTm.wf_tp, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_fst {Γ A B C p l₀ l l'} : Γ ⊢[l₀] .fst l l' A B p : C →
    l₀ = l ∧ (Γ ⊢[max l l'] p : .sigma l l' A B) ∧ (Γ ⊢[l₀] C ≡ A) := by
  suffices
      ∀ {Γ l C t}, Γ ⊢[l] t : C → ∀ {A B p l₁ l₂}, t = .fst l₁ l₂ A B p →
        l = l₁ ∧ (Γ ⊢[max l₁ l₂] p : .sigma l₁ l₂ A B) ∧ (Γ ⊢[l] C ≡ A) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind [EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_snd {Γ A B C p l₀ l l'} : Γ ⊢[l₀] .snd l l' A B p : C →
    l₀ = l' ∧ (Γ ⊢[max l l'] p : .sigma l l' A B) ∧
      (Γ ⊢[l₀] C ≡ B.subst (Expr.fst l l' A B p).toSb) := by
  suffices
      ∀ {Γ l C t}, Γ ⊢[l] t : C → ∀ {A B p l₁ l₂}, t = .snd l₁ l₂ A B p →
        l = l₂ ∧ (Γ ⊢[max l₁ l₂] p : .sigma l₁ l₂ A B) ∧
        (Γ ⊢[l] C ≡ B.subst (Expr.fst l₁ l₂ A B p).toSb) from
    fun h => this h rfl
  mutual_induction WfCtx <;>
    grind [InvProof.tp_inst, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp, WfTm.fst, WfTp.wf_ctx]

theorem WfTm.inv_code {Γ A C l₀} : Γ ⊢[l₀] .code A : C →
    ∃ l, l₀ = l+1 ∧ (Γ ⊢[l] A) ∧ (Γ ⊢[l+1] C ≡ .univ l) := by
  suffices
      ∀ {Γ l C t}, Γ ⊢[l] t : C → ∀ {A}, t = .code A →
        ∃ l₁, l = l₁+1 ∧ (Γ ⊢[l₁] A) ∧ (Γ ⊢[l₁+1] C ≡ .univ l₁) from
    fun h => this h rfl
  mutual_induction WfCtx <;> try grind [EqTp.refl_tp, WfTp.univ, WfTp.wf_ctx]
  case conv =>
    intros; rename_i ih _ _ eq
    obtain ⟨_, rfl, _⟩ := ih eq
    grind [EqTp.trans_tp, EqTp.symm_tp]
