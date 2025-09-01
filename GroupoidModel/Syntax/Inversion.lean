import GroupoidModel.Syntax.Substitution

variable {χ : Type*} {E : Axioms χ} {Θ Δ Γ : Ctx χ}
  {A A' B B' t t' b b' u u' : Expr χ}
  {σ σ' : Nat → Expr χ}
  {i l l' : Nat}

/-! ## Inversion of typing

In this module we prove that presuppositions hold of typing judgments:
e.g. if `E ∣ Γ ⊢[l] t : A` then `WfCtx Γ` and `E ∣ Γ ⊢[l] A`.
Note that `E.Wf` does not necessarily hold. -/

/- We hide proof-specific lemmas in a namespace analogous to `SubstProof`. -/
namespace InvProof
open SubstProof

/-! ## Helper lemmas -/

theorem eqSb_snoc' : EqSb E Δ σ σ' Γ → E ∣ Γ ⊢[l] A →
    E ∣ Δ ⊢[l] t : A.subst σ → E ∣ Δ ⊢[l] t' : A.subst σ' → E ∣ Δ ⊢[l] t ≡ t' : A.subst σ →
    EqSb E Δ (Expr.snoc σ t) (Expr.snoc σ' t') ((A,l) :: Γ) := by
  intro σσ' A t t' tt'
  apply eqSb_snoc σσ' A (A.subst σσ'.wf_left) (A.subst σσ'.wf_right) (A.subst_eq σσ') t t' tt'

theorem wfSb_conv_binder : WfCtx E Γ → E ∣ Γ ⊢[l] A → E ∣ Γ ⊢[l] A' → E ∣ Γ ⊢[l] A ≡ A' →
    WfSb E ((A', l) :: Γ) Expr.bvar ((A, l) :: Γ) := by
  intro Γ A A' AA'
  rw [show Expr.bvar = Expr.up Expr.bvar by autosubst, Expr.up_eq_snoc]
  apply WfSb.snoc
  . apply wfSb_wk <;> assumption
  . assumption
  . apply WfTm.conv (WfTm.bvar (WfCtx.snoc Γ A') (Lookup.zero ..))
    apply eqTp_wk Γ A' AA'.symm_tp

theorem tp_conv_binder : WfCtx E Γ → E ∣ Γ ⊢[l] A → E ∣ Γ ⊢[l] A' → E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] B → E ∣ (A', l) :: Γ ⊢[l'] B := by
  intro Γ A A' AA' B
  exact autosubst% B.subst (wfSb_conv_binder Γ A A' AA')

theorem tm_conv_binder : WfCtx E Γ → E ∣ Γ ⊢[l] A → E ∣ Γ ⊢[l] A' → E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] t : B → E ∣ (A', l) :: Γ ⊢[l'] t : B := by
  intro Γ A A' AA' t
  exact autosubst% t.subst (wfSb_conv_binder Γ A A' AA')

/-! ## Instantiation -/

theorem tp_inst : WfCtx E Γ → E ∣ Γ ⊢[l] A → E ∣ Γ ⊢[l] t : A → E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[l'] B.subst t.toSb :=
  fun Γ A t B => subst_all.1 B |>.1 ((WfSb.id Γ).snoc A (autosubst% t))

theorem tm_inst : WfCtx E Γ → E ∣ Γ ⊢[l] A → E ∣ Γ ⊢[l] t : A →
    E ∣ (A, l) :: Γ ⊢[l'] b : B →
    E ∣ Γ ⊢[l'] b.subst t.toSb : B.subst t.toSb :=
  fun Γ A t b => subst_all.2.2.1 b |>.1 ((WfSb.id Γ).snoc A (autosubst% t))

theorem eqtp_inst : WfCtx E Γ → E ∣ Γ ⊢[l] A →
    E ∣ Γ ⊢[l] t : A → E ∣ Γ ⊢[l] t' : A → E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ ((A, l) :: Γ) ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[l'] B.subst t.toSb ≡ B'.subst t'.toSb := by
  intro Γ A t t' tt' BB'
  apply subst_all.2.1 BB' (eqSb_snoc ..)
  all_goals (try autosubst); grind [WfSb.id, EqSb.refl, EqTp.refl_tp]

attribute [local grind] tp_conv_binder tm_conv_binder WfCtx.snoc in
theorem inv_all :
    (∀ {Γ l A}, E ∣ Γ ⊢[l] A →
      WfCtx E Γ) ∧
    (∀ {Γ l A B}, E ∣ Γ ⊢[l] A ≡ B →
      (WfCtx E Γ) ∧ (E ∣ Γ ⊢[l] A) ∧ (E ∣ Γ ⊢[l] B)) ∧
    (∀ {Γ l A t}, E ∣ Γ ⊢[l] t : A →
      (WfCtx E Γ) ∧ (E ∣ Γ ⊢[l] A)) ∧
    (∀ {Γ l A t u}, E ∣ Γ ⊢[l] t ≡ u : A →
      (WfCtx E Γ) ∧ (E ∣ Γ ⊢[l] A) ∧ (E ∣ Γ ⊢[l] t : A) ∧ (E ∣ Γ ⊢[l] u : A)) := by
  mutual_induction WfCtx
  all_goals dsimp; try intros
  case bvar => grind [WfCtx.lookup_wf]
  case cong_pi' => grind [WfTp.pi']
  case cong_sigma' => grind [WfTp.sigma']
  case cong_Id => grind [WfTp.Id', WfTm.conv]
  case cong_el => grind [WfTp.el]
  case el_code => grind [WfTp.el, WfTm.code]
  case lam' => grind [WfTp.pi']
  case app' => grind [tp_inst]
  case pair' => grind [WfTp.sigma']
  case snd' => grind [tp_inst, WfTm.fst']
  case refl' => grind [WfTp.Id']
  case idRec' C _ _ h _ _ _ _ _ _ =>
    refine ⟨?_, ?C⟩
    case C =>
      apply C.subst ((wfSb_toSb _ _ _).snoc _ (autosubst% h))
      all_goals grind [Id_bvar]
    all_goals grind
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
  case cong_refl' eq iheq =>
    refine ⟨?_, ?_, ?_, ?c⟩
    case c =>
      apply (WfTm.refl' iheq.2.1 iheq.2.2.2).conv
      grind [EqTp.cong_Id, EqTm.symm_tm', EqTp.refl_tp]
    all_goals grind [WfTp.Id', WfTm.refl']
  case cong_idRec' A t teq Ceq _ ueq heq _ _ iht ihC ihr _ ihh =>
    refine ⟨?_, ?C, ?_, ?c⟩
    case C =>
      apply ihC.2.1.subst <| WfSb.snoc (wfSb_toSb _ _ _) _ (autosubst% ihh.2.2.1)
      all_goals grind [Id_bvar]
    case c =>
      apply (WfTm.idRec' iht.2.1 ..).conv
      . apply EqTp.symm_tp
        apply Ceq.subst_eq
        apply eqSb_snoc' (eqSb_toSb ..) _ ?hwf ?h'wf ?hh'
        case hwf => exact autosubst% ihh.2.2.1
        case h'wf =>
          autosubst
          apply ihh.2.2.2.conv <| EqTp.cong_Id (.refl_tp A) (.refl_tm t) ueq
        case hh' => exact autosubst% heq
        all_goals grind [Id_bvar, EqTm.symm_tm']
      . grind
      . apply tp_conv_binder _ _ _ ?eq ihC.2.2
        case eq =>
          apply EqTp.cong_Id (.refl_tp <| tp_wk _ A A) (eqTm_wk _ _ teq)
              (EqTm.refl_tm (WfTm.bvar _ (.zero ..)))
            <;> grind
        all_goals grind [Id_bvar]
      . apply ihr.2.2.2.conv
        apply Ceq.subst_eq
        apply eqSb_snoc' (eqSb_toSb ..) _ _ ?rwf _
        case rwf =>
          autosubst
          apply (WfTm.refl' A iht.2.2.2).conv
          grind [EqTp.cong_Id, EqTm.symm_tm', EqTm.refl_tm, EqTp.refl_tp]
        all_goals (try autosubst); grind [Id_bvar, WfTm.refl', EqTm.cong_refl']
      . grind
      . grind [EqTp.cong_Id, WfTm.conv, EqTp.refl_tp]
    all_goals grind [WfTm.idRec']
  case cong_code => grind [WfTp.univ, WfTm.code]
  case app_lam' => grind [WfTm.app', WfTm.lam', tp_inst, tm_inst]
  case fst_pair' => grind [WfTm.fst', WfTm.pair']
  case snd_pair' A B _ _ _ _ _ _ =>
    refine ⟨?_, ?_, WfTm.conv (WfTm.snd' ?_ ?_ ?_) ?_, ?_⟩
    all_goals grind [eqtp_inst, EqTp.refl_tp, EqTm.fst_pair', WfTm.fst', WfTm.pair']
  case code_el => grind [WfTm.code, WfTp.el, WfTm.le_univMax]
  case idRec_refl' ihA _ _ =>
    refine ⟨?_, ?_, ?r, ?_⟩
    case r => apply WfTm.idRec' ihA.2 <;> grind [WfTm.refl']
    all_goals grind
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
          apply WfSb.snoc _ Awf
          . apply WfTm.bvar _ _
            . grind [WfCtx.snoc, tp_wk]
            . rw [show ∀ (A : Expr χ), A.subst (Expr.comp Expr.wk Expr.wk) =
                (A.subst Expr.wk).subst Expr.wk by intro; autosubst]
              apply Lookup.zero
          . apply WfSb.ofRen
            . grind [tp_wk, WfCtx.snoc]
            . assumption
            . apply WfRen.comp (WfRen.wk ..) (WfRen.wk ..)
      . exact tm_wk Γwf Awf fwf
      . exact WfTm.bvar (by grind) (Lookup.zero ..)
    all_goals grind
  case pair_fst_snd' => grind [WfTm.pair', WfTm.fst', WfTm.snd']
  case conv_eq => grind [EqTp.symm_tp, WfTm.conv]
  grind_cases

end InvProof

/-! ## General inversion lemmas -/

theorem WfCtx.inv_snoc : WfCtx E ((A, l) :: Γ) → E ∣ Γ ⊢[l] A | .snoc _ hA => hA

section
open InvProof

theorem WfTp.wf_ctx : E ∣ Γ ⊢[l] A → WfCtx E Γ := inv_all.1
theorem EqTp.wf_left : E ∣ Γ ⊢[l] A ≡ B → E ∣ Γ ⊢[l] A := fun h => (inv_all.2.1 h).2.1
theorem EqTp.wf_right : E ∣ Γ ⊢[l] A ≡ B → E ∣ Γ ⊢[l] B := fun h => (inv_all.2.1 h).2.2
theorem EqTp.wf_ctx : E ∣ Γ ⊢[l] A ≡ B → WfCtx E Γ := fun h => h.wf_left.wf_ctx
theorem WfTm.wf_tp : E ∣ Γ ⊢[l] t : A → E ∣ Γ ⊢[l] A := fun h => (inv_all.2.2.1 h).2
theorem WfTm.wf_ctx : E ∣ Γ ⊢[l] t : A → WfCtx E Γ := fun h => h.wf_tp.wf_ctx
theorem EqTm.wf_left : E ∣ Γ ⊢[l] t ≡ u : A → E ∣ Γ ⊢[l] t : A :=
  fun h => (inv_all.2.2.2 h).2.2.1
theorem EqTm.wf_right : E ∣ Γ ⊢[l] t ≡ u : A → E ∣ Γ ⊢[l] u : A :=
  fun h => (inv_all.2.2.2 h).2.2.2
theorem EqTm.wf_tp : E ∣ Γ ⊢[l] t ≡ u : A → E ∣ Γ ⊢[l] A := fun h => h.wf_left.wf_tp
theorem EqTm.wf_ctx : E ∣ Γ ⊢[l] t ≡ u : A → WfCtx E Γ := fun h => h.wf_tp.wf_ctx
theorem WfTp.wf_binder : E ∣ (A, l) :: Γ ⊢[l'] B → E ∣ Γ ⊢[l] A :=
  fun h => h.wf_ctx.inv_snoc
theorem EqTp.wf_binder : E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' → E ∣ Γ ⊢[l] A :=
  fun h => h.wf_ctx.inv_snoc
theorem WfTm.wf_binder : E ∣ (A, l) :: Γ ⊢[l'] t : B → E ∣ Γ ⊢[l] A :=
  fun h => h.wf_ctx.inv_snoc
theorem EqTm.wf_binder : E ∣ (A, l) :: Γ ⊢[l'] t ≡ u : B → E ∣ Γ ⊢[l] A :=
  fun h => h.wf_ctx.inv_snoc
end

/-! ## Substitution -/

namespace WfSb

theorem mk : WfCtx E Δ → WfCtx E Γ → (∀ {i A l}, Lookup Γ i A l → E ∣ Δ ⊢[l] σ i : A.subst σ) →
    WfSb E Δ σ Γ := by
  unfold WfSb EqSb
  intro Δ Γ h
  refine ⟨Δ, Γ, fun lk => ?_⟩
  replace h := h lk
  exact ⟨h.wf_tp, h.wf_tp, EqTp.refl_tp h.wf_tp, h, h, EqTm.refl_tm h⟩

theorem wk : E ∣ Γ ⊢[l] A → WfSb E ((A, l) :: Γ) Expr.wk Γ :=
  fun A => SubstProof.wfSb_wk A.wf_ctx A

theorem terminal (σ) : WfCtx E Δ → WfSb E Δ σ [] :=
  fun Δ => mk Δ .nil nofun

theorem comp : WfSb E Θ σ Δ → WfSb E Δ σ' Γ → WfSb E Θ (Expr.comp σ σ') Γ := by
  intro σ σ'
  apply mk σ.wf_dom σ'.wf_cod
  intro _ _ _ lk
  exact autosubst% σ'.lookup lk |>.subst σ

theorem toSb : E ∣ Γ ⊢[l] t : A → WfSb E Γ t.toSb ((A, l) :: Γ) :=
  fun t => SubstProof.wfSb_toSb t.wf_ctx t.wf_tp t

end WfSb

namespace EqSb

theorem mk : WfCtx E Δ → WfCtx E Γ →
    (∀ {i A l}, Lookup Γ i A l →
      (E ∣ Δ ⊢[l] A.subst σ ≡ A.subst σ') ∧ (E ∣ Δ ⊢[l] σ i ≡ σ' i : A.subst σ)) →
    EqSb E Δ σ σ' Γ := by
  unfold EqSb
  intro Δ Γ h
  refine ⟨Δ, Γ, fun lk => ?_⟩
  replace h := h lk
  have A := Γ.lookup_wf lk
  exact ⟨h.1.wf_left, h.1.wf_right, h.1, h.2.wf_left, WfTm.conv h.2.wf_right h.1, h.2⟩

theorem snoc : EqSb E Δ σ σ' Γ → E ∣ Γ ⊢[l] A → E ∣ Δ ⊢[l] t ≡ t' : A.subst σ →
    EqSb E Δ (Expr.snoc σ t) (Expr.snoc σ' t') ((A,l) :: Γ) := by
  intro σσ' A tt'
  apply SubstProof.eqSb_snoc σσ' A (A.subst σσ'.wf_left) (A.subst σσ'.wf_right)
    (A.subst_eq σσ') tt'.wf_left (tt'.wf_right.conv (A.subst_eq σσ')) tt'

theorem terminal (σ σ') : WfCtx E Δ → EqSb E Δ σ σ' [] :=
  fun Δ => mk Δ .nil nofun

theorem toSb : E ∣ Γ ⊢[l] t ≡ t' : A → EqSb E Γ t.toSb t'.toSb ((A, l) :: Γ) :=
  fun tt' => snoc (EqSb.refl <| WfSb.id tt'.wf_ctx) tt'.wf_tp (autosubst% tt')

end EqSb
