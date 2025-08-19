import GroupoidModel.Syntax.Typechecker.Value

/-! ## Inversion for value relations -/

variable {χ : Type*} {E : Env χ} [Fact E.Wf]

attribute [local grind]
  EqTp.refl_tp EqTp.symm_tp EqTp.trans_tp
  EqTm.refl_tm EqTm.symm_tm EqTm.trans_tm

theorem ValEqTp.inv_pi {Γ C vA vB l k k'} : ValEqTp E Γ l (.pi k k' vA vB) C →
    l = max k k' ∧ ∃ A B, ValEqTp E Γ k vA A ∧ ClosEqTp E Γ k k' A vB B ∧
      (E ∣ Γ ⊢[max k k'] C ≡ .pi k k' A B) := by
  suffices ∀ {Γ l vC C}, ValEqTp E Γ l vC C →
      ∀ {vA vB k k'}, vC = .pi k k' vA vB →
        l = max k k' ∧ ∃ A B, ValEqTp E Γ k vA A ∧ ClosEqTp E Γ k k' A vB B ∧
        (E ∣ Γ ⊢[max k k'] C ≡ .pi k k' A B) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.pi, ClosEqTp.wf_tp]

theorem ValEqTp.inv_sigma {Γ C vA vB l k k'} : ValEqTp E Γ l (.sigma k k' vA vB) C →
    l = max k k' ∧ ∃ A B, ValEqTp E Γ k vA A ∧ ClosEqTp E Γ k k' A vB B ∧
      (E ∣ Γ ⊢[max k k'] C ≡ .sigma k k' A B) := by
  suffices ∀ {Γ l vC C}, ValEqTp E Γ l vC C →
      ∀ {vA vB k k'}, vC = .sigma k k' vA vB →
        l = max k k' ∧ ∃ A B, ValEqTp E Γ k vA A ∧ ClosEqTp E Γ k k' A vB B ∧
        (E ∣ Γ ⊢[max k k'] C ≡ .sigma k k' A B) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.sigma, ClosEqTp.wf_tp]

theorem ValEqTp.inv_Id {Γ C vA vt vu l k} : ValEqTp E Γ l (.Id k vA vt vu) C →
    l = k ∧ ∃ A t u,
      ValEqTp E Γ k vA A ∧ ValEqTm E Γ k vt t A ∧ ValEqTm E Γ k vu u A ∧
      (E ∣ Γ ⊢[k] C ≡ .Id k A t u) := by
  suffices ∀ {Γ l vC C}, ValEqTp E Γ l vC C →
    ∀ {vA vt vu k}, vC = .Id k vA vt vu →
    l = k ∧ ∃ A t u, ValEqTp E Γ k vA A ∧ ValEqTm E Γ k vt t A ∧ ValEqTm E Γ k vu u A ∧
      (E ∣ Γ ⊢[k] C ≡ .Id k A t u) from
  fun h => this h rfl
  mutual_induction ValEqTp
  case Id =>
    introv vA vt vu
    have := WfTp.Id vt.wf_tm vu.wf_tm
    grind [EqTp.refl_tp]
  all_goals grind

omit [Fact E.Wf] in
theorem ValEqTp.inv_univ {Γ l k t} : ValEqTp E Γ l (.univ k) t → l = k + 1 ∧
    (E ∣ Γ ⊢[k + 1] t ≡ .univ k) := by
  suffices ∀ {Γ l vt t}, ValEqTp E Γ l vt t → ∀ {k}, vt = .univ k → l = k + 1 ∧
      (E ∣ Γ ⊢[k + 1] t ≡ .univ k) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.univ]

theorem ValEqTp.inv_el {Γ l na A} : ValEqTp E Γ l (.el na) A →
    ∃ a, NeutEqTm E Γ (l + 1) na a (.univ l) ∧
      (E ∣ Γ ⊢[l] A ≡ .el a) := by
  suffices ∀ {Γ l vA A}, ValEqTp E Γ l vA A → ∀ {na}, vA = .el na →
      ∃ a, NeutEqTm E Γ (l + 1) na a (.univ l) ∧
        (E ∣ Γ ⊢[l] A ≡ .el a) from
    fun h => this h rfl
  mutual_induction ValEqTp
  all_goals grind [WfTp.el, NeutEqTm.wf_tm]

theorem ValEqTm.inv_lam {Γ C vA vb t l₀ l l'} : ValEqTm E Γ l₀ (.lam l l' vA vb) t C →
    l₀ = max l l' ∧ ∃ A B b,
      (ValEqTp E Γ l vA A) ∧
      (ClosEqTm E Γ l l' A B vb b) ∧
      (E ∣ Γ ⊢[max l l'] t ≡ .lam l l' A b : C) ∧
      (E ∣ Γ ⊢[max l l'] C ≡ .pi l l' A B) := by
  suffices
      ∀ {Γ l₀ vt t C}, ValEqTm E Γ l₀ vt t C → ∀ {l l' vA vb}, vt = .lam l l' vA vb →
        l₀ = max l l' ∧ ∃ A B b, (ValEqTp E Γ l vA A) ∧
          (ClosEqTm E Γ l l' A B vb b) ∧
          (E ∣ Γ ⊢[max l l'] t ≡ .lam l l' A b : C) ∧
          (E ∣ Γ ⊢[max l l'] C ≡ .pi l l' A B) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_nf => grind [EqTm.conv_eq]
  case lam => grind [WfTm.lam, ClosEqTm.wf_tm, WfTm.wf_tp, WfTp.pi]

theorem ValEqTm.inv_pair {Γ C vt vu p l₀ l l'} : ValEqTm E Γ l₀ (.pair l l' vt vu) p C →
    l₀ = max l l' ∧ ∃ A B t u, (ValEqTm E Γ l vt t A) ∧ (ValEqTm E Γ l' vu u (B.subst t.toSb)) ∧
      (E ∣ Γ ⊢[max l l'] p ≡ .pair l l' B t u : C) ∧
      (E ∣ Γ ⊢[max l l'] C ≡ .sigma l l' A B) := by
  suffices
      ∀ {Γ l₀ vp p C}, ValEqTm E Γ l₀ vp p C → ∀ {vt vu l l'}, vp = .pair l l' vt vu →
        l₀ = max l l' ∧ ∃ A B t u,
          (ValEqTm E Γ l vt t A) ∧
          (ValEqTm E Γ l' vu u (B.subst t.toSb)) ∧
          (E ∣ Γ ⊢[max l l'] p ≡ .pair l l' B t u : C) ∧
          (E ∣ Γ ⊢[max l l'] C ≡ .sigma l l' A B) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_nf => grind [EqTm.conv_eq]
  case pair => grind [WfTm.pair, ValEqTm.wf_tm, WfTp.sigma]

theorem ValEqTm.inv_refl {Γ C vt r l₀ l} : ValEqTm E Γ l₀ (.refl l vt) r C →
    l₀ = l ∧ ∃ A t, (ValEqTm E Γ l vt t A) ∧
      (E ∣ Γ ⊢[l] r ≡ .refl l t : C) ∧ (E ∣ Γ ⊢[l] C ≡ .Id l A t t) := by
  suffices ∀ {Γ l₀ vr r C}, ValEqTm E Γ l₀ vr r C → ∀ {vt l}, vr = .refl l vt → l₀ = l ∧ ∃ A t,
      (ValEqTm E Γ l vt t A) ∧ (E ∣ Γ ⊢[l] r ≡ .refl l t : C) ∧ (E ∣ Γ ⊢[l] C ≡ .Id l A t t) from
    fun h => this h rfl
  mutual_induction ValEqTm
  case refl =>
    introv vt
    have := vt.wf_tm
    grind [WfTm.refl, WfTp.Id]
  all_goals grind [EqTm.conv_eq]

theorem NeutEqTm.inv_idRec {Γ C vA cM va vr nh j l₀ l l'} :
    NeutEqTm E Γ l₀ (.idRec l l' vA va cM vr nh) j C → l₀ = l' ∧ ∃ A M t r u h,
      (ValEqTp E Γ l vA A) ∧
      (ValEqTm E Γ l va t A) ∧
      (Clos₂EqTp E Γ A l (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0)) l l' cM M) ∧
      (ValEqTm E Γ l' vr r (M.subst (.snoc t.toSb <| .refl l t))) ∧
      (NeutEqTm E Γ l nh h (.Id l A t u)) ∧
      (E ∣ Γ ⊢[l'] j ≡ .idRec l l' t M r u h : C) ∧
      (E ∣ Γ ⊢[l'] C ≡ M.subst (.snoc u.toSb h)) := by
  suffices
    ∀ {Γ l₀ vj j C}, NeutEqTm E Γ l₀ vj j C → ∀ {vA cM va vr nh l l'},
      vj = .idRec l l' vA va cM vr nh → l₀ = l' ∧ ∃ A M t r u h,
        (ValEqTp E Γ l vA A) ∧
        (ValEqTm E Γ l va t A) ∧
        (Clos₂EqTp E Γ A l (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0)) l l' cM M) ∧
        (ValEqTm E Γ l' vr r (M.subst (.snoc t.toSb <| .refl l t))) ∧
        (NeutEqTm E Γ l nh h (.Id l A t u)) ∧
        (E ∣ Γ ⊢[l'] j ≡ .idRec l l' t M r u h : C) ∧
        (E ∣ Γ ⊢[l'] C ≡ M.subst (.snoc u.toSb h)) from
    fun h => this h rfl
  mutual_induction ValEqTm
  case idRec => grind [NeutEqTm.wf_tm, WfTm.wf_tp, → NeutEqTm.idRec]
  all_goals grind [EqTm.conv_eq]

theorem ValEqTm.inv_code {Γ C vA c l₀} : ValEqTm E Γ l₀ (.code vA) c C →
    ∃ l A, l₀ = l + 1 ∧
      (ValEqTp E Γ l vA A) ∧ (E ∣ Γ ⊢[l₀] c ≡ .code A : C) ∧ (E ∣ Γ ⊢[l₀] C ≡ .univ l) := by
  suffices
      ∀ {Γ l₀ vc c C}, ValEqTm E Γ l₀ vc c C → ∀ {vA}, vc = .code vA →
        ∃ l A, l₀ = l + 1 ∧
          (ValEqTp E Γ l vA A) ∧ (E ∣ Γ ⊢[l₀] c ≡ .code A : C) ∧ (E ∣ Γ ⊢[l₀] C ≡ .univ l) from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_nf => grind [EqTm.conv_eq]
  case code => grind [WfTp.univ, WfTm.code, ValEqTp.wf_tp, WfTp.wf_ctx]

omit [Fact E.Wf] in
theorem ValEqTm.inv_neut {Γ vA A vt t l} : ValEqTm E Γ l (.neut vt vA) t A →
    ValEqTp E Γ l vA A ∧ NeutEqTm E Γ l vt t A := by
  suffices ∀ {Γ l vt t A}, ValEqTm E Γ l vt t A → ∀ {n vA}, vt = .neut n vA →
      ValEqTp E Γ l vA A ∧ NeutEqTm E Γ l n t A from
    fun h => this h rfl
  mutual_induction ValEqTm
  all_goals grind [NeutEqTm.conv_neut, ValEqTp.conv_tp]

theorem NeutEqTm.inv_bvar {Γ A t i l} : NeutEqTm E Γ l (.bvar i) t A →
    ∃ A', Lookup Γ (Γ.length - i - 1) A' l ∧
      (E ∣ Γ ⊢[l] t ≡ .bvar (Γ.length - i - 1) : A) ∧ (E ∣ Γ ⊢[l] A ≡ A') := by
  suffices ∀ {Γ l vn n A}, NeutEqTm E Γ l vn n A → ∀ {i}, vn = .bvar i →
      ∃ A', Lookup Γ (Γ.length - i - 1) A' l ∧
        (E ∣ Γ ⊢[l] n ≡ .bvar (Γ.length - i - 1) : A) ∧ (E ∣ Γ ⊢[l] A ≡ A') from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case bvar Γ _ i _ Γwf lk =>
    have := lk.lt_length
    rw [show Γ.length - (Γ.length - i - 1) - 1 = i by omega]
    exact ⟨_, lk, EqTm.refl_tm (WfTm.bvar (by omega) lk), EqTp.refl_tp (Γwf.lookup_wf lk)⟩
  case conv_neut => grind [EqTm.conv_eq]

theorem NeutEqTm.inv_app {Γ vA C vf va t l₀ l l'} : NeutEqTm E Γ l₀ (.app l l' vA vf va) t C →
    l₀ = l' ∧ ∃ A B f a,
      ValEqTp E Γ l vA A ∧ NeutEqTm E Γ (max l l') vf f (.pi l l' A B) ∧ ValEqTm E Γ l va a A ∧
      (E ∣ Γ ⊢[l'] t ≡ .app l l' B f a : C) ∧ (E ∣ Γ ⊢[l'] C ≡ B.subst a.toSb) := by
  suffices ∀ {Γ l₀ vn n C}, NeutEqTm E Γ l₀ vn n C → ∀ {vA vf va l l'}, vn = .app l l' vA vf va →
      l₀ = l' ∧ ∃ A B f a,
        ValEqTp E Γ l vA A ∧ NeutEqTm E Γ (max l l') vf f (.pi l l' A B) ∧ ValEqTm E Γ l va a A ∧
        (E ∣ Γ ⊢[l'] n ≡ .app l l' B f a : C) ∧ (E ∣ Γ ⊢[l'] C ≡ B.subst a.toSb) from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_neut => grind [EqTm.conv_eq]
  case app =>
    grind [WfTm.app, ValEqTm.wf_tm, NeutEqTm.wf_tm, WfSb.toSb, WfTp.subst, WfTp.inv_pi, WfTm.wf_tp]

theorem NeutEqTm.inv_fst {Γ C vp f l₀ l l'} : NeutEqTm E Γ l₀ (.fst l l' vp) f C →
    l₀ = l ∧ ∃ A B p, NeutEqTm E Γ (max l l') vp p (.sigma l l' A B) ∧
      (E ∣ Γ ⊢[l] f ≡ .fst l l' A B p : C) ∧ (E ∣ Γ ⊢[l] C ≡ A) := by
  suffices ∀ {Γ l₀ vn n C}, NeutEqTm E Γ l₀ vn n C → ∀ {vp l l'}, vn = .fst l l' vp →
      l₀ = l ∧ ∃ A B p, NeutEqTm E Γ (max l l') vp p (.sigma l l' A B) ∧
      (E ∣ Γ ⊢[l] n ≡ .fst l l' A B p : C) ∧ (E ∣ Γ ⊢[l] C ≡ A) from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_neut => grind [EqTm.conv_eq]
  case fst =>
    grind [WfTm.fst, NeutEqTm.wf_tm, WfTm.wf_tp, WfTp.inv_sigma, WfTp.wf_ctx, WfCtx.inv_snoc]

theorem NeutEqTm.inv_snd {Γ C vp s l₀ l l'} : NeutEqTm E Γ l₀ (.snd l l' vp) s C →
    l₀ = l' ∧ ∃ A B p, NeutEqTm E Γ (max l l') vp p (.sigma l l' A B) ∧
      (E ∣ Γ ⊢[l'] s ≡ .snd l l' A B p : C) ∧ (E ∣ Γ ⊢[l'] C ≡ B.subst (Expr.fst l l' A B p).toSb) := by
  suffices ∀ {Γ l₀ vn n C}, NeutEqTm E Γ l₀ vn n C → ∀ {vp l l'}, vn = .snd l l' vp →
      l₀ = l' ∧ ∃ A B p, NeutEqTm E Γ (max l l') vp p (.sigma l l' A B) ∧
      (E ∣ Γ ⊢[l'] n ≡ .snd l l' A B p : C) ∧ (E ∣ Γ ⊢[l'] C ≡ B.subst (Expr.fst l l' A B p).toSb) from
    fun h => this h rfl
  mutual_induction NeutEqTm
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case conv_neut => grind [EqTm.conv_eq]
  case snd =>
    grind [WfTm.snd, NeutEqTm.wf_tm, WfTm.wf_tp, WfTp.inv_sigma, WfTp.wf_ctx, WfCtx.inv_snoc]
