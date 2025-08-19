import GroupoidModel.Syntax.Inversion

variable {χ : Type*} {E : Env χ} {Γ : Ctx χ}

/-! This module establishes consequences of typing inversion,
namely inversion lemmas for type/term formers,
and inference rules with fewer presuppositions. -/

/-! ## Type former inversion -/

theorem WfTp.inv_pi {Γ A B l₀ l l'} : E ∣ Γ ⊢[l₀] .pi l l' A B →
    l₀ = max l l' ∧ (E ∣ (A,l) :: Γ ⊢[l'] B) := by
  suffices
      ∀ {Γ l A}, E ∣ Γ ⊢[l] A → ∀ {A' B l₁ l₂}, A = .pi l₁ l₂ A' B →
        l = max l₁ l₂ ∧ (E ∣ (A', l₁) :: Γ ⊢[l₂] B) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

theorem WfTp.inv_sigma {Γ A B l₀ l l'} : E ∣ Γ ⊢[l₀] .sigma l l' A B →
    l₀ = max l l' ∧ (E ∣ (A,l) :: Γ ⊢[l'] B) := by
  suffices
      ∀ {Γ l A}, E ∣ Γ ⊢[l] A → ∀ {A' B l₁ l₂}, A = .sigma l₁ l₂ A' B →
        l = max l₁ l₂ ∧ (E ∣ (A', l₁) :: Γ ⊢[l₂] B) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

theorem WfTp.inv_Id {Γ A t u l₀ l} : E ∣ Γ ⊢[l₀] .Id l A t u →
    l₀ = l ∧ (E ∣ Γ ⊢[l] t : A) ∧ (E ∣ Γ ⊢[l] u : A) := by
  suffices
      ∀ {Γ l₀ T}, E ∣ Γ ⊢[l₀] T → ∀ {l t u}, T = .Id l A t u →
        l₀ = l ∧ (E ∣ Γ ⊢[l] t : A) ∧ (E ∣ Γ ⊢[l] u : A) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

theorem WfTp.inv_univ {Γ l₀ l} : E ∣ Γ ⊢[l₀] .univ l → l₀ = l+1 := by
  suffices ∀ {Γ l A}, E ∣ Γ ⊢[l] A → ∀ {l₁}, A = .univ l₁ → l = l₁+1 from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

theorem WfTp.inv_el {Γ a l} : E ∣ Γ ⊢[l] .el a → E ∣ Γ ⊢[l+1] a : .univ l := by
  suffices ∀ {Γ l A}, E ∣ Γ ⊢[l] A → ∀ {a}, A = .el a → E ∣ Γ ⊢[l+1] a : .univ l from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind

/-! ## Smart constructors -/

-- FIXME: write a generator for these lemmas.

variable [Fact E.Wf]

theorem WfTp.pi {A B l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[max l l'] .pi l l' A B :=
  fun B => WfTp.pi' B.wf_binder B

theorem WfTp.sigma {A B l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[max l l'] .sigma l l' A B :=
  fun B => WfTp.sigma' B.wf_binder B

theorem WfTp.Id {Γ A t u l} :
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l] u : A →
    E ∣ Γ ⊢[l] .Id l A t u :=
  fun t u => WfTp.Id' t.wf_tp t u

theorem EqTp.cong_pi {Γ A A' B B' l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A' B' :=
  fun hAA' hBB' => EqTp.cong_pi' hAA'.wf_left hAA'.wf_right hAA' hBB'

theorem EqTp.cong_sigma {Γ A A' B B' l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] .sigma l l' A B ≡ .sigma l l' A' B' :=
  fun hAA' hBB' => EqTp.cong_sigma' hAA'.wf_left hAA'.wf_right hAA' hBB'

theorem WfTm.lam {Γ A B t l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] t : B →
    E ∣ Γ ⊢[max l l'] .lam l l' A t : .pi l l' A B :=
  fun h => WfTm.lam' h.wf_binder h

theorem WfTm.app {Γ A B f a l l'} :
    E ∣ Γ ⊢[max l l'] f : .pi l l' A B →
    E ∣ Γ ⊢[l] a : A →
    E ∣ Γ ⊢[l'] .app l l' B f a : B.subst a.toSb :=
  fun hf ha =>
    have ⟨_, hB⟩ := hf.wf_tp.inv_pi
    WfTm.app' hB.wf_binder hB hf ha

theorem WfTm.pair {Γ A B t u l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l'] u : B.subst t.toSb →
    E ∣ Γ ⊢[max l l'] .pair l l' B t u : .sigma l l' A B :=
  fun hB ht hu => WfTm.pair' ht.wf_tp hB ht hu

theorem WfTm.fst {Γ A B p l l'} :
    E ∣ Γ ⊢[max l l'] p : .sigma l l' A B →
    E ∣ Γ ⊢[l] .fst l l' A B p : A :=
  fun hp =>
    have ⟨_, hB⟩ := hp.wf_tp.inv_sigma
    WfTm.fst' hB.wf_binder hB hp

theorem WfTm.snd {Γ A B p l l'} :
    E ∣ Γ ⊢[max l l'] p : .sigma l l' A B →
    E ∣ Γ ⊢[l'] .snd l l' A B p : B.subst (Expr.fst l l' A B p).toSb :=
  fun hp =>
    have ⟨_, hB⟩ := hp.wf_tp.inv_sigma
    WfTm.snd' hB.wf_binder hB hp

theorem WfTm.refl {Γ A t l} :
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l] .refl l t : .Id l A t t :=
  fun t => .refl' t.wf_tp t

theorem WfTm.idRec {Γ A M t r u h l l'} :
    E ∣ (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0), l) :: (A, l) :: Γ ⊢[l'] M →
    E ∣ Γ ⊢[l'] r : M.subst (.snoc t.toSb <| .refl l t) →
    E ∣ Γ ⊢[l] h : .Id l A t u →
    E ∣ Γ ⊢[l'] .idRec l l' t M r u h : M.subst (.snoc u.toSb h) :=
  fun M r h =>
    have ⟨_, t, u⟩ := h.wf_tp.inv_Id
    .idRec' t.wf_tp t M r u h

theorem EqTm.cong_lam {Γ A A' B t t' l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] t ≡ t' : B →
    E ∣ Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A' t' : .pi l l' A B :=
  fun hAA' htt' => EqTm.cong_lam' hAA'.wf_left hAA'.wf_right hAA' htt'

theorem EqTm.cong_app {Γ A B B' f f' a a' l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] f ≡ f' : .pi l l' A B →
    E ∣ Γ ⊢[l] a ≡ a' : A →
    E ∣ Γ ⊢[l'] .app l l' B f a ≡ .app l l' B' f' a' : B.subst a.toSb :=
  fun hBB' hff' haa' => EqTm.cong_app' haa'.wf_tp hBB' hff' haa'

theorem EqTm.cong_pair {Γ A B B' t t' u u' l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ Γ ⊢[l'] u ≡ u' : B.subst t.toSb →
    E ∣ Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B' t' u' : .sigma l l' A B :=
  fun hBB' htt' huu' => EqTm.cong_pair' htt'.wf_tp hBB' htt' huu'

theorem EqTm.cong_fst {Γ A A' B B' p p' l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    E ∣ Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A' B' p' : A :=
  fun hAA' hBB' hpp' => EqTm.cong_fst' hAA'.wf_left hAA' hBB' hpp'

theorem EqTm.cong_snd {Γ A A' B B' p p' l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    E ∣ Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A' B' p' : B.subst (Expr.fst l l' A B p).toSb :=
  fun hAA' hBB' hpp' => EqTm.cong_snd' hAA'.wf_left hAA' hBB' hpp'

theorem EqTm.cong_idRec {Γ A M M' t t' r r' u u' h h' l l'} :
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0), l) :: (A, l) :: Γ ⊢[l'] M ≡ M' →
    E ∣ Γ ⊢[l'] r ≡ r' : M.subst (.snoc t.toSb <| .refl l t) →
    E ∣ Γ ⊢[l] u ≡ u' : A →
    E ∣ Γ ⊢[l] h ≡ h' : .Id l A t u →
    E ∣ Γ ⊢[l'] .idRec l l' t M r u h ≡ .idRec l l' t' M' r' u' h' : M.subst (.snoc u.toSb h) :=
  fun teq Meq req ueq heq => .cong_idRec' teq.wf_tp teq.wf_left teq Meq req ueq heq

theorem EqTm.app_lam {Γ A B t u l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] t : B →
    E ∣ Γ ⊢[l] u : A →
    E ∣ Γ ⊢[l'] .app l l' B (.lam l l' A t) u ≡ t.subst u.toSb : B.subst u.toSb :=
  fun ht hu => EqTm.app_lam' hu.wf_tp ht.wf_tp ht hu

theorem EqTm.fst_pair {Γ A B t u l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l'] u : B.subst t.toSb →
    E ∣ Γ ⊢[l] .fst l l' A B (.pair l l' B t u) ≡ t : A :=
  fun hB ht hu => EqTm.fst_pair' ht.wf_tp hB ht hu

theorem EqTm.snd_pair {Γ A B t u l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l'] u : B.subst t.toSb →
    E ∣ Γ ⊢[l'] .snd l l' A B (.pair l l' B t u) ≡ u : B.subst t.toSb :=
  fun hB ht hu => EqTm.snd_pair' ht.wf_tp hB ht hu

theorem EqTm.cong_refl {Γ A t t' l} :
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ Γ ⊢[l] .refl l t ≡ .refl l t' : .Id l A t t :=
  fun t => .cong_refl' t.wf_tp t

theorem EqTm.idRec_refl {Γ A M t r l l'} :
    E ∣ Γ ⊢[l] t : A →
    E ∣ (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0), l) :: (A, l) :: Γ ⊢[l'] M →
    E ∣ Γ ⊢[l'] r : M.subst (.snoc t.toSb <| .refl l t) →
    E ∣ Γ ⊢[l'] .idRec l l' t M r t (.refl l t) ≡ r : M.subst (.snoc t.toSb <| .refl l t) :=
  fun t M r => .idRec_refl' t.wf_tp t M r

theorem EqTm.lam_app {Γ A B f l l'} :
    E ∣ Γ ⊢[max l l'] f : .pi l l' A B →
    E ∣ Γ ⊢[max l l'] f ≡
      .lam l l' A (.app l l' (B.subst (Expr.up Expr.wk)) (f.subst Expr.wk) (.bvar 0)) :
      .pi l l' A B :=
  fun hf =>
    have ⟨_, hB⟩ := hf.wf_tp.inv_pi
    EqTm.lam_app' hB.wf_binder hB hf

theorem EqTm.pair_fst_snd {Γ A B p l l'} :
    E ∣ Γ ⊢[max l l'] p : .sigma l l' A B →
    E ∣ Γ ⊢[max l l'] p ≡ .pair l l' B (.fst l l' A B p) (.snd l l' A B p) : .sigma l l' A B :=
  fun hp =>
    have ⟨_, hB⟩ := hp.wf_tp.inv_sigma
    EqTm.pair_fst_snd' hB.wf_binder hB hp

theorem EqTm.symm_tm {Γ A t t' l} :
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ Γ ⊢[l] t' ≡ t : A :=
  fun htt' => EqTm.symm_tm' htt'.wf_tp htt'

theorem EqTm.trans_tm {Γ A t t' t'' l} :
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ Γ ⊢[l] t' ≡ t'' : A →
    E ∣ Γ ⊢[l] t ≡ t'' : A :=
  fun htt' ht't'' => EqTm.trans_tm' htt'.wf_tp htt' ht't''

theorem WfTp.Id_bvar {Γ A t l} : E ∣ Γ ⊢[l] t : A →
    E ∣ (A, l) :: Γ ⊢[l] .Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0) :=
  fun t => .Id (t.subst (WfSb.wk t.wf_tp)) (.bvar (t.wf_ctx.snoc t.wf_tp) (.zero ..))

/-! ## Term former inversion -/

omit [Fact E.Wf] in
theorem WfTm.inv_bvar {Γ A i l} : E ∣ Γ ⊢[l] .bvar i : A →
  ∃ B, Lookup Γ i B l ∧ (E ∣ Γ ⊢[l] A ≡ B) := by
  suffices
      ∀ {Γ l C t}, E ∣ Γ ⊢[l] t : C → ∀ {i}, t = .bvar i → ∃ B,
        Lookup Γ i B l ∧ (E ∣ Γ ⊢[l] C ≡ B) from
    fun h => this h rfl
  mutual_induction WfCtx <;>
    grind [EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp, WfCtx.lookup_wf]

theorem WfTm.inv_lam {Γ A C b l₀ l l'} : E ∣ Γ ⊢[l₀] .lam l l' A b : C →
    l₀ = max l l' ∧ ∃ B,
      (E ∣ (A, l) :: Γ ⊢[l'] b : B) ∧ (E ∣ Γ ⊢[max l l'] C ≡ .pi l l' A B) := by
  suffices
      ∀ {Γ l C t}, E ∣ Γ ⊢[l] t : C → ∀ {A b l₁ l₂}, t = .lam l₁ l₂ A b →
        l = max l₁ l₂ ∧ ∃ B,
          (E ∣ (A, l₁) :: Γ ⊢[l₂] b : B) ∧ (E ∣ Γ ⊢[max l₁ l₂] C ≡ .pi l₁ l₂ A B) from
    fun h => this h rfl
  mutual_induction WfCtx <;>
    try grind [WfTp.pi, WfTm.wf_tp, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_app {Γ B C f a l₀ l l'} : E ∣ Γ ⊢[l₀] .app l l' B f a : C →
    l₀ = l' ∧ ∃ A,
      (E ∣ Γ ⊢[max l l'] f : .pi l l' A B) ∧ (E ∣ Γ ⊢[l] a : A) ∧
      (E ∣ Γ ⊢[l'] C ≡ B.subst a.toSb) := by
  suffices
      ∀ {Γ l₀ C t}, E ∣ Γ ⊢[l₀] t : C → ∀ {B f a l l'}, t = .app l l' B f a →
        l₀ = l' ∧ ∃ A,
          (E ∣ Γ ⊢[max l l'] f : .pi l l' A B) ∧ (E ∣ Γ ⊢[l] a : A) ∧
          (E ∣ Γ ⊢[l'] C ≡ B.subst a.toSb) from
    fun h => this h rfl
  mutual_induction WfCtx <;>
    grind [InvProof.tp_inst, WfTp.wf_ctx, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_pair {Γ B C t u l₀ l l'} : E ∣ Γ ⊢[l₀] .pair l l' B t u : C →
    l₀ = max l l' ∧ ∃ A,
      (E ∣ Γ ⊢[l] t : A) ∧
      (E ∣ Γ ⊢[l'] u : B.subst t.toSb) ∧
      (E ∣ Γ ⊢[l₀] C ≡ .sigma l l' A B) := by
  suffices
      ∀ {Γ l C t}, E ∣ Γ ⊢[l] t : C → ∀ {B t' u' l₁ l₂}, t = .pair l₁ l₂ B t' u' →
        l = max l₁ l₂ ∧ ∃ A,
          (E ∣ Γ ⊢[l₁] t' : A) ∧
          (E ∣ Γ ⊢[l₂] u' : B.subst t'.toSb) ∧
          (E ∣ Γ ⊢[l] C ≡ .sigma l₁ l₂ A B) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind [WfTp.sigma, WfTm.wf_tp, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

omit [Fact E.Wf] in
theorem WfTm.inv_fst {Γ A B C p l₀ l l'} : E ∣ Γ ⊢[l₀] .fst l l' A B p : C →
    l₀ = l ∧ (E ∣ Γ ⊢[max l l'] p : .sigma l l' A B) ∧ (E ∣ Γ ⊢[l₀] C ≡ A) := by
  suffices
      ∀ {Γ l C t}, E ∣ Γ ⊢[l] t : C → ∀ {A B p l₁ l₂}, t = .fst l₁ l₂ A B p →
        l = l₁ ∧ (E ∣ Γ ⊢[max l₁ l₂] p : .sigma l₁ l₂ A B) ∧ (E ∣ Γ ⊢[l] C ≡ A) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind [EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_snd {Γ A B C p l₀ l l'} : E ∣ Γ ⊢[l₀] .snd l l' A B p : C →
    l₀ = l' ∧ (E ∣ Γ ⊢[max l l'] p : .sigma l l' A B) ∧
      (E ∣ Γ ⊢[l₀] C ≡ B.subst (Expr.fst l l' A B p).toSb) := by
  suffices
      ∀ {Γ l C t}, E ∣ Γ ⊢[l] t : C → ∀ {A B p l₁ l₂}, t = .snd l₁ l₂ A B p →
        l = l₂ ∧ (E ∣ Γ ⊢[max l₁ l₂] p : .sigma l₁ l₂ A B) ∧
        (E ∣ Γ ⊢[l] C ≡ B.subst (Expr.fst l₁ l₂ A B p).toSb) from
    fun h => this h rfl
  mutual_induction WfCtx <;>
    grind [InvProof.tp_inst, EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp, WfTm.fst, WfTp.wf_ctx]

theorem WfTm.inv_refl {Γ C t l₀ l} : E ∣ Γ ⊢[l₀] .refl l t : C →
    l₀ = l ∧ ∃ A, (E ∣ Γ ⊢[l] t : A) ∧ (E ∣ Γ ⊢[l] C ≡ .Id l A t t) := by
  suffices
      ∀ {Γ l₀ C t'}, E ∣ Γ ⊢[l₀] t' : C → ∀ {l t}, t' = .refl l t →
        l₀ = l ∧ ∃ A, (E ∣ Γ ⊢[l] t : A) ∧ (E ∣ Γ ⊢[l] C ≡ .Id l A t t) from
    fun h => this h rfl
  mutual_induction WfCtx <;> grind [WfTp.Id,  EqTp.refl_tp, EqTp.symm_tp, EqTp.trans_tp]

theorem WfTm.inv_idRec {Γ M C t r u h l₀ l l'} : E ∣ Γ ⊢[l₀] .idRec l l' t M r u h : C →
    l₀ = l' ∧ ∃ A,
      (E ∣ Γ ⊢[l] t : A) ∧
      (E ∣ (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0), l) :: (A, l) :: Γ ⊢[l'] M) ∧
      (E ∣ Γ ⊢[l'] r : M.subst (.snoc t.toSb <| .refl l t)) ∧
      (E ∣ Γ ⊢[l] u : A) ∧
      (E ∣ Γ ⊢[l] h : .Id l A t u) ∧
      (E ∣ Γ ⊢[l'] C ≡ M.subst (.snoc u.toSb h)) := by
  suffices ∀ {Γ l₀ C t'}, E ∣ Γ ⊢[l₀] t' : C → ∀ {t M r u h l l'},
      t' = .idRec l l' t M r u h → l₀ = l' ∧ ∃ A,
        (E ∣ Γ ⊢[l] t : A) ∧
        (E ∣ (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0), l) :: (A, l) :: Γ ⊢[l'] M) ∧
        (E ∣ Γ ⊢[l'] r : M.subst (.snoc t.toSb <| .refl l t)) ∧
        (E ∣ Γ ⊢[l] u : A) ∧
        (E ∣ Γ ⊢[l] h : .Id l A t u) ∧
        (E ∣ Γ ⊢[l'] C ≡ M.subst (.snoc u.toSb h)) from
    fun h => this h rfl
  mutual_induction WfCtx
  all_goals intros; try exact True.intro
  all_goals rename_i eq; cases eq
  case refl t M r u h _ _ _ _ _ _ =>
    refine ⟨rfl, _, t, M, r, u, h, ?_⟩
    apply EqTp.refl_tp <| M.subst (WfSb.snoc (WfSb.toSb u) _ _)
    . grind [WfTp.Id_bvar, WfTp.wf_ctx]
    . autosubst; assumption
  case conv => grind [EqTp.trans_tp, EqTp.symm_tp]

theorem WfTm.inv_code {Γ A C l₀} : E ∣ Γ ⊢[l₀] .code A : C →
    ∃ l, l₀ = l+1 ∧ (E ∣ Γ ⊢[l] A) ∧ (E ∣ Γ ⊢[l+1] C ≡ .univ l) := by
  suffices
      ∀ {Γ l C t}, E ∣ Γ ⊢[l] t : C → ∀ {A}, t = .code A →
        ∃ l₁, l = l₁+1 ∧ (E ∣ Γ ⊢[l₁] A) ∧ (E ∣ Γ ⊢[l₁+1] C ≡ .univ l₁) from
    fun h => this h rfl
  mutual_induction WfCtx <;> try grind [EqTp.refl_tp, WfTp.univ, WfTp.wf_ctx]
  case conv =>
    intros; rename_i ih _ _ eq
    obtain ⟨_, rfl, _⟩ := ih eq
    grind [EqTp.trans_tp, EqTp.symm_tp]
