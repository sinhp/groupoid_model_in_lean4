import GroupoidModel.Syntax.EqCtx
import Mathlib.Tactic.GCongr

/-! # `gcongr` lemmas

In this module we prove special-case congruence lemmas for use with `gcongr`.
Some of these have fewer premises than general congruences. -/

/- Note: `refl` lemmas are not marked `@[refl]`
because the `rfl` tactic expects unconditional reflexivity
whereas we have `Γ ⊢[l] A → Γ ⊢[l] A ≡ A`. -/

attribute [symm] EqTp.symm_tp
attribute [trans] EqTp.trans_tp

attribute [symm] EqTm.symm_tm
attribute [trans] EqTm.trans_tm

/-! ## Lemmas for types -/

attribute [gcongr] EqTp.cong_pi

@[gcongr]
theorem EqTp.cong_pi_dom {Γ A A' B l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A' B :=
  fun h h' => EqTp.cong_pi h (EqTp.refl_tp h')

@[gcongr]
theorem EqTp.cong_pi_cod {Γ A B B' l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A B' :=
  fun h => EqTp.cong_pi (EqTp.refl_tp h.wf_binder) h

attribute [gcongr] EqTp.cong_sigma

@[gcongr]
theorem EqTp.cong_sigma_dom {Γ A A' B l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] .sigma l l' A B ≡ .sigma l l' A' B :=
  fun h h' => EqTp.cong_sigma h (EqTp.refl_tp h')

@[gcongr]
theorem EqTp.cong_sigma_cod {Γ A B B' l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .sigma l l' A B ≡ .sigma l l' A B' :=
  fun h => EqTp.cong_sigma (EqTp.refl_tp h.wf_binder) h

attribute [gcongr] EqTp.cong_el

@[gcongr]
theorem EqTp.cong_Id_tp {Γ A A' t u l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] t : A →
    Γ ⊢[l] u : A →
    Γ ⊢[l] .Id A t u ≡ .Id A' t u :=
  fun A t u => .cong_Id A (.refl_tm t) (.refl_tm u)

@[gcongr]
theorem EqTp.cong_Id_left {Γ A t t' u l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] u : A →
    Γ ⊢[l] .Id A t u ≡ .Id A t' u :=
  fun h h' => .cong_Id (.refl_tp h.wf_tp) h (.refl_tm h')

@[gcongr]
theorem EqTp.cong_Id_right {Γ A t u u' l} :
    Γ ⊢[l] t : A →
    Γ ⊢[l] u ≡ u' : A →
    Γ ⊢[l] .Id A t u ≡ .Id A t u' :=
  fun h h' => .cong_Id (.refl_tp h.wf_tp) (.refl_tm h) h'

attribute [gcongr] EqTp.cong_Id

/-! ### Lemmas for terms -/

attribute [gcongr] EqTm.cong_lam

@[gcongr]
theorem EqTm.cong_lam_dom {Γ A A' B t l l'} :
    Γ ⊢[l] A ≡ A' →
    (A, l) :: Γ ⊢[l'] t : B →
    Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A' t : .pi l l' A B :=
  fun hAA' ht => EqTm.cong_lam hAA' (EqTm.refl_tm ht)

@[gcongr]
theorem EqTm.cong_lam_body {Γ A B t t' l l'} :
    (A, l) :: Γ ⊢[l'] t ≡ t' : B →
    Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A t' : .pi l l' A B :=
  fun htt' => EqTm.cong_lam (EqTp.refl_tp htt'.wf_binder) htt'

attribute [gcongr] EqTm.cong_app

@[gcongr]
theorem EqTm.cong_app_cod {Γ A B B' f a l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] f : .pi l l' A B →
    Γ ⊢[l] a : A →
    Γ ⊢[l'] .app l B f a ≡ .app l B' f a : B.subst a.toSb :=
  fun hBB' hf ha =>
    EqTm.cong_app hBB' (EqTm.refl_tm hf) (EqTm.refl_tm ha)

@[gcongr]
theorem EqTm.cong_app_fn {Γ A B f f' a l l'} :
    Γ ⊢[max l l'] f ≡ f' : .pi l l' A B →
    Γ ⊢[l] a : A →
    Γ ⊢[l'] .app l B f a ≡ .app l B f' a : B.subst a.toSb :=
  fun hff' ha =>
    EqTm.cong_app (EqTp.refl_tp hff'.wf_tp.inv_pi.2) hff' (EqTm.refl_tm ha)

@[gcongr]
theorem EqTm.cong_app_arg {Γ A B f a a' l l'} :
    Γ ⊢[max l l'] f : .pi l l' A B →
    Γ ⊢[l] a ≡ a' : A →
    Γ ⊢[l'] .app l B f a ≡ .app l B f a' : B.subst a.toSb :=
  fun hf haa' =>
    EqTm.cong_app (EqTp.refl_tp hf.wf_tp.inv_pi.2) (EqTm.refl_tm hf) haa'

attribute [gcongr] EqTm.cong_pair

@[gcongr]
theorem EqTm.cong_pair_cod {Γ A B B' t u l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B' t u : .sigma l l' A B :=
  fun BB' t u => .cong_pair BB' (EqTm.refl_tm t) (EqTm.refl_tm u)

@[gcongr]
theorem EqTm.cong_pair_fst {Γ A B t t' u l l'} :
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B t' u : .sigma l l' A B :=
  fun B tt' u => .cong_pair (EqTp.refl_tp B) tt' (EqTm.refl_tm u)

@[gcongr]
theorem EqTm.cong_pair_snd {Γ A B t u u' l l'} :
    (A, l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u ≡ u' : B.subst t.toSb →
    Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B t u' : .sigma l l' A B :=
  fun B t uu' => .cong_pair (EqTp.refl_tp B) (EqTm.refl_tm t) uu'

attribute [gcongr] EqTm.cong_fst

@[gcongr]
theorem EqTm.cong_fst_dom {Γ A A' B p l l'} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A' B p : A :=
  fun AA' p => .cong_fst AA' (EqTp.refl_tp p.wf_tp.inv_sigma.2) (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_fst_cod {Γ A B B' p l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A B' p : A :=
  fun BB' p => .cong_fst (EqTp.refl_tp BB'.wf_binder) BB' (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_fst_pair {Γ A B p p' l l'} :
    Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A B p' : A :=
  fun pp' =>
    have ⟨_, B⟩ := pp'.wf_tp.inv_sigma
    .cong_fst (EqTp.refl_tp B.wf_binder) (EqTp.refl_tp B) pp'

attribute [gcongr] EqTm.cong_snd

@[gcongr]
theorem EqTm.cong_snd_dom {Γ A A' B p l l'} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A' B p : B.subst (Expr.fst l l' A B p).toSb :=
  fun AA' p => .cong_snd AA' (EqTp.refl_tp p.wf_tp.inv_sigma.2) (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_snd_cod {Γ A B B' p l l'} :
    (A, l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A B' p : B.subst (Expr.fst l l' A B p).toSb :=
  fun BB' p => .cong_snd (EqTp.refl_tp BB'.wf_binder) BB' (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_snd_pair {Γ A B p p' l l'} :
    Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A B p' : B.subst (Expr.fst l l' A B p).toSb :=
  fun pp' =>
    have ⟨_, B⟩ := pp'.wf_tp.inv_sigma
    .cong_snd (EqTp.refl_tp B.wf_binder) (EqTp.refl_tp B) pp'

attribute [gcongr] EqTm.cong_refl
attribute [gcongr] EqTm.cong_idRec

/-! ## Lemmas for substitution -/

attribute [gcongr] WfTp.subst_eq
attribute [gcongr] EqTp.subst_eq
attribute [gcongr] WfTm.subst_eq
attribute [gcongr] EqTm.subst_eq

attribute [gcongr] EqTp.subst
attribute [gcongr] EqTm.subst
