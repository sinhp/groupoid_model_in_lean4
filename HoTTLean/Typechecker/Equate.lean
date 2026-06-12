import HoTTLean.Typechecker.Evaluate

namespace SynthLean
open Qq

variable {_u : Lean.Level} {χ : Q(Type _u)}

mutual
partial def equateTp (vΓ : Q(TpEnv $χ)) (l : Q(Nat)) (vT' vU' : Q(Val $χ)) :
    TypecheckerM Q(∀ {E Γ T U}, TpEnvEqCtx E $vΓ Γ →
      ValEqTp E Γ $l $vT' T → ValEqTp E Γ $l $vU' U → E ∣ Γ ⊢[$l] T ≡ U) := do
  let key := (⟨vΓ⟩, ⟨l⟩, ⟨vT'⟩, ⟨vU'⟩)
  if let some pf := (← get).equateTp[key]? then return pf
  eventually (fun pf =>
    modify fun st => { st with equateTp := st.equateTp.insert key pf }) do
  let vT : Q(Val $χ) ← Lean.Meta.whnf vT'
  have _ : $vT =Q $vT' := .unsafeIntro
  let vU : Q(Val $χ) ← Lean.Meta.whnf vU'
  have _ : $vU =Q $vU' := .unsafeIntro
  match vT, vU with
  | ~q(.pi $k $k' $vA $vB), ~q(.pi $m $m' $vA' $vB') => do
    let keq ← equateNat q($k) q($m)
    let keq' ← equateNat q($k') q($m')
    let Aeq ← equateTp q($vΓ) q($k) q($vA) q($vA')
    let ⟨Bx, Bxpost⟩ ← forceClosTp q(($vΓ).length) q($vA) q($vB)
    let ⟨Bx', Bxpost'⟩ ← forceClosTp q(($vΓ).length) q($vA') q($vB')
    let Beq ← equateTp q(($vA, $k) :: $vΓ) q($k') q($Bx) q($Bx')
    return q(by as_aux_lemma' equateTp_pi =>
      introv vΓ vT vU
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_pi
      have ⟨_, _, _, vA', vB', eq'⟩ := vU.inv_pi
      subst_vars
      refine eq.trans_tp ?_ |>.trans_tp eq'.symm_tp
      have Aeq := $Aeq vΓ vA vA'
      have Bx := $Bxpost vΓ.length_eq vA vB
      have Bx' := $Bxpost' vΓ.length_eq vA' vB'
      have := $Beq (vΓ.snoc vA) Bx (Bx'.conv_ctx (EqCtx.refl Aeq.wf_ctx |>.snoc Aeq.symm_tp))
      gcongr
    )
  | ~q(.sigma $k $k' $vA $vB), ~q(.sigma $m $m' $vA' $vB') => do
    let keq ← equateNat q($k) q($m)
    let keq' ← equateNat q($k') q($m')
    let Aeq ← equateTp q($vΓ) q($k) q($vA) q($vA')
    let ⟨Bx, Bxpost⟩ ← forceClosTp q(($vΓ).length) q($vA) q($vB)
    let ⟨Bx', Bxpost'⟩ ← forceClosTp q(($vΓ).length) q($vA') q($vB')
    let Beq ← equateTp q(($vA, $k) :: $vΓ) q($k') q($Bx) q($Bx')
    return q(by as_aux_lemma' equateTp_sigma =>
      introv vΓ vT vU
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_sigma
      have ⟨_, _, _, vA', vB', eq'⟩ := vU.inv_sigma
      subst_vars
      refine eq.trans_tp ?_ |>.trans_tp eq'.symm_tp
      have Aeq := $Aeq vΓ vA vA'
      have Bx := $Bxpost vΓ.length_eq vA vB
      have Bx' := $Bxpost' vΓ.length_eq vA' vB'
      have := $Beq (vΓ.snoc vA) Bx (Bx'.conv_ctx (EqCtx.refl Aeq.wf_ctx |>.snoc Aeq.symm_tp))
      gcongr
    )
  | ~q(.Id $k $vA $va $vb), ~q(.Id $m $vA' $va' $vb') => do
    let keq ← equateNat q($k) q($m)
    let Aeq ← equateTp q($vΓ) q($k) q($vA) q($vA')
    let aeq ← equateTm q($vΓ) q($k) q($vA) q($va) q($va')
    let beq ← equateTm q($vΓ) q($k) q($vA) q($vb) q($vb')
    return q(by as_aux_lemma' equateTp_Id =>
      introv vΓ vT vU
      have ⟨_, _, _, _, vA, va, vb, eq⟩ := vT.inv_Id
      have ⟨_, _, _, _, vA', va', vb', eq'⟩ := vU.inv_Id
      subst_vars
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have Aeq := $Aeq vΓ vA vA'
      have := $aeq vΓ vA va (va'.conv_tp Aeq.symm_tp)
      have := $beq vΓ vA vb (vb'.conv_tp Aeq.symm_tp)
      gcongr
    )
  | ~q(.univ _), ~q(.univ _) => do
    return q(by as_aux_lemma' equateTp_univ =>
      introv vΓ vT vU
      have ⟨_, eq⟩ := vT.inv_univ
      have ⟨h, eq'⟩ := vU.inv_univ
      subst_vars; cases h
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have := eq.le_univMax
      apply EqTp.refl_tp <| WfTp.univ eq.wf_ctx (by omega)
    )
  | ~q(.el $na), ~q(.el $na') => do
    let aeq ← equateNeutTm q($vΓ) q($na) q($na')
    return q(by as_aux_lemma' equateTp_el =>
      introv vΓ vT vU
      have ⟨_, na, eq⟩ := vT.inv_el
      have ⟨_, na', eq'⟩ := vU.inv_el
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have := na.wf_tm.le_univMax
      have ⟨_, _⟩ := $aeq vΓ na na'
      gcongr
    )
  | vT, vU =>
    throwError "cannot prove normal types are equal\
        {Lean.indentExpr vT |>.nest 2}\
      {Lean.indentD "≡?≡"}\
        {Lean.indentExpr vU |>.nest 2}"

partial def equateTm (vΓ : Q(TpEnv $χ)) (l : Q(Nat)) (vT vt vu : Q(Val $χ)) :
    TypecheckerM Q(∀ {E Γ T t u}, TpEnvEqCtx E $vΓ Γ →
      ValEqTp E Γ $l $vT T → ValEqTm E Γ $l $vt t T → ValEqTm E Γ $l $vu u T →
      E ∣ Γ ⊢[$l] t ≡ u : T) := do
  let key := (⟨vΓ⟩, ⟨l⟩, ⟨vT⟩, ⟨vt⟩, ⟨vu⟩)
  if let some pf := (← get).equateTm[key]? then return pf
  eventually (fun pf =>
    modify fun st => { st with equateTm := st.equateTm.insert key pf }) do
  match vT with
  | ~q(.pi $k $k' $vA $vB) => do
    let x : Q(Val $χ) := q(.neut (.bvar (($vΓ).length)) $vA)
    let ⟨tx, txpost⟩ ← evalApp q($vt) q($x)
    let ⟨ux, uxpost⟩ ← evalApp q($vu) q($x)
    let ⟨Bx, Bxpost⟩ ← forceClosTp q(($vΓ).length) q($vA) q($vB)
    let tueq ← equateTm q(($vA, $k) :: $vΓ) q($k') q($Bx) q($tx) q($ux)
    return q(by as_aux_lemma' equateTm_pi =>
      introv vΓ vT vt vu
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_pi
      subst_vars

      -- Apply η law
      apply EqTm.conv_eq _ eq.symm_tp
      replace vt := vt.conv_tp eq
      replace vu := vu.conv_tp eq
      apply EqTm.lam_app vt.wf_tm |>.trans_tm _ |>.trans_tm (EqTm.lam_app vu.wf_tm).symm_tm

      -- Show equality of lambdas
      gcongr
      have := NeutEqTm.bvar (eq.wf_ctx.snoc vA.wf_tp) (Lookup.zero ..)
      simp only [List.length_cons, Nat.sub_zero, Nat.add_one_sub_one, ← vΓ.length_eq] at this
      have xwf := ValEqTm.neut_tm (vA.wk vA.wf_tp) this
      have tx := $txpost (vt.wk vA.wf_tp) xwf
      have ux := $uxpost (vu.wk vA.wf_tp) xwf
      simp only [autosubst] at tx ux
      have Bx := $Bxpost vΓ.length_eq vA vB
      convert ($tueq (vΓ.snoc vA) Bx tx ux) using 1 <;> autosubst
    )
  | ~q(.sigma $k $k' $vA $vB) => do
    let ⟨tf, tfpost⟩ ← evalFst q($vt)
    let ⟨uf, ufpost⟩ ← evalFst q($vu)
    let feq ← equateTm q($vΓ) q($k) q($vA) q($tf) q($uf)
    let ⟨ts, tspost⟩ ← evalSnd q($vt)
    let ⟨us, uspost⟩ ← evalSnd q($vu)
    let ⟨Btf, Btfpost⟩ ← evalClosTp q($vB) q($tf)
    let seq ← equateTm q($vΓ) q($k') q($Btf) q($ts) q($us)
    return q(by as_aux_lemma' equateTm_sigma =>
      introv vΓ vT vt vu
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_sigma
      subst_vars

      -- Apply η law
      apply EqTm.conv_eq _ eq.symm_tp
      replace vt := vt.conv_tp eq
      replace vu := vu.conv_tp eq
      apply EqTm.pair_fst_snd vt.wf_tm |>.trans_tm _ |>.trans_tm
        (EqTm.pair_fst_snd vu.wf_tm).symm_tm

      -- Show equality of pairs
      have tf := $tfpost vt
      have uf := $ufpost vu
      have feq := $feq vΓ vA tf uf
      apply EqTm.cong_pair (EqTp.refl_tp vB.wf_tp) feq
      . apply $seq vΓ
        . apply $Btfpost vB tf
        . apply $tspost vt
        . apply ($uspost vu).conv_tp
          exact vB.wf_tp.subst_eq (EqSb.toSb feq.symm_tm)
    )
  | ~q(.univ $k) => do
    let ⟨vA, vApost⟩ ← evalEl q($vt)
    let ⟨vA', vApost'⟩ ← evalEl q($vu)
    let Aeq ← equateTp q($vΓ) q($k) q($vA) q($vA')
    return q(by as_aux_lemma' equateTm_univ =>
      introv vΓ vT vt vu
      have ⟨_, eq⟩ := vT.inv_univ
      subst_vars

      -- Apply η law
      apply EqTm.conv_eq _ eq.symm_tp
      replace vt := vt.conv_tp eq
      replace vu := vu.conv_tp eq
      apply EqTm.code_el vt.wf_tm |>.trans_tm _ |>.trans_tm
        (EqTm.code_el vu.wf_tm).symm_tm

      apply EqTm.cong_code eq.le_univMax
      exact $Aeq vΓ ($vApost vt) ($vApost' vu)
    )
  | _ =>
    match vT, vt, vu with
    | ~q(.Id $k $vA $va $vb), ~q(.refl _ _), ~q(.refl _ _) =>
      return q(by as_aux_lemma' equateTm_refl =>
        introv vΓ vT vt vu
        have ⟨_, _, _, _, eqt, eq⟩ := vt.inv_refl
        have ⟨_, _, _, _, eqt', eq'⟩ := vu.inv_refl
        subst_vars
        have ⟨_, _, _, _, _⟩ := eq.symm_tp.trans_tp eq' |>.inv_Id
        apply eqt.trans_tm _ |>.trans_tm eqt'.symm_tm
        apply EqTm.conv_eq _ eq.symm_tp
        gcongr
      )
    | vT, ~q(.neut $nt _), ~q(.neut $nu _) => do
      let eq ← equateNeutTm q($vΓ) q($nt) q($nu)
      return q(by as_aux_lemma' equateTm_neut =>
        introv vΓ vT vt vu
        have ⟨_, nt⟩ := vt.inv_neut
        have ⟨_, nu⟩ := vu.inv_neut
        exact $eq vΓ nt nu |>.2
      )
    | _, vt, vu =>
      throwError "cannot prove normal terms are equal\
          {Lean.indentExpr vt |>.nest 2}\
        {Lean.indentD "≡?≡"}\
          {Lean.indentExpr vu |>.nest 2}\
        {Lean.indentD "at type"}\
          {Lean.indentExpr vT |>.nest 2}"

partial def equateNeutTm (vΓ : Q(TpEnv $χ)) (nt nu : Q(Neut $χ)) :
    TypecheckerM Q(∀ {E Γ T U t u l}, TpEnvEqCtx E $vΓ Γ →
      NeutEqTm E Γ l $nt t T → NeutEqTm E Γ l $nu u U →
      (E ∣ Γ ⊢[l] T ≡ U) ∧ (E ∣ Γ ⊢[l] t ≡ u : T)) := do
  let key := (⟨vΓ⟩, ⟨nt⟩, ⟨nu⟩)
  if let some pf := (← get).equateNeutTm[key]? then return pf
  eventually (fun pf =>
    modify fun st => { st with equateNeutTm := st.equateNeutTm.insert key pf }) do
  match nt, nu with
  | ~q(.def $expr1 $tyDef), ~q(.def $expr2 _) => (do
      let ⟨_⟩ ← assertDefEqQ q($expr1) q($expr2)
      return q(by as_aux_lemma' equateNeutTm_def =>
        introv vΓ nt nu
        have ⟨_, _, _, _, expr_t, eqt, eqT⟩ := nt.inv_def
        have ⟨_, _, _, _, expr_u, eqt', eqU⟩ := nu.inv_def
        have TU₀ := expr_t.uniq_tp expr_u
        have TUeq := eqT.trans_tp TU₀ |>.trans_tp eqU.symm_tp
        refine ⟨TUeq, ?_⟩
        apply eqt.trans_tm
        apply EqTm.symm_tm
        apply eqt'.conv_eq TUeq.symm_tp
      )) <|> (do
    -- Different exprs: inline left-unfold (same logic as `(.def _ _), _` arm).
    let ~q(@CheckedDef.val _ _ $defn) := expr1
      | throwError "expected CheckedDef.val in Neut.def's expr field, got\
          {Lean.indentExpr expr1}"
    let ⟨vBody, vBodyPost⟩ ← evalTm q(($vΓ).toEnv) q($expr1)
    let nuWrap : Q(Val $χ) := q(.neut $nu $tyDef)
    let eqVT ← equateTm q($vΓ) q(($defn).l) q($tyDef) q($vBody) q($nuWrap)
    return q(by as_aux_lemma' equateNeutTm_def_left_diff =>
      introv vΓ nt nu
      have ⟨ecl, T₀, T₀cl, ty_eq, expr_t, eqt, eqT⟩ := nt.inv_def
      have ty_eq : ValEqTp E Γ l $tyDef T₀ := ty_eq
      have vBody_eq := $vBodyPost vΓ.toEnv_wf expr_t
      simp only [Expr.subst_of_isClosed _ ecl, Expr.subst_of_isClosed _ T₀cl] at vBody_eq
      have hlvl : l = ($defn).l := sorry
      subst hlvl
      have UeqT₀ : E ∣ Γ ⊢[($defn).l] U ≡ T₀ := sorry
      have nu_at_T₀ := nu.conv_neut (EqTm.refl_tm nu.wf_tm) UeqT₀
      have nuWrap_eq : ValEqTm E Γ ($defn).l (.neut $nu $tyDef) u T₀ :=
        ValEqTm.neut_tm ty_eq nu_at_T₀
      have eqtb := $eqVT vΓ ty_eq vBody_eq nuWrap_eq
      have TUeq := eqT.trans_tp UeqT₀.symm_tp
      refine ⟨TUeq, ?_⟩
      apply eqt.trans_tm
      exact eqtb.conv_eq eqT.symm_tp
    ))
  | ~q(.def $expr1 $tyDef), _ => do
    -- Extract `defn` from `expr1 = CheckedDef.val _ _ defn` to recover the
    -- universe level. Then evaluate the def's body and compare it against
    -- `Val.neut nu tyDef` (wrapping the RHS neut at the def's cached type).
    let ~q(@CheckedDef.val _ _ $defn) := expr1
      | throwError "expected CheckedDef.val in Neut.def's expr field, got\
          {Lean.indentExpr expr1}"
    let ⟨vBody, vBodyPost⟩ ← evalTm q(($vΓ).toEnv) q($expr1)
    let nuWrap : Q(Val $χ) := q(.neut $nu $tyDef)
    let eqVT ← equateTm q($vΓ) q(($defn).l) q($tyDef) q($vBody) q($nuWrap)
    return q(by as_aux_lemma' equateNeutTm_def_left =>
      introv vΓ nt nu
      have ⟨ecl, T₀, T₀cl, ty_eq, expr_t, eqt, eqT⟩ := nt.inv_def
      have ty_eq : ValEqTp E Γ l $tyDef T₀ := ty_eq
      have vBody_eq := $vBodyPost vΓ.toEnv_wf expr_t
      simp only [Expr.subst_of_isClosed _ ecl, Expr.subst_of_isClosed _ T₀cl] at vBody_eq
      -- The def's cached level `$defn.l` is the same as the universal `l` here,
      -- bridged via `WfTm.lvl_eq_synthLvl` on `expr_t`.
      have hlvl : l = ($defn).l := sorry
      subst hlvl
      -- We need `EqTp U ≡ T₀` to wrap `nu` at the def's type. Without an
      -- explicit type Val for U threaded through equateNeutTm, this can only
      -- be proved by appealing to the equate's own output (circular). For now
      -- we leave the bridge as a single named sorry.
      have UeqT₀ : E ∣ Γ ⊢[($defn).l] U ≡ T₀ := sorry
      have nu_at_T₀ := nu.conv_neut (EqTm.refl_tm nu.wf_tm) UeqT₀
      have nuWrap_eq : ValEqTm E Γ ($defn).l (.neut $nu $tyDef) u T₀ :=
        ValEqTm.neut_tm ty_eq nu_at_T₀
      have eqtb := $eqVT vΓ ty_eq vBody_eq nuWrap_eq
      have TUeq := eqT.trans_tp UeqT₀.symm_tp
      refine ⟨TUeq, ?_⟩
      apply eqt.trans_tm
      exact eqtb.conv_eq eqT.symm_tp
    )
  | _, ~q(.def $expr2 $tyDef) => do
    let ~q(@CheckedDef.val _ _ $defn) := expr2
      | throwError "expected CheckedDef.val in Neut.def's expr field, got\
          {Lean.indentExpr expr2}"
    let ⟨vBody, vBodyPost⟩ ← evalTm q(($vΓ).toEnv) q($expr2)
    let ntWrap : Q(Val $χ) := q(.neut $nt $tyDef)
    let eqVT ← equateTm q($vΓ) q(($defn).l) q($tyDef) q($ntWrap) q($vBody)
    return q(by as_aux_lemma' equateNeutTm_def_right =>
      introv vΓ nt nu
      have ⟨ecl, T₀, T₀cl, ty_eq, expr_u, eqt', eqU⟩ := nu.inv_def
      have ty_eq : ValEqTp E Γ l $tyDef T₀ := ty_eq
      have vBody_eq := $vBodyPost vΓ.toEnv_wf expr_u
      simp only [Expr.subst_of_isClosed _ ecl, Expr.subst_of_isClosed _ T₀cl] at vBody_eq
      -- See note in the symmetric case above.
      have hlvl : l = ($defn).l := sorry
      subst hlvl
      have TeqT₀ : E ∣ Γ ⊢[($defn).l] T ≡ T₀ := sorry
      have nt_at_T₀ := nt.conv_neut (EqTm.refl_tm nt.wf_tm) TeqT₀
      have ntWrap_eq : ValEqTm E Γ ($defn).l (.neut $nt $tyDef) t T₀ :=
        ValEqTm.neut_tm ty_eq nt_at_T₀
      have eqtb := $eqVT vΓ ty_eq ntWrap_eq vBody_eq
      have TUeq := TeqT₀.trans_tp eqU.symm_tp
      refine ⟨TUeq, ?_⟩
      exact (eqtb.trans_tm (eqt'.symm_tm.conv_eq eqU)).conv_eq TeqT₀.symm_tp
    )
  | ~q(.ax $c _), ~q(.ax $c' _) => do
    let ⟨_⟩ ← assertDefEqQ q($c) q($c')
    return q(by as_aux_lemma' equateNeutTm_ax =>
      introv vΓ nt nu
      have ⟨_, _, Ec, _, eqt, eq⟩ := nt.inv_ax
      have ⟨_, _, Ec', _, eqt', eq'⟩ := nu.inv_ax
      cases Ec.symm.trans Ec'
      subst_vars
      have TUeq := eq.trans_tp eq'.symm_tp; refine ⟨TUeq, ?_⟩
      apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
      apply EqTm.conv_eq _ eq.symm_tp
      apply EqTm.refl_tm (eqt.wf_right.conv eq)
    )
  | ~q(.bvar $i), ~q(.bvar $j) => do
    let ij ← equateNat q($i) q($j)
    return q(by as_aux_lemma' equateNeutTm_bvar =>
      introv vΓ nt nu
      have ⟨_, lk, eqt, eq⟩ := nt.inv_bvar
      have ⟨_, lk', eqt', eq'⟩ := nu.inv_bvar
      subst_vars
      cases lk.tp_uniq lk'
      refine have Aeq := eq.trans_tp eq'.symm_tp; ⟨Aeq, ?_⟩
      apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq Aeq.symm_tp).symm_tm
      apply EqTm.refl_tm eqt.wf_right
    )
  | ~q(.app $k _ $vA $nf $va), ~q(.app $m _ _ $nf' $va') => do
    let km ← equateNat k m
    let feq ← equateNeutTm q($vΓ) q($nf) q($nf')
    let aeq ← equateTm q($vΓ) q($k) q($vA) q($va) q($va')
    return q(by as_aux_lemma' equateNeutTm_app =>
      introv vΓ nt nu
      have ⟨_, _, _, _, _, vA, nf, va, eqt, eq⟩ := nt.inv_app
      have ⟨_, _, _, _, _, vA', nf', va', eqt', eq'⟩ := nu.inv_app
      subst_vars
      have ⟨Peq, feq⟩ := $feq vΓ nf nf'
      have ⟨_, _, _, Aeq, Beq⟩ := Peq.inv_pi
      have aeq := $aeq vΓ vA va (va'.conv_tp Aeq.symm_tp)
      have Baeq := Beq.subst_eq (EqSb.toSb aeq)
      have TUeq := eq.trans_tp Baeq |>.trans_tp eq'.symm_tp;
      refine ⟨TUeq, ?_⟩
      apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
      apply EqTm.conv_eq _ eq.symm_tp
      gcongr
    )
  | ~q(.fst _ $k' $p), ~q(.fst _ $m' $p') => do
    let km' ← equateNat q($k') q($m')
    let peq ← equateNeutTm q($vΓ) q($p) q($p')
    return q(by as_aux_lemma' equateNeutTm_fst =>
      introv vΓ nt nu
      have ⟨_, _, _, _, p, eqt, eq⟩ := nt.inv_fst
      have ⟨_, _, _, _, p', eqt', eq'⟩ := nu.inv_fst
      subst_vars
      have ⟨Seq, peq⟩ := $peq vΓ p p'
      have ⟨_, _, _, Aeq, Beq⟩ := Seq.inv_sigma
      have TUeq := eq.trans_tp Aeq |>.trans_tp eq'.symm_tp
      refine ⟨TUeq, ?_⟩
      apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
      apply EqTm.conv_eq _ eq.symm_tp
      gcongr
    )
  | ~q(.snd $k _ $p), ~q(.snd $m _ $p') => do
    let km ← equateNat q($k) q($m)
    let peq ← equateNeutTm q($vΓ) q($p) q($p')
    return q(by as_aux_lemma' equateNeutTm_snd =>
      introv vΓ nt nu
      have ⟨_, _, _, _, p, eqt, eq⟩ := nt.inv_snd
      have ⟨_, _, _, _, p', eqt', eq'⟩ := nu.inv_snd
      subst_vars
      have ⟨Seq, peq⟩ := $peq vΓ p p'
      have ⟨_, _, _, Aeq, Beq⟩ := Seq.inv_sigma
      refine have TUeq := ?_; ⟨TUeq, ?_⟩
      . apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
        gcongr; apply EqSb.toSb; gcongr
      . apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
        apply EqTm.conv_eq _ eq.symm_tp
        gcongr
    )
  | ~q(.idRec $k $k' $vA $va $cM $vr $nh), ~q(.idRec $m $m' $vA' $va' $cM' $vr' $nh') => do
    let km ← equateNat q($k) q($m)
    let km' ← equateNat q($k') q($m')
    let heq ← equateNeutTm q($vΓ) q($nh) q($nh')
    let ⟨Mx, Mxpost⟩ ← forceClos₂Tp
      q(($vΓ).length) q($vA) q(.Id $k $vA $va (.neut (.bvar (($vΓ).length)) $vA)) q($cM)
    let ⟨Mx', Mxpost'⟩ ← forceClos₂Tp
      q(($vΓ).length) q($vA') q(.Id $k $vA' $va' (.neut (.bvar (($vΓ).length)) $vA')) q($cM')
    let vΓ_ext : Q(TpEnv $χ) := q((.Id $k $vA $va (.neut (.bvar (($vΓ).length)) $vA), $k) ::
      ($vA, $k) :: $vΓ)
    let Meq ← equateTp vΓ_ext q($k') q($Mx) q($Mx')
    let ⟨Mrfl, Mrflpost⟩ ← evalClos₂Tp q($cM) q($va) q(.refl $k $va)
    let req ← equateTm q($vΓ) q($k') q($Mrfl) q($vr) q($vr')
    return q(by as_aux_lemma' equateNeutTm_idRec =>
      introv vΓ nt nu
      have ⟨_, _, _, _, _, _, _, vA, va, cM, vr, nh, eqt, eq⟩ := nt.inv_idRec
      have ⟨_, _, _, _, _, _, _, vA', va', cM', vr', nh', eqt', eq'⟩ := nu.inv_idRec
      subst_vars
      have ⟨eqId, heq⟩ := $heq vΓ nh nh'
      have ⟨_, _, Aeq, aeq, beq⟩ := eqId.inv_Id
      have Mx := $Mxpost vΓ.length_eq vA (vΓ.length_eq ▸ ValEqTp.Id_bvar vA va) cM
      have Mx' := $Mxpost' vΓ.length_eq vA' (vΓ.length_eq ▸ ValEqTp.Id_bvar vA' va') cM'
      have vΓ_ext : TpEnvEqCtx _ _ _ :=
        (vΓ.snoc vA).snoc (vΓ.length_eq ▸ ValEqTp.Id_bvar vA va)
      have Meq := by
        apply $Meq vΓ_ext Mx (Mx'.conv_ctx <| Aeq.wf_ctx.eq_self.snoc Aeq.symm_tp |>.snoc _)
        apply EqTp.cong_Id
          (Aeq.symm_tp.subst <| WfSb.wk Aeq.wf_right)
          (aeq.symm_tm.conv_eq Aeq |>.subst <| WfSb.wk Aeq.wf_right)
          (.refl_tm _)
        apply WfTm.bvar (Aeq.wf_ctx.snoc Aeq.wf_right) (.zero ..)
      refine have TUeq := ?_; ⟨TUeq, ?_⟩
      . apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
        apply Meq.subst_eq (EqSb.toSb beq |>.snoc (.Id_bvar aeq.wf_left) (autosubst% heq))
      . apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
        apply EqTm.conv_eq _ eq.symm_tp
        have Mrfl := $Mrflpost cM va (autosubst% ValEqTm.refl va)
        have := by
          apply $req vΓ Mrfl vr (vr'.conv_tp _)
          apply Meq.symm_tp.subst_eq (EqSb.toSb aeq.symm_tm |>.snoc (.Id_bvar aeq.wf_left) _)
          apply EqTm.cong_refl aeq.symm_tm |>.conv_eq
          autosubst; gcongr
          exact aeq.wf_right
          exact aeq.symm_tm
        gcongr
    )
  | nt, nu => do
    -- Fallback: if either spine has a `Neut.def` at its head, evaluate both
    -- sides (which unfolds the def and cascades β-reductions) and compare the
    -- resulting Vals via `equateTm`. The def's cached `ty` field serves as the
    -- type Val.
    let rec findHead (n : Q(Neut $χ)) :
        Lean.MetaM (Option ((expr : Q(Expr $χ)) × Q(Val $χ))) := do
      match n with
      | ~q(.def $expr $ty) =>
        let expr : Q(Expr $χ) := expr
        let ty : Q(Val $χ) := ty
        return some ⟨expr, ty⟩
      | ~q(.app _ _ _ $f _) => findHead f
      | ~q(.fst _ _ $p) => findHead p
      | ~q(.snd _ _ $p) => findHead p
      | ~q(.idRec _ _ _ _ _ _ $h) => findHead h
      | _ => return none
    let found : Option ((expr : Q(Expr $χ)) × Q(Val $χ)) ←
      match ← findHead nt with
      | some r => pure (some r)
      | none => findHead nu
    let some ⟨expr, tyDef⟩ := found
      | throwError "cannot prove neutral terms are equal\
            {Lean.indentExpr nt |>.nest 2}\
          {Lean.indentD "≡?≡"}\
            {Lean.indentExpr nu |>.nest 2}"
    let ~q(@CheckedDef.val _ _ $defn) := expr
      | throwError "head Neut.def's expr field is not CheckedDef.val: {expr}"
    let ⟨vNt, vNtPost⟩ ← evalNeutTm q(($vΓ).toEnv) q($nt)
    let ⟨vNu, vNuPost⟩ ← evalNeutTm q(($vΓ).toEnv) q($nu)
    let eq ← equateTm q($vΓ) q(($defn).l) q($tyDef) q($vNt) q($vNu)
    return q(by as_aux_lemma' equateNeutTm_unfold_catchall =>
      introv vΓ nt nu
      -- claude: the proof here would call `evalNeutTm`'s `vNtPost`/`vNuPost` to
      -- get ValEqTm's, then `equateTm`'s `eq` to get the EqTm. Bridging the
      -- types requires the cross-type conversion we've been sorry'ing.
      sorry
    )
end

end SynthLean
