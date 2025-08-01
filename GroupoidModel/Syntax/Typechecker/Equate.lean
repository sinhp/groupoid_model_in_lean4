import GroupoidModel.Syntax.Typechecker.Evaluate

open Qq

mutual
partial def equateTp (d : Q(Nat)) (l : Q(Nat)) (vT vU : Q(Val)) :
    Lean.MetaM Q(∀ {Γ T U},
      $d = Γ.length → ValEqTp Γ $l $vT T → ValEqTp Γ $l $vU U → Γ ⊢[$l] T ≡ U) := do
  match vT, vU with
  | ~q(.pi $k $k' $vA $vB), ~q(.pi $m $m' $vA' $vB') => do
    let keq ← equateNat q($k) q($m)
    let keq' ← equateNat q($k') q($m')
    let Aeq ← equateTp q($d) q($k) q($vA) q($vA')
    let ⟨Bx, Bxpost⟩ ← forceClosTp q($d) q($vA) q($vB)
    let ⟨Bx', Bxpost'⟩ ← forceClosTp q($d) q($vA') q($vB')
    let Beq ← equateTp q($d + 1) q($k') q($Bx) q($Bx')
    return q(by as_aux_lemma =>
      introv _ vT vU
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_pi
      have ⟨_, _, _, vA', vB', eq'⟩ := vU.inv_pi
      subst_vars
      refine eq.trans_tp ?_ |>.trans_tp eq'.symm_tp
      have Aeq := $Aeq rfl vA vA'
      have Bx := $Bxpost rfl vA vB
      have Bx' := $Bxpost' rfl vA' vB'
      have := $Beq (by simp) Bx (Bx'.conv_ctx (EqCtx.refl Aeq.wf_ctx |>.snoc Aeq.symm_tp))
      gcongr
    )
  | ~q(.sigma $k $k' $vA $vB), ~q(.sigma $m $m' $vA' $vB') => do
    let keq ← equateNat q($k) q($m)
    let keq' ← equateNat q($k') q($m')
    let Aeq ← equateTp q($d) q($k) q($vA) q($vA')
    let ⟨Bx, Bxpost⟩ ← forceClosTp q($d) q($vA) q($vB)
    let ⟨Bx', Bxpost'⟩ ← forceClosTp q($d) q($vA') q($vB')
    let Beq ← equateTp q($d + 1) q($k') q($Bx) q($Bx')
    return q(by as_aux_lemma =>
      introv _ vT vU
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_sigma
      have ⟨_, _, _, vA', vB', eq'⟩ := vU.inv_sigma
      subst_vars
      refine eq.trans_tp ?_ |>.trans_tp eq'.symm_tp
      have Aeq := $Aeq rfl vA vA'
      have Bx := $Bxpost rfl vA vB
      have Bx' := $Bxpost' rfl vA' vB'
      have := $Beq (by simp) Bx (Bx'.conv_ctx (EqCtx.refl Aeq.wf_ctx |>.snoc Aeq.symm_tp))
      gcongr
    )
  | ~q(.univ _), ~q(.univ _) => do
    return q(by as_aux_lemma =>
      introv _ vT vU
      have ⟨_, eq⟩ := vT.inv_univ
      have ⟨h, eq'⟩ := vU.inv_univ
      subst_vars; cases h
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have := eq.le_univMax
      apply EqTp.refl_tp <| WfTp.univ eq.wf_ctx (by omega)
    )
  | ~q(.el $va), ~q(.el $va') => do
    let aeq ← equateTm q($d) q($l + 1) q(.univ $l) q($va) q($va')
    return q(by as_aux_lemma =>
      introv deq vT vU
      have ⟨_, va, eq⟩ := vT.inv_el
      have ⟨_, va', eq'⟩ := vU.inv_el
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have := va.wf_tm.le_univMax
      have := $aeq deq (ValEqTp.univ eq.wf_ctx <| by omega) va va'
      gcongr
    )
  | vT, vU =>
    throwError "cannot prove normal types are equal{Lean.indentExpr vT}\n≡?≡{Lean.indentExpr vU}"

partial def equateTm (d : Q(Nat)) (l : Q(Nat)) (vT vt vu : Q(Val)) : Lean.MetaM Q(∀ {Γ T t u},
    $d = Γ.length → ValEqTp Γ $l $vT T → ValEqTm Γ $l $vt t T → ValEqTm Γ $l $vu u T →
      Γ ⊢[$l] t ≡ u : T) := do
  match vT with
  | ~q(.pi _ $k' $vA $vB) => do
    let x : Q(Val) := q(.neut (.bvar $d) $vA)
    let ⟨tx, txpost⟩ ← evalApp q($vt) q($x)
    let ⟨ux, uxpost⟩ ← evalApp q($vu) q($x)
    let ⟨Bx, Bxpost⟩ ← forceClosTp q($d) q($vA) q($vB)
    let tueq ← equateTm q($d + 1) q($k') q($Bx) q($tx) q($ux)
    return q(by as_aux_lemma =>
      introv _ vT vt vu
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
      simp only [List.length_cons, Nat.sub_zero, Nat.add_one_sub_one] at this
      have xwf := ValEqTm.neut_tm (vA.wk vA.wf_tp) this
      have tx := $txpost (vt.wk vA.wf_tp) xwf
      have ux := $uxpost (vu.wk vA.wf_tp) xwf
      simp only [autosubst] at tx ux
      have Bx := $Bxpost rfl vA vB
      convert ($tueq (by simp) Bx tx ux) using 1 <;> autosubst
    )
  | ~q(.sigma $k $k' $vA $vB) => do
    let ⟨tf, tfpost⟩ ← evalFst q($vt)
    let ⟨uf, ufpost⟩ ← evalFst q($vu)
    let feq ← equateTm q($d) q($k) q($vA) q($tf) q($uf)
    let ⟨ts, tspost⟩ ← evalSnd q($vt)
    let ⟨us, uspost⟩ ← evalSnd q($vu)
    let ⟨Btf, Btfpost⟩ ← evalClosTp q($vB) q($tf)
    let seq ← equateTm q($d) q($k') q($Btf) q($ts) q($us)
    return q(by as_aux_lemma =>
      introv deq vT vt vu
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
      have feq := $feq rfl vA tf uf
      apply EqTm.cong_pair (EqTp.refl_tp vB.wf_tp) feq
      . apply $seq rfl
        . apply $Btfpost vB tf
        . apply $tspost vt
        . apply ($uspost vu).conv_tp
          exact vB.wf_tp.subst_eq (EqSb.toSb feq.symm_tm)
    )
  | _ =>
    match vt, vu with
    -- FIXME: add the defeq that makes these neutral.
    | ~q(.code $vT), ~q(.code $vU) =>
      let ~q(.succ $k) := l | throwError "expected _+1, got{Lean.indentExpr l}"
      let Teq ← equateTp q($d) q($k) q($vT) q($vU)
      return q(by as_aux_lemma =>
        introv deq vT vt vu
        have ⟨_, _, h, vT, eqt, eq⟩ := vt.inv_code
        have ⟨_, _, h', vU, eqt', eq'⟩ := vu.inv_code
        simp +zetaDelta only at h h'
        cases deq; cases h; cases h'
        apply eqt.trans_tm _ |>.trans_tm eqt'.symm_tm
        apply EqTm.conv_eq _ eq.symm_tp
        have := eq.le_univMax
        apply EqTm.cong_code (by omega) <| $Teq rfl vT vU
      )
    | ~q(.neut $nt _), ~q(.neut $nu _) => do
      let eq ← equateNeutTm q($d) q($nt) q($nu)
      return q(by as_aux_lemma =>
        introv deq vT vt vu
        have ⟨_, nt⟩ := vt.inv_neut
        have ⟨_, nu⟩ := vu.inv_neut
        exact $eq deq nt nu |>.2
      )
    | vt, vu =>
      throwError "cannot prove normal terms are equal{Lean.indentExpr vt}\n≡?≡{Lean.indentExpr vu}"

partial def equateNeutTm (d : Q(Nat)) (nt nu : Q(Neut)) : Lean.MetaM Q(∀ {Γ T U t u l},
    $d = Γ.length → NeutEqTm Γ l $nt t T → NeutEqTm Γ l $nu u U →
      (Γ ⊢[l] T ≡ U) ∧ (Γ ⊢[l] t ≡ u : T)) :=
  match nt, nu with
  | ~q(.bvar $i), ~q(.bvar $j) => do
    let ij ← equateNat q($i) q($j)
    return q(by as_aux_lemma =>
      introv deq nt nu
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
    let feq ← equateNeutTm q($d) q($nf) q($nf')
    let aeq ← equateTm q($d) q($k) q($vA) q($va) q($va')
    return q(by as_aux_lemma =>
      introv _ nt nu
      have ⟨_, _, _, _, _, vA, nf, va, eqt, eq⟩ := nt.inv_app
      have ⟨_, _, _, _, _, vA', nf', va', eqt', eq'⟩ := nu.inv_app
      subst_vars
      have ⟨Peq, feq⟩ := $feq rfl nf nf'
      have ⟨_, _, _, Aeq, Beq⟩ := Peq.inv_pi
      have aeq := $aeq rfl vA va (va'.conv_tp Aeq.symm_tp)
      have Baeq := Beq.subst_eq (EqSb.toSb aeq)
      have TUeq := eq.trans_tp Baeq |>.trans_tp eq'.symm_tp;
      refine ⟨TUeq, ?_⟩
      apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
      apply EqTm.conv_eq _ eq.symm_tp
      gcongr
    )
  | ~q(.fst _ $k' $p), ~q(.fst _ $m' $p') => do
    let km' ← equateNat q($k') q($m')
    let peq ← equateNeutTm q($d) q($p) q($p')
    return q(by as_aux_lemma =>
      introv deq nt nu
      have ⟨_, _, _, _, p, eqt, eq⟩ := nt.inv_fst
      have ⟨_, _, _, _, p', eqt', eq'⟩ := nu.inv_fst
      subst_vars
      have ⟨Seq, peq⟩ := $peq rfl p p'
      have ⟨_, _, _, Aeq, Beq⟩ := Seq.inv_sigma
      have TUeq := eq.trans_tp Aeq |>.trans_tp eq'.symm_tp
      refine ⟨TUeq, ?_⟩
      apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
      apply EqTm.conv_eq _ eq.symm_tp
      gcongr
    )
  | ~q(.snd $k _ $p), ~q(.snd $m _ $p') => do
    let km ← equateNat q($k) q($m)
    let peq ← equateNeutTm q($d) q($p) q($p')
    return q(by as_aux_lemma =>
      introv deq nt nu
      have ⟨_, _, _, _, p, eqt, eq⟩ := nt.inv_snd
      have ⟨_, _, _, _, p', eqt', eq'⟩ := nu.inv_snd
      subst_vars
      have ⟨Seq, peq⟩ := $peq rfl p p'
      have ⟨_, _, _, Aeq, Beq⟩ := Seq.inv_sigma
      refine have TUeq := ?_; ⟨TUeq, ?_⟩
      . apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
        gcongr; apply EqSb.toSb; gcongr
      . apply eqt.trans_tm _ |>.trans_tm (eqt'.conv_eq TUeq.symm_tp).symm_tm
        apply EqTm.conv_eq _ eq.symm_tp
        gcongr
    )
  | nt, nu =>
    throwError "cannot prove neutral terms are equal{Lean.indentExpr nt}\n≡?≡{Lean.indentExpr nu}"
end
