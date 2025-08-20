import GroupoidModel.Syntax.Typechecker.Evaluate

open Qq

variable {_u : Lean.Level} {χ : Q(Type _u)}

mutual
partial def equateTp (d : Q(Nat)) (l : Q(Nat)) (vT vU : Q(Val $χ)) :
    Lean.MetaM Q(∀ {E Γ T U}, [Fact E.Wf] → $d = Γ.length →
      ValEqTp E Γ $l $vT T → ValEqTp E Γ $l $vU U → E ∣ Γ ⊢[$l] T ≡ U) := do
  match vT, vU with
  | ~q(.pi $k $k' $vA $vB), ~q(.pi $m $m' $vA' $vB') => do
    let keq ← equateNat q($k) q($m)
    let keq' ← equateNat q($k') q($m')
    let Aeq ← equateTp q($d) q($k) q($vA) q($vA')
    let ⟨Bx, Bxpost⟩ ← forceClosTp q($d) q($vA) q($vB)
    let ⟨Bx', Bxpost'⟩ ← forceClosTp q($d) q($vA') q($vB')
    let Beq ← equateTp q($d + 1) q($k') q($Bx) q($Bx')
    return q(by as_aux_lemma =>
      introv _ _ vT vU
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
      introv _ _ vT vU
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
  | ~q(.Id $k $vA $va $vb), ~q(.Id $m $vA' $va' $vb') => do
    let keq ← equateNat q($k) q($m)
    let Aeq ← equateTp q($d) q($k) q($vA) q($vA')
    let aeq ← equateTm q($d) q($k) q($vA) q($va) q($va')
    let beq ← equateTm q($d) q($k) q($vA) q($vb) q($vb')
    return q(by as_aux_lemma =>
      introv _ _ vT vU
      have ⟨_, _, _, _, vA, va, vb, eq⟩ := vT.inv_Id
      have ⟨_, _, _, _, vA', va', vb', eq'⟩ := vU.inv_Id
      subst_vars
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have Aeq := $Aeq rfl vA vA'
      have := $aeq rfl vA va (va'.conv_tp Aeq.symm_tp)
      have := $beq rfl vA vb (vb'.conv_tp Aeq.symm_tp)
      gcongr
    )
  | ~q(.univ _), ~q(.univ _) => do
    return q(by as_aux_lemma =>
      introv _ _ vT vU
      have ⟨_, eq⟩ := vT.inv_univ
      have ⟨h, eq'⟩ := vU.inv_univ
      subst_vars; cases h
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have := eq.le_univMax
      apply EqTp.refl_tp <| WfTp.univ eq.wf_ctx (by omega)
    )
  | ~q(.el $na), ~q(.el $na') => do
    let aeq ← equateNeutTm q($d) q($na) q($na')
    return q(by as_aux_lemma =>
      introv _ deq vT vU
      have ⟨_, na, eq⟩ := vT.inv_el
      have ⟨_, na', eq'⟩ := vU.inv_el
      apply eq.trans_tp _ |>.trans_tp eq'.symm_tp
      have := na.wf_tm.le_univMax
      have ⟨_, _⟩ := $aeq deq na na'
      gcongr
    )
  | vT, vU =>
    throwError "cannot prove normal types are equal{Lean.indentExpr vT}\n≡?≡{Lean.indentExpr vU}"

partial def equateTm (d : Q(Nat)) (l : Q(Nat)) (vT vt vu : Q(Val $χ)) :
    Lean.MetaM Q(∀ {E Γ T t u}, [Fact E.Wf] → $d = Γ.length →
      ValEqTp E Γ $l $vT T → ValEqTm E Γ $l $vt t T → ValEqTm E Γ $l $vu u T →
      E ∣ Γ ⊢[$l] t ≡ u : T) := do
  match vT with
  | ~q(.pi _ $k' $vA $vB) => do
    let x : Q(Val $χ) := q(.neut (.bvar $d) $vA)
    let ⟨tx, txpost⟩ ← evalApp q($vt) q($x)
    let ⟨ux, uxpost⟩ ← evalApp q($vu) q($x)
    let ⟨Bx, Bxpost⟩ ← forceClosTp q($d) q($vA) q($vB)
    let tueq ← equateTm q($d + 1) q($k') q($Bx) q($tx) q($ux)
    return q(by as_aux_lemma =>
      introv _ _ vT vt vu
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
      introv _ deq vT vt vu
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
  | ~q(.univ $k) => do
    let ⟨vA, vApost⟩ ← evalEl q($vt)
    let ⟨vA', vApost'⟩ ← evalEl q($vu)
    let Aeq ← equateTp q($d) q($k) q($vA) q($vA')
    return q(by as_aux_lemma =>
      introv _ deq vT vt vu
      have ⟨_, eq⟩ := vT.inv_univ
      subst_vars

      -- Apply η law
      apply EqTm.conv_eq _ eq.symm_tp
      replace vt := vt.conv_tp eq
      replace vu := vu.conv_tp eq
      apply EqTm.code_el vt.wf_tm |>.trans_tm _ |>.trans_tm
        (EqTm.code_el vu.wf_tm).symm_tm

      apply EqTm.cong_code eq.le_univMax
      exact $Aeq rfl ($vApost vt) ($vApost' vu)
    )
  | _ =>
    match vT, vt, vu with
    | vT, ~q(.const $c), ~q(.const $c') =>
      let ⟨_⟩ ← assertDefEqQ q($c) q($c')
      return q(by as_aux_lemma =>
        introv _ deq vT vt vu
        have ⟨_, _, _, eqt, eq⟩ := vt.inv_const
        have ⟨_, _, _, eqt', eq'⟩ := vu.inv_const
        apply eqt.trans_tm _ |>.trans_tm eqt'.symm_tm
        apply EqTm.refl_tm eqt'.wf_right
      )
    | ~q(.Id $k $vA $va $vb), ~q(.refl _ _), ~q(.refl _ _) =>
      return q(by as_aux_lemma =>
        introv _ deq vT vt vu
        have ⟨_, _, _, _, eqt, eq⟩ := vt.inv_refl
        have ⟨_, _, _, _, eqt', eq'⟩ := vu.inv_refl
        subst_vars
        have ⟨_, _, _, _, _⟩ := eq.symm_tp.trans_tp eq' |>.inv_Id
        apply eqt.trans_tm _ |>.trans_tm eqt'.symm_tm
        apply EqTm.conv_eq _ eq.symm_tp
        gcongr
      )
    | vT, ~q(.neut $nt _), ~q(.neut $nu _) => do
      let eq ← equateNeutTm q($d) q($nt) q($nu)
      return q(by as_aux_lemma =>
        introv _ deq vT vt vu
        have ⟨_, nt⟩ := vt.inv_neut
        have ⟨_, nu⟩ := vu.inv_neut
        exact $eq deq nt nu |>.2
      )
    | _, vt, vu =>
      throwError "cannot prove normal terms are equal\
        {Lean.indentExpr vt}\n≡?≡{Lean.indentExpr vu}\n\
        at type\
        {Lean.indentExpr vT}"

partial def equateNeutTm (d : Q(Nat)) (nt nu : Q(Neut $χ)) :
    Lean.MetaM Q(∀ {E Γ T U t u l}, [Fact E.Wf] → $d = Γ.length →
      NeutEqTm E Γ l $nt t T → NeutEqTm E Γ l $nu u U →
      (E ∣ Γ ⊢[l] T ≡ U) ∧ (E ∣ Γ ⊢[l] t ≡ u : T)) :=
  match nt, nu with
  | ~q(.bvar $i), ~q(.bvar $j) => do
    let ij ← equateNat q($i) q($j)
    return q(by as_aux_lemma =>
      introv _ deq nt nu
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
      introv _ _ nt nu
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
      introv _ deq nt nu
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
      introv _ deq nt nu
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
  | ~q(.idRec $k $k' $vA $va $cM $vr $nh), ~q(.idRec $m $m' $vA' $va' $cM' $vr' $nh') => do
    let km ← equateNat q($k) q($m)
    let km' ← equateNat q($k') q($m')
    let heq ← equateNeutTm q($d) q($nh) q($nh')
    let ⟨Mx, Mxpost⟩ ← forceClos₂Tp
      q($d) q($vA) q(.Id $k $vA $va (.neut (.bvar $d) $vA)) q($cM)
    let ⟨Mx', Mxpost'⟩ ← forceClos₂Tp
      q($d) q($vA') q(.Id $k $vA' $va' (.neut (.bvar $d) $vA')) q($cM')
    let Meq ← equateTp q($d + 2) q($k') q($Mx) q($Mx')
    let ⟨Mrfl, Mrflpost⟩ ← evalClos₂Tp q($cM) q($va) q(.refl $k $va)
    let req ← equateTm q($d) q($k') q($Mrfl) q($vr) q($vr')
    return q(by as_aux_lemma =>
      introv _ _ nt nu
      have ⟨_, _, _, _, _, _, _, vA, va, cM, vr, nh, eqt, eq⟩ := nt.inv_idRec
      have ⟨_, _, _, _, _, _, _, vA', va', cM', vr', nh', eqt', eq'⟩ := nu.inv_idRec
      subst_vars
      have ⟨eqId, heq⟩ := $heq rfl nh nh'
      have ⟨_, _, Aeq, aeq, beq⟩ := eqId.inv_Id
      have Mx := $Mxpost rfl vA (.Id_bvar vA va) cM
      have Mx' := $Mxpost' rfl vA' (.Id_bvar vA' va') cM'
      have Meq := by
        apply $Meq rfl Mx (Mx'.conv_ctx <| Aeq.wf_ctx.eq_self.snoc Aeq.symm_tp |>.snoc _)
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
          apply $req rfl Mrfl vr (vr'.conv_tp _)
          apply Meq.symm_tp.subst_eq (EqSb.toSb aeq.symm_tm |>.snoc (.Id_bvar aeq.wf_left) _)
          apply EqTm.cong_refl aeq.symm_tm |>.conv_eq
          autosubst; gcongr
          exact aeq.wf_right
          exact aeq.symm_tm
        gcongr
    )
  | nt, nu =>
    throwError "cannot prove neutral terms are equal{Lean.indentExpr nt}\n≡?≡{Lean.indentExpr nu}"
end
