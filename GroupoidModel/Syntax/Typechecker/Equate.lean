import GroupoidModel.Syntax.Typechecker.Evaluate

open Qq

attribute [local grind]
  EqTp.refl_tp EqTp.symm_tp EqTp.trans_tp
  EqTm.refl_tm EqTm.symm_tm EqTm.trans_tm

-- macro_rules
--   | `(tactic| as_aux_lemma => $s:tacticSeq) => `(tactic| sorry)
-- set_option linter.unusedTactic false
-- set_option linter.unreachableTactic false
-- set_option debug.skipKernelTC true

partial def equateNat (n m : Q(Nat)) : Lean.MetaM Q($n = $m) :=
  match n, m with
  | ~q(.zero), ~q(.zero) => return q(Eq.refl 0)
  | ~q(.succ $n'), ~q(.succ $m') => do
    let eq ← equateNat n' m'
    return q(congrArg Nat.succ $eq)
  | _, _ => do
    let ⟨(_ : $n =Q $m)⟩ ← assertDefEqQ n m
    return q(Eq.refl $n)

/-- Evaluate a type closure on a fresh variable. -/
def evalClosTp (Γ : Q(Ctx)) (l l' : Q(Nat)) (A B : Q(Expr)) (vB : Q(Clos))
    (ΓB : Q(ClosEqTp $Γ $l $l' $A $vB $B)) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTp (($A, $l) :: $Γ) $l' $v $B)) := do
  let ~q(.mk_tp $Δ $C $env $B') := vB | throwError "invalid type closure: {vB}"
  let x : Q(Val) := q(.neut (.bvar ($Γ).length))
  let ex : Q(∃ σ, EnvEqSb $Γ $env σ $Δ) :=
    q(by as_aux_lemma =>
      dsimp +zetaDelta only at ($ΓB)
      have ⟨env, _, _⟩ := $ΓB
      exact ⟨_, env⟩
    )
  let ⟨v, veq⟩ ← evalTp
    q(($A, $l) :: $Γ) q($x :: $env) q(Expr.up ($ex).choose) q(($C, $l) :: $Δ)
    l' B'
    q(by as_aux_lemma =>
      simp +zetaDelta only [Expr.up_eq_snoc] at ($ΓB) ⊢
      have ⟨env, Ceq, B'⟩ := $ΓB
      have sbeq := env.sb_uniq ($ex).choose_spec
      apply EnvEqSb.snoc (($ex).choose_spec.wk Ceq.wf_right) B'.wf_binder
      apply ValEqTm.neut_tm
      have := NeutEqTm.bvar (Ceq.wf_ctx.snoc Ceq.wf_right) (Lookup.zero ..)
      apply this.conv_tp
      have := Ceq.symm_tp.trans_tp <| B'.wf_binder.subst_eq sbeq
      convert this.subst (WfSb.wk Ceq.wf_right) using 1
      autosubst
    )
    q(by as_aux_lemma =>
      simp +zetaDelta only at ($ΓB)
      have ⟨_, _, B'⟩ := $ΓB
      exact B'
    )
  return ⟨v, q(by as_aux_lemma =>
    simp +zetaDelta only at ($ΓB)
    have ⟨env, Ceq, B'⟩ := $ΓB
    have sbeq := env.sb_uniq ($ex).choose_spec
    have := (B'.subst_eq <| sbeq.up B'.wf_binder).conv_binder Ceq
    apply ($veq).conv_tp this.symm_tp
  )⟩

-- 2025-07-23: attempt to quantify away unnecessary args.
-- 2025-07-25: revised attempt
abbrev ValEqValTp (Γ : Ctx) (l : Nat) (vT vU : Val) :=
  ∃ T, ValEqTp Γ l vT T ∧ ValEqTp Γ l vU T

theorem ValEqValTp.tp_uniq {Γ l vT vU T U} : ValEqValTp Γ l vT vU →
    ValEqTp Γ l vT T → ValEqTp Γ l vU U → Γ ⊢[l] T ≡ U :=
  fun ⟨_, vT, vU⟩ vT' vU' => vT'.tp_uniq vT |>.trans_tp (vU.tp_uniq vU')

abbrev ValEqValTm (Γ : Ctx) (l : Nat) (vt vu : Val) (T : Expr) :=
  ∃ t, ValEqTm Γ l vt t T ∧ ValEqTm Γ l vu t T

theorem ValEqValTm.tm_uniq {Γ l vt vu t u T} : ValEqValTm Γ l vt vu T →
    ValEqTm Γ l vt t T → ValEqTm Γ l vu u T → Γ ⊢[l] t ≡ u : T :=
  fun ⟨_, vt, vu⟩ vt' vu' => vt'.tm_uniq vt |>.trans_tm (vu.tm_uniq vu')

abbrev NeutEqNeutTm (Γ : Ctx) (l : Nat) (nt nu : Neut) :=
  ∃ t T, NeutEqTm Γ l nt t T ∧ NeutEqTm Γ l nu t T

theorem NeutEqNeutTm.tp_uniq {Γ l nt nu t u T U} : NeutEqNeutTm Γ l nt nu →
    NeutEqTm Γ l nt t T → NeutEqTm Γ l nu u U → Γ ⊢[l] T ≡ U :=
  fun ⟨_, _, nt, nu⟩ nt' nu' => nt'.tp_uniq nt |>.trans_tp (nu.tp_uniq nu')

theorem NeutEqNeutTm.tm_uniq {Γ l nt nu t u T U} : NeutEqNeutTm Γ l nt nu →
    NeutEqTm Γ l nt t T → NeutEqTm Γ l nu u U → Γ ⊢[l] t ≡ u : T :=
  fun ⟨_, _, nt, nu⟩ nt' nu' => nt'.tm_uniq nt |>.trans_tm <|
    nu.tm_uniq nu' |>.conv_eq <| nt.tp_uniq nt'

mutual
partial def equateTp (Γ : Q(Ctx)) (l : Q(Nat)) (vT vU : Q(Val))
    (ΓT : Q(∃ T, ValEqTp $Γ $l $vT T))
    (ΓU : Q(∃ U, ValEqTp $Γ $l $vU U)) :
    Lean.MetaM Q(ValEqValTp $Γ $l $vT $vU) :=
  match vT, vU with
  | ~q(.pi $k $k' $vA $vB), ~q(.pi $m $m' $vA' $vB') => do
    let keq ← equateNat k m
    let keq' ← equateNat k' m'
    let Aeq ← equateTp Γ k vA vA'
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := $ΓT
        have := ΓT.inv_pi
        grind
      )
      q(by as_aux_lemma =>
        have ⟨_, ΓU⟩ := $ΓU
        have := ΓU.inv_pi
        grind
      )
    let ex : Q(∃ A B B', ClosEqTp $Γ $k $k' A $vB B ∧ ClosEqTp $Γ $k $k' A $vB' B') :=
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := $ΓT
        have ⟨_, ΓU⟩ := $ΓU
        have ⟨_, _, _, A, B, _⟩ := ΓT.inv_pi
        have ⟨_, _, _, A', B', _⟩ := ΓU.inv_pi
        have ⟨_, vA, vA'⟩ := $Aeq
        rcases B' with ⟨env, Ceq, B'⟩
        cases ($keq)
        cases ($keq')
        exact ⟨_, _, _, B, ⟨env, Ceq.trans_tp (($Aeq).tp_uniq A A').symm_tp, B'⟩⟩
      )
    let ⟨Bx, Bxeq⟩ ← evalClosTp Γ k k'
      q(($ex).choose) q(($ex).choose_spec.choose) vB
      q(($ex).choose_spec.choose_spec.choose_spec.1)
    let ⟨Bx', Bxeq'⟩ ← evalClosTp Γ k k'
      q(($ex).choose) q(($ex).choose_spec.choose_spec.choose) vB'
      q(($ex).choose_spec.choose_spec.choose_spec.2)
    let Beq ← equateTp q((($ex).choose, $k) :: $Γ) k' Bx Bx' q(⟨_, $Bxeq⟩) q(⟨_, $Bxeq'⟩)
    return q(by as_aux_lemma =>
      /- It's not ideal that most of this proof is getting rid of `Exists.choose`s.
      On the other hand, that way we use less runtime data. -/
      have ΓT := ($ΓT).choose_spec
      have ΓU := ($ΓU).choose_spec
      refine ⟨_, ΓT, ΓU.conv_tp ?_⟩
      obtain ⟨rfl, _, _, vA, vB, eq⟩ := ΓT.inv_pi
      have ⟨_, _, _, vA', vB', eq'⟩ := ΓU.inv_pi
      cases ($keq)
      cases ($keq')
      refine eq'.trans_tp ?_ |>.trans_tp eq.symm_tp
      have := ($Aeq).tp_uniq vA vA'
      have := ($Beq).tp_uniq $Bxeq $Bxeq'
      have := vB.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have := vB.binder_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have := vB'.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.2
      gcongr
      grind [EqTp.conv_binder]
    )
  | ~q(.sigma $k $k' $vA $vB), ~q(.sigma $m $m' $vA' $vB') => do
    let keq ← equateNat k m
    let keq' ← equateNat k' m'
    let Aeq ← equateTp Γ k vA vA'
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := $ΓT
        have := ΓT.inv_sigma
        grind
      )
      q(by as_aux_lemma =>
        have ⟨_, ΓU⟩ := $ΓU
        have := ΓU.inv_sigma
        grind
      )
    let ex : Q(∃ A B B', ClosEqTp $Γ $k $k' A $vB B ∧ ClosEqTp $Γ $k $k' A $vB' B') :=
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := $ΓT
        have ⟨_, ΓU⟩ := $ΓU
        have ⟨_, _, _, A, B, _⟩ := ΓT.inv_sigma
        have ⟨_, _, _, A', B', _⟩ := ΓU.inv_sigma
        rcases B' with ⟨env, Ceq, B'⟩
        cases ($keq)
        cases ($keq')
        exact ⟨_, _, _, B, ⟨env, Ceq.trans_tp (($Aeq).tp_uniq A A').symm_tp, B'⟩⟩
      )
    let ⟨Bx, Bxeq⟩ ← evalClosTp Γ k k'
      q(($ex).choose) q(($ex).choose_spec.choose) vB
      q(($ex).choose_spec.choose_spec.choose_spec.1)
    let ⟨Bx', Bxeq'⟩ ← evalClosTp Γ k k'
      q(($ex).choose) q(($ex).choose_spec.choose_spec.choose) vB'
      q(($ex).choose_spec.choose_spec.choose_spec.2)
    let Beq ← equateTp q((($ex).choose, $k) :: $Γ) k' Bx Bx'
      q(⟨_, $Bxeq⟩)
      q(⟨_, $Bxeq'⟩)
    return q(by as_aux_lemma =>
      have ΓT := ($ΓT).choose_spec
      have ΓU := ($ΓU).choose_spec
      refine ⟨_, ΓT, ΓU.conv_tp ?_⟩
      obtain ⟨rfl, _, _, vA, vB, eq⟩ := ΓT.inv_sigma
      have ⟨_, _, _, vA', vB', eq'⟩ := ΓU.inv_sigma
      cases ($keq)
      cases ($keq')
      refine eq'.trans_tp ?_ |>.trans_tp eq.symm_tp
      have := ($Aeq).tp_uniq vA vA'
      have := ($Beq).tp_uniq $Bxeq $Bxeq'
      have := vB.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have := vB.binder_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have := vB'.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.2
      gcongr
      grind [EqTp.conv_binder]
    )
  | ~q(.univ _), ~q(.univ _) => do
    return q(by as_aux_lemma =>
      have ⟨_, ΓT⟩ := $ΓT
      have ⟨_, ΓU⟩ := $ΓU
      refine ⟨_, ΓT, ΓU.conv_tp ?_⟩
      cases ΓT.inv_univ.1
      cases ΓU.inv_univ.1
      apply ΓU.tp_uniq ΓT
    )
  | ~q(.el $va), ~q(.el $va') => do
    let aeq ← equateTm Γ q($l + 1) va va' q(.univ $l) q(.univ $l)
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := ($ΓT)
        have ⟨_, va, _⟩ := ΓT.inv_el
        have a := va.wf_tm
        apply ValEqTp.univ a.wf_ctx a.le_univMax
      )
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := ($ΓT)
        have ⟨_, va, _⟩ := ΓT.inv_el
        exact ⟨_, va⟩
      )
      q(by as_aux_lemma =>
        have ⟨_, ΓU⟩ := ($ΓU)
        have ⟨_, va, _⟩ := ΓU.inv_el
        exact ⟨_, va⟩
      )
    return q(by as_aux_lemma =>
      have ⟨_, ΓT⟩ := $ΓT
      have ⟨_, ΓU⟩ := $ΓU
      refine ⟨_, ΓT, ΓU.conv_tp ?_⟩
      have ⟨_, va, eq⟩ := ΓT.inv_el
      have ⟨_, va', eq'⟩ := ΓU.inv_el
      have := EqTp.cong_el <| ($aeq).tm_uniq va va'
      grind
    )
  | _, _ =>
    throwError "unexpected inputs to {Γ} ⊢[{l}] {vT} ≡?≡ {vU}"

partial def equateTm (Γ : Q(Ctx)) (l : Q(Nat)) (vt vu vT : Q(Val)) (T : Q(Expr))
    (ΓT : Q(ValEqTp $Γ $l $vT $T))
    (Γt : Q(∃ t, ValEqTm $Γ $l $vt t $T))
    (Γu : Q(∃ u, ValEqTm $Γ $l $vu u $T)) :
    Lean.MetaM Q(ValEqValTm $Γ $l $vt $vu $T) :=
  match vT with
  | ~q(.pi $k $k' $vA $vB) => do
    let x : Q(Val) := q(.neut (.bvar ($Γ).length))
    let ex : Q(∃ A B, ClosEqTp $Γ $k $k' A $vB B) :=
      q(by as_aux_lemma => have := ($ΓT).inv_pi; grind)
    let A : Q(Expr) := q(($ex).choose)
    let B : Q(Expr) := q(($ex).choose_spec.choose)
    let AΓ : Q(Ctx) := q(($A, $k) :: $Γ)
    let ⟨tx, txeq⟩ ← evalApp AΓ k k'
      q(($A).subst Expr.wk) q(($B).subst (Expr.up Expr.wk))
      vt x q(($Γt).choose.subst Expr.wk) q(.bvar 0)
      q(by as_aux_lemma =>
        obtain ⟨rfl, _, _, vA, vB, eq⟩ := ($ΓT).inv_pi
        have ⟨_, Γt⟩ := $Γt
        have Aeq := vB.binder_uniq ($ex).choose_spec.choose_spec
        have Beq := vB.tp_uniq ($ex).choose_spec.choose_spec
        have A := Aeq.wf_right
        apply Γt.wk A |>.conv_nf
        . exact Γt.tm_uniq ($Γt).choose_spec |>.subst <| WfSb.wk A
        . apply eq.subst (WfSb.wk A) |>.trans_tp
          simp only [Expr.subst]
          have := Aeq.subst (WfSb.wk A)
          have := WfSb.wk A |>.up Aeq.wf_left
          gcongr; assumption
      )
      q(by as_aux_lemma =>
        apply ValEqTm.neut_tm
        have A := ($ex).choose_spec.choose_spec.wf_tp.wf_binder
        exact NeutEqTm.bvar (A.wf_ctx.snoc A) (Lookup.zero ..)
      )
    let ⟨ux, uxeq⟩ ← evalApp AΓ k k'
      q(($A).subst Expr.wk) q(($B).subst (Expr.up Expr.wk))
      vu x q(($Γu).choose.subst Expr.wk) q(.bvar 0)
      q(by as_aux_lemma =>
        obtain ⟨rfl, _, _, vA, vB, eq⟩ := ($ΓT).inv_pi
        have ⟨_, Γu⟩ := $Γu
        have Aeq := vB.binder_uniq ($ex).choose_spec.choose_spec
        have Beq := vB.tp_uniq ($ex).choose_spec.choose_spec
        have A := Aeq.wf_right
        apply Γu.wk A |>.conv_nf
        . exact Γu.tm_uniq ($Γu).choose_spec |>.subst <| WfSb.wk A
        . apply eq.subst (WfSb.wk A) |>.trans_tp
          simp only [Expr.subst]
          have := Aeq.subst (WfSb.wk A)
          have := WfSb.wk A |>.up Aeq.wf_left
          gcongr; assumption
      )
      q(by as_aux_lemma =>
        apply ValEqTm.neut_tm
        have := ($ex).choose_spec.choose_spec
        have A := this.wf_tp.wf_binder
        exact NeutEqTm.bvar (A.wf_ctx.snoc A) (Lookup.zero ..)
      )
    let ⟨Bx, Bxeq⟩ ← evalClosTp Γ k k' A B vB
      q(by as_aux_lemma => exact ($ex).choose_spec.choose_spec)
    let tueq ← equateTm AΓ k' tx ux Bx B q($Bxeq)
      q(by as_aux_lemma =>
        refine ⟨_, ($txeq).conv_tp ?_⟩
        convert EqTp.refl_tp ($ex).choose_spec.choose_spec.wf_tp using 1
        autosubst
      )
      q(by as_aux_lemma =>
        refine ⟨_, ($uxeq).conv_tp ?_⟩
        convert EqTp.refl_tp ($ex).choose_spec.choose_spec.wf_tp using 1
        autosubst
      )
    return q(by as_aux_lemma =>
      have Γt := ($Γt).choose_spec
      have Γu := ($Γu).choose_spec
      obtain ⟨rfl, _, _, vA, vB, eq⟩ := ($ΓT).inv_pi
      have := ($ex).choose_spec.choose_spec
      have Aeq := this.binder_uniq vB
      have Beq := this.tp_uniq vB
      have peq := eq.trans_tp <| (EqTp.cong_pi Aeq Beq).symm_tp
      refine ⟨_, Γt, Γu.conv_tm (EqTm.conv_eq ?_ peq.symm_tp)⟩
      apply EqTm.lam_app (Γu.wf_tm.conv peq) |>.trans_tm _ |>.trans_tm <|
        EqTm.lam_app (Γt.wf_tm.conv peq) |>.symm_tm
      gcongr
      simp only [autosubst] at ($txeq) ($uxeq)
      symm; convert ($tueq).tm_uniq $txeq $uxeq using 1 <;> autosubst
    )
  | ~q(.sigma $k $k' $vA $vB) => do
    throwError "TODO implement: {Γ} ⊢[{l}] {vt} ≡?≡ {vu} : {vT}"
  | _ =>
    match vt, vu with
    | ~q(.code $vT), ~q(.code $vU) =>
      -- FIXME: add the defeq that makes these neutral.
      throwError "TODO implement: {Γ} ⊢[{l}] {vt} ≡?≡ {vu} : {vT}"
    | ~q(.neut $nt), ~q(.neut $nu) => do
      let eq ← equateNeut Γ l nt nu
        q(⟨_, _, ($Γt).choose_spec.inv_neut⟩)
        q(⟨_, _, ($Γu).choose_spec.inv_neut⟩)
      return q(by as_aux_lemma =>
        have Γt := ($Γt).choose_spec
        have Γu := ($Γu).choose_spec
        refine ⟨_, Γt, Γu.conv_tm ?_⟩
        symm
        exact ($eq).tm_uniq Γt.inv_neut Γu.inv_neut
      )
    | _, _ =>
      throwError "unexpected inputs to {Γ} ⊢[{l}] {vt} ≡?≡ {vu} : {vT}"

partial def equateNeut (Γ : Q(Ctx)) (l : Q(Nat)) (nt nu : Q(Neut))
    (Γt : Q(∃ t T, NeutEqTm $Γ $l $nt t T))
    (Γu : Q(∃ u U, NeutEqTm $Γ $l $nu u U)) :
    Lean.MetaM Q(NeutEqNeutTm $Γ $l $nt $nu) :=
  match nt, nu with
  | _, _ => throwError "TODO implement: {Γ} ⊢[{l}] {nt} ≡?≡ₙₑᵤₜ {nu}"
end
