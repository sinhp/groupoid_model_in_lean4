import GroupoidModel.Syntax.Typechecker.Evaluate

open Qq

attribute [local grind]
  EqTp.refl_tp EqTp.symm_tp EqTp.trans_tp
  EqTm.refl_tm EqTm.symm_tm EqTm.trans_tm

/-- The two type values are well-formed and equal. -/
abbrev ValEqValTp (Γ : Ctx) (l : Nat) (vT vU : Val) :=
  ∃ T, ValEqTp Γ l vT T ∧ ValEqTp Γ l vU T

theorem ValEqValTp.tp_uniq {Γ l vT vU T U} : ValEqValTp Γ l vT vU →
    ValEqTp Γ l vT T → ValEqTp Γ l vU U → Γ ⊢[l] T ≡ U :=
  fun ⟨_, vT, vU⟩ vT' vU' => vT'.tp_uniq vT |>.trans_tp (vU.tp_uniq vU')

/-- The two term values are well-formed and equal. -/
abbrev ValEqValTm (Γ : Ctx) (l : Nat) (vt vu : Val) (T : Expr) :=
  ∃ t, ValEqTm Γ l vt t T ∧ ValEqTm Γ l vu t T

theorem ValEqValTm.tm_uniq {Γ l vt vu t u T} : ValEqValTm Γ l vt vu T →
    ValEqTm Γ l vt t T → ValEqTm Γ l vu u T → Γ ⊢[l] t ≡ u : T :=
  fun ⟨_, vt, vu⟩ vt' vu' => vt'.tm_uniq vt |>.trans_tm (vu.tm_uniq vu')

/-- The two neutral terms are well-formed and equal. -/
abbrev NeutEqNeutTm (Γ : Ctx) (l : Nat) (nt nu : Neut) :=
  ∃ t T, NeutEqTm Γ l nt t T ∧ NeutEqTm Γ l nu t T

theorem NeutEqNeutTm.tp_uniq {Γ l nt nu t u T U} : NeutEqNeutTm Γ l nt nu →
    NeutEqTm Γ l nt t T → NeutEqTm Γ l nu u U → Γ ⊢[l] T ≡ U :=
  fun ⟨_, _, nt, nu⟩ nt' nu' => nt'.tp_uniq nt |>.trans_tp (nu.tp_uniq nu')

theorem NeutEqNeutTm.tm_uniq {Γ l nt nu t u T U} : NeutEqNeutTm Γ l nt nu →
    NeutEqTm Γ l nt t T → NeutEqTm Γ l nu u U → Γ ⊢[l] t ≡ u : T :=
  fun ⟨_, _, nt, nu⟩ nt' nu' => nt'.tm_uniq nt |>.trans_tm <|
    nu.tm_uniq nu' |>.conv_eq <| nt.tp_uniq nt'

/-- Evaluate a type closure on a fresh variable. -/
def evalClosTp (Γ : Q(Ctx)) (l l' : Q(Nat)) (vA : Q(Val)) (vB : Q(Clos)) (A B : Q(Expr))
    (ΓA : Q(ValEqTp $Γ $l $vA $A))
    (ΓB : Q(ClosEqTp $Γ $l $l' $A $vB $B)) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTp (($A, $l) :: $Γ) $l' $v $B)) := do
  let ~q(.mk_tp $Δ $C $env $B') := vB | throwError "invalid type closure: {vB}"
  let x : Q(Val) := q(.neut (.bvar ($Γ).length) $vA)
  let ex_ : Q(∃ σ, EnvEqSb $Γ $env σ $Δ) :=
    q(by as_aux_lemma =>
      dsimp +zetaDelta only at ($ΓB)
      have ⟨env, _, _⟩ := $ΓB
      exact ⟨_, env⟩
    )
  withHave ex_ fun ex => do
  let ⟨v, veq_⟩ ← evalTp
    q(($A, $l) :: $Γ) q($x :: $env) q(Expr.up ($ex).choose) q(($C, $l) :: $Δ)
    l' B'
    q(by as_aux_lemma =>
      sorry
      -- simp +zetaDelta only [Expr.up_eq_snoc] at ($ΓB) ⊢
      -- have ⟨env, Ceq, B'⟩ := $ΓB
      -- have sbeq := env.sb_uniq ($ex).choose_spec
      -- apply EnvEqSb.snoc (($ex).choose_spec.wk Ceq.wf_right) B'.wf_binder
      -- apply ValEqTm.neut_tm
      -- have := NeutEqTm.bvar (Ceq.wf_ctx.snoc Ceq.wf_right) (Lookup.zero ..)
      -- apply this.conv_tp
      -- have := Ceq.symm_tp.trans_tp <| B'.wf_binder.subst_eq sbeq
      -- convert this.subst (WfSb.wk Ceq.wf_right) using 1
      -- autosubst
    )
    q(by as_aux_lemma =>
      simp +zetaDelta only at ($ΓB)
      have ⟨_, _, B'⟩ := $ΓB
      exact B'
    )
  withHave veq_ fun veq => do
  return ⟨v, ← mkHaves #[ex, veq] q(by as_aux_lemma =>
    simp +zetaDelta only at ($ΓB)
    have ⟨env, Ceq, B'⟩ := $ΓB
    have sbeq := env.sb_uniq ($ex).choose_spec
    have := (B'.subst_eq <| sbeq.up B'.wf_binder).conv_binder Ceq
    apply ($veq).conv_tp this.symm_tp
  )⟩

mutual
partial def equateTp (Γ : Q(Ctx)) (l : Q(Nat)) (vT vU : Q(Val))
    (ΓT : Q(∃ T, ValEqTp $Γ $l $vT T))
    (ΓU : Q(∃ U, ValEqTp $Γ $l $vU U)) :
    Lean.MetaM Q(ValEqValTp $Γ $l $vT $vU) :=
  match vT, vU with
  | ~q(.pi $k $k' $vA $vB), ~q(.pi $m $m' $vA' $vB') => do
    let keq_ ← equateNat k m
    withHave keq_ fun keq => do
    let keq'_ ← equateNat k' m'
    withHave keq'_ fun keq' => do
    let Aeq_ ← equateTp Γ k vA vA'
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := $ΓT
        have ⟨_, _, _, h, _⟩ := ΓT.inv_pi
        /- 2025-07-26: avoiding `grind` for now due to
        https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Bad.20interaction.20of.20Qq.20with.20grind -/
        -- grind
        exact ⟨_, h⟩
      )
      q(by as_aux_lemma =>
        have ⟨_, ΓU⟩ := $ΓU
        have ⟨_, _, _, h, _⟩ := ΓU.inv_pi
        -- grind
        cases ($keq)
        exact ⟨_, h⟩
      )
    withHave Aeq_ fun Aeq => do
    let ex_ : Q(∃ A B B', ClosEqTp $Γ $k $k' A $vB B ∧ ClosEqTp $Γ $k $k' A $vB' B') :=
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
    withHave ex_ fun ex => do
    let A := q(($ex).choose)
    let B := q(($ex).choose_spec.choose)
    let B' := q(($ex).choose_spec.choose_spec.choose)
    let ⟨Bx, Bxeq_⟩ ← evalClosTp Γ k k' vA vB A B
      q(sorry) q(($ex).choose_spec.choose_spec.choose_spec.1)
    withHave Bxeq_ fun Bxeq => do
    let ⟨Bx', Bxeq'_⟩ ← evalClosTp Γ k k' vA vB' A B'
      q(sorry) q(($ex).choose_spec.choose_spec.choose_spec.2)
    withHave Bxeq'_ fun Bxeq' => do
    let Beq_ ← equateTp q((($ex).choose, $k) :: $Γ) k' Bx Bx' q(⟨_, $Bxeq⟩) q(⟨_, $Bxeq'⟩)
    withHave Beq_ fun Beq => do
    mkHaves #[keq, keq', Aeq, ex, Bxeq, Bxeq', Beq] q(by as_aux_lemma =>
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
      have Aeq := ($Aeq).tp_uniq vA vA'
      have Beq := ($Beq).tp_uniq $Bxeq $Bxeq'
      have Beq' := vB.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have Aeq' := vB.binder_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have Beq'' := vB'.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.2
      gcongr
      -- grind [EqTp.conv_binder]
      apply Beq''.trans_tp
      apply Beq.symm_tp.conv_binder Aeq'.symm_tp |>.conv_binder Aeq |>.trans_tp
      apply Beq'.symm_tp.conv_binder Aeq
    )
  | ~q(.sigma $k $k' $vA $vB), ~q(.sigma $m $m' $vA' $vB') => do
    let keq_ ← equateNat k m
    withHave keq_ fun keq => do
    let keq'_ ← equateNat k' m'
    withHave keq'_ fun keq' => do
    let Aeq_ ← equateTp Γ k vA vA'
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := $ΓT
        have ⟨_, _, _, h, _⟩ := ΓT.inv_sigma
        -- grind
        exact ⟨_, h⟩
      )
      q(by as_aux_lemma =>
        have ⟨_, ΓU⟩ := $ΓU
        have ⟨_, _, _, h, _⟩ := ΓU.inv_sigma
        -- grind
        cases ($keq)
        exact ⟨_, h⟩
      )
    withHave Aeq_ fun Aeq => do
    let ex_ : Q(∃ A B B', ClosEqTp $Γ $k $k' A $vB B ∧ ClosEqTp $Γ $k $k' A $vB' B') :=
      q(by as_aux_lemma =>
        have ⟨_, ΓT⟩ := $ΓT
        have ⟨_, ΓU⟩ := $ΓU
        have ⟨_, _, _, A, B, _⟩ := ΓT.inv_sigma
        have ⟨_, _, _, A', B', _⟩ := ΓU.inv_sigma
        have ⟨_, vA, vA'⟩ := $Aeq
        rcases B' with ⟨env, Ceq, B'⟩
        cases ($keq)
        cases ($keq')
        exact ⟨_, _, _, B, ⟨env, Ceq.trans_tp (($Aeq).tp_uniq A A').symm_tp, B'⟩⟩
      )
    withHave ex_ fun ex => do
    let A := q(($ex).choose)
    let B := q(($ex).choose_spec.choose)
    let B' := q(($ex).choose_spec.choose_spec.choose)
    let ⟨Bx, Bxeq_⟩ ← evalClosTp Γ k k' vA vB A B
      q(sorry) q(($ex).choose_spec.choose_spec.choose_spec.1)
    withHave Bxeq_ fun Bxeq => do
    let ⟨Bx', Bxeq'_⟩ ← evalClosTp Γ k k' vA vB' A B'
      q(sorry) q(($ex).choose_spec.choose_spec.choose_spec.2)
    withHave Bxeq'_ fun Bxeq' => do
    let Beq_ ← equateTp q((($ex).choose, $k) :: $Γ) k' Bx Bx' q(⟨_, $Bxeq⟩) q(⟨_, $Bxeq'⟩)
    withHave Beq_ fun Beq => do
    mkHaves #[keq, keq', Aeq, ex, Bxeq, Bxeq', Beq] q(by as_aux_lemma =>
      /- It's not ideal that most of this proof is getting rid of `Exists.choose`s.
      On the other hand, that way we use less runtime data. -/
      have ΓT := ($ΓT).choose_spec
      have ΓU := ($ΓU).choose_spec
      refine ⟨_, ΓT, ΓU.conv_tp ?_⟩
      obtain ⟨rfl, _, _, vA, vB, eq⟩ := ΓT.inv_sigma
      have ⟨_, _, _, vA', vB', eq'⟩ := ΓU.inv_sigma
      cases ($keq)
      cases ($keq')
      refine eq'.trans_tp ?_ |>.trans_tp eq.symm_tp
      have Aeq := ($Aeq).tp_uniq vA vA'
      have Beq := ($Beq).tp_uniq $Bxeq $Bxeq'
      have Beq' := vB.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have Aeq' := vB.binder_uniq ($ex).choose_spec.choose_spec.choose_spec.1
      have Beq'' := vB'.tp_uniq ($ex).choose_spec.choose_spec.choose_spec.2
      gcongr
      -- grind [EqTp.conv_binder]
      apply Beq''.trans_tp
      apply Beq.symm_tp.conv_binder Aeq'.symm_tp |>.conv_binder Aeq |>.trans_tp
      apply Beq'.symm_tp.conv_binder Aeq
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
    let aeq_ ← equateTm Γ q($l + 1) va va' q(.univ $l) q(.univ $l)
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
    withHave aeq_ fun aeq => do
    mkHaves #[aeq] q(by as_aux_lemma =>
      have ⟨_, ΓT⟩ := $ΓT
      have ⟨_, ΓU⟩ := $ΓU
      refine ⟨_, ΓT, ΓU.conv_tp ?_⟩
      have ⟨_, va, eq⟩ := ΓT.inv_el
      have ⟨_, va', eq'⟩ := ΓU.inv_el
      have := EqTp.cong_el <| ($aeq).tm_uniq va va'
      -- grind
      apply eq'.trans_tp this.symm_tp |>.trans_tp eq.symm_tp
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
    let x : Q(Val) := q(.neut (.bvar ($Γ).length) $vA)
    let ex_ : Q(∃ A B, ClosEqTp $Γ $k $k' A $vB B) :=
      q(by as_aux_lemma =>
        have ⟨_, _, _, _, h, _⟩ := ($ΓT).inv_pi
        --grind
        exact ⟨_, _, h⟩
      )
    withHave ex_ fun ex => do
    let A : Q(Expr) := q(($ex).choose)
    let B : Q(Expr) := q(($ex).choose_spec.choose)
    let AΓ : Q(Ctx) := q(($A, $k) :: $Γ)
    let xwf_ : Q(ValEqTm $AΓ $k $x (.bvar 0) (($A).subst Expr.wk)) := q(by as_aux_lemma =>
      sorry
      -- apply ValEqTm.neut_tm
      -- have A := ($ex).choose_spec.choose_spec.wf_tp.wf_binder
      -- exact NeutEqTm.bvar (A.wf_ctx.snoc A) (Lookup.zero ..)
    )
    withHave xwf_ fun xwf => do
    let ⟨tx, txeq_⟩ ← evalApp AΓ k k'
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
      q($xwf)
    withHave txeq_ fun txeq => do
    let ⟨ux, uxeq_⟩ ← evalApp AΓ k k'
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
      q($xwf)
    withHave uxeq_ fun uxeq => do
    let ⟨Bx, Bxeq_⟩ ← evalClosTp Γ k k' vA vB A B
      q(sorry)
      q(by as_aux_lemma => exact ($ex).choose_spec.choose_spec)
    withHave Bxeq_ fun Bxeq => do
    let tueq_ ← equateTm AΓ k' tx ux Bx B q($Bxeq)
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
    withHave tueq_ fun tueq => do
    mkHaves #[ex, xwf, txeq, uxeq, Bxeq, tueq] q(by as_aux_lemma =>
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
    throwError "TODO NF equality at sigma"
  | _ =>
    match vt, vu with
    | ~q(.code $vT), ~q(.code $vU) =>
      -- TODO: add the defeq that makes these neutral.
      throwError "TODO code equality"
    | ~q(.neut $nt _), ~q(.neut $nu _) => do
      let eq_ ← equateNeut Γ l nt nu
        q(sorry)
        -- q(⟨_, _, ($Γt).choose_spec.inv_neut⟩)
        q(sorry)
        -- q(⟨_, _, ($Γu).choose_spec.inv_neut⟩)
      withHave eq_ fun eq => do
      mkHaves #[eq] q(by as_aux_lemma =>
        sorry
        -- have Γt := ($Γt).choose_spec
        -- have Γu := ($Γu).choose_spec
        -- refine ⟨_, Γt, Γu.conv_tm ?_⟩
        -- symm
        -- exact ($eq).tm_uniq Γt.inv_neut Γu.inv_neut
      )
    | _, _ =>
      throwError "unexpected inputs to {Γ} ⊢[{l}] {vt} ≡?≡ {vu} : {vT}"

partial def equateNeut (Γ : Q(Ctx)) (l : Q(Nat)) (nt nu : Q(Neut))
    (Γt : Q(∃ t T, NeutEqTm $Γ $l $nt t T))
    (Γu : Q(∃ u U, NeutEqTm $Γ $l $nu u U)) :
    Lean.MetaM Q(NeutEqNeutTm $Γ $l $nt $nu) :=
  match nt, nu with
  | ~q(.bvar $i), ~q(.bvar $j) => do
    let eq_ ← equateNat i j
    withHave eq_ fun eq => do
    mkHaves #[eq] q(by as_aux_lemma =>
      have ⟨_, _, nt⟩ := $Γt
      have ⟨_, _, nu⟩ := $Γu
      have ⟨_, lk, eqt, eq⟩ := nt.inv_bvar
      have ⟨_, lk', eqt', eq'⟩ := nu.inv_bvar
      cases ($eq)
      cases lk.tp_uniq lk'
      have Aeq := eq'.trans_tp eq.symm_tp
      refine ⟨_, _, nt, nu.conv_neut ?_ Aeq⟩
      apply eqt'.trans_tm (eqt.symm_tm.conv_eq Aeq.symm_tp)
    )
  | ~q(.app $k $k' $vA $nf $va), ~q(.app $m $m' $vA' $nf' $va') => do
    let km_ ← equateNat k m
    withHave km_ fun km => do
    let km'_ ← equateNat k' m'
    withHave km'_ fun km' => do
    let Aeq_ ← equateTp Γ k vA vA' q(sorry) q(sorry)
    withHave Aeq_ fun Aeq => do
    let feq_ ← equateNeut Γ q(max $k $k') nf nf'
      q(by as_aux_lemma =>
        sorry
        -- have ⟨_, _, nf⟩ := $Γt
        -- have ⟨_, _, _, _, _, h, _⟩ := nf.inv_app
        -- exact ⟨_, _, h⟩
      )
      q(by as_aux_lemma =>
        sorry
        -- have ⟨_, _, nf⟩ := $Γu
        -- have ⟨_, _, _, _, _, h, _⟩ := nf.inv_app
        -- cases ($km)
        -- cases ($km')
        -- exact ⟨_, _, h⟩
      )
    withHave feq_ fun feq => do
    let aeq_ ← equateTm Γ k va va' vA q(($Aeq).choose) q(($Aeq).choose_spec.1)
      q(sorry)
      q(sorry)
    withHave aeq_ fun aeq => do
    mkHaves #[km, km', Aeq, feq, aeq] q(sorry)
  | ~q(.fst ..), ~q(.fst ..) =>
    throwError "TODO neutral fst eq"
  | ~q(.snd ..), ~q(.snd ..) =>
    throwError "TODO neutral snd eq"
  | _, _ =>
    throwError "neutral forms are not equal{Lean.indentD ""}{Γ} ⊢[{l}] {nu} ≢ {nt}"
end
