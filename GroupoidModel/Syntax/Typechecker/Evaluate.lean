import Qq

import GroupoidModel.Syntax.Synth
import GroupoidModel.Syntax.Typechecker.Value
import GroupoidModel.Syntax.Typechecker.Util

open Qq

/-! ## Evaluation -/

mutual
/-- Evaluate a type in an environment of values.

Note: Inferring implicits from `Q(...)` is pretty flaky,
so all the arguments are explicit.

Note: we use `as_aux_lemma` pervasively to minimize the size of produced proof terms.
See also `withHave`. -/
-- FIXME: by using `synthLvl`, we could also get rid of the `l` args in `eval*`.
partial def evalTp (Δ : Q(Ctx)) (env : Q(List Val)) (σ : Q(Nat → Expr)) (Γ : Q(Ctx))
    (l : Q(Nat)) (T' : Q(Expr))
    (Δenv : Q(EnvEqSb $Δ $env $σ $Γ))
    (ΓT : Q($Γ ⊢[$l] ($T'))) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTp $Δ $l $v <| ($T').subst $σ)) := do
  /- TODO: establish a convention for when inputs are supposed to be in WHNF.
  Should `evalTp` reject types not in WHNF?
  Then we'd need to evaluate them in `lookup`,
  and other places where compound quotations are produced.
  On the other hand, lazy evaluation may be more efficient. -/
  let T : Q(Expr) ← Lean.Meta.whnf T'
  have _ : $T =Q $T' := .unsafeIntro
  match T with
  | ~q(.pi $l $l' $A $B) => do
    let ⟨vA, vAeq_⟩ ← evalTp Δ env σ Γ l A
      q($Δenv)
      q(by as_aux_lemma => exact ($ΓT).inv_pi.2.wf_binder)
    withHave vAeq_ fun vAeq => do
    let vT : Q(Val) := q(.pi $l $l' $vA (.mk_tp $Γ $A $env $B))
    return ⟨vT, ← mkHaves #[vAeq] q(by as_aux_lemma =>
      obtain ⟨rfl, B⟩ := ($ΓT).inv_pi
      apply ValEqTp.pi $vAeq
      apply ClosEqTp.clos_tp $Δenv (EqTp.refl_tp ($vAeq).wf_tp) B
    )⟩
  | ~q(.sigma $l $l' $A $B) => do
    let ⟨vA, vAeq_⟩ ← evalTp Δ env σ Γ l A
      q($Δenv)
      q(by as_aux_lemma => exact ($ΓT).inv_sigma.2.wf_binder)
    withHave vAeq_ fun vAeq => do
    let vT : Q(Val) := q(.sigma $l $l' $vA (.mk_tp $Γ $A $env $B))
    return ⟨vT, ← mkHaves #[vAeq] q(by as_aux_lemma =>
      obtain ⟨rfl, B⟩ := ($ΓT).inv_sigma
      apply ValEqTp.sigma $vAeq
      apply ClosEqTp.clos_tp $Δenv (EqTp.refl_tp ($vAeq).wf_tp) B
    )⟩
  | ~q(.el $a) => do
    let ⟨va, vaeq_⟩ ← evalTm Δ env σ Γ q($l + 1) a
      q($Δenv)
      q(by as_aux_lemma => exact ($ΓT).inv_el.with_synthTp)
    withHave vaeq_ fun vaeq => do
    let vT : Q(Val) := q(.el $va)
    return ⟨vT, ← mkHaves #[vaeq] q(by as_aux_lemma =>
      apply ValEqTp.el <| ($vaeq).conv_tp _
      exact ($ΓT).inv_el.tp_eq_synthTp.symm_tp.subst ($Δenv).wf_sb
    )⟩
  | ~q(.univ $l) =>
    let vT : Q(Val) := q(.univ $l)
    return ⟨vT, q(by as_aux_lemma =>
      cases ($ΓT).inv_univ
      apply ValEqTp.univ ($Δenv).wf_dom
      have := ($ΓT).le_univMax
      omega
    )⟩
  | A => throwError "{A} is not a type"

/-- Evaluate a term in an environment of values. -/
partial def evalTm (Δ : Q(Ctx)) (env : Q(List Val)) (σ : Q(Nat → Expr)) (Γ : Q(Ctx))
    (l : Q(Nat)) (t' : Q(Expr))
    (Δenv : Q(EnvEqSb $Δ $env $σ $Γ))
    (Γt : Q($Γ ⊢[$l] ($t') : synthTp $Γ $t')) :
    Lean.MetaM ((v : Q(Val)) ×
      Q(ValEqTm $Δ $l $v (($t').subst $σ) ((synthTp $Γ $t').subst $σ))) := do
  -- TODO: see comment at `evalTp`.
  let t : Q(Expr) ← Lean.Meta.whnf t'
  have _ : $t =Q $t' := .unsafeIntro
  match t with
  | ~q(.bvar $i) => do
    let v : Q(Option Val) := q($env[$i]?)
    /- We evaluate the list access and error if a concrete element doesn't pop out.
    We do this (instead of producing e.g. `q($env[$i]? |>.getD default)`)
    because the evaluator may inspect the syntactic form of this value later,
    and it being `Option.getD ..` would lead to hard-to-debug errors. -/
    let v : Q(Option Val) ← Lean.Meta.whnf v
    have pf : $v =Q $env[$i]? := .unsafeIntro -- FIXME: `whnfQ`?
    let ~q(some $v') := v | throwError "expected 'some _', got{Lean.indentExpr v}"
    return ⟨v', q(by as_aux_lemma =>
      simp +zetaDelta only [Expr.subst]
      have ⟨_, lk, eq⟩ := ($Γt).inv_bvar
      apply ValEqTm.conv_tp _ (eq.subst ($Δenv).wf_sb).symm_tp
      . convert ($Δenv).lookup_eq lk using 1
        -- grind -- solves this, but results in `unknown metavariable`
        subst $v
        rename_i h
        have ⟨_, h⟩ := List.getElem?_eq_some_iff.mp h
        rw [h]
    )⟩
  | ~q(.lam $k $k' $C $b) => do
    return ⟨q(.lam $k $k' (.mk_tm $Γ $C $env $b)),
      q(by as_aux_lemma =>
        simp +zetaDelta only [Expr.subst, synthTp]
        obtain ⟨rfl, B, b, eq⟩ := ($Γt).inv_lam
        have C := b.wf_binder
        apply ValEqTm.lam <| ClosEqTm.clos_tm (B := B) $Δenv _ _ b
        . exact EqTp.refl_tp <| C.subst ($Δenv).wf_sb
        . exact b.tp_eq_synthTp.subst (($Δenv).wf_sb.up C)
      )⟩
  | ~q(.app $k $k' $B $f $a) => do
    let ⟨vf, vfeq_⟩ ← evalTm Δ env σ Γ q(max $k $k') f
      q($Δenv)
      q(by as_aux_lemma =>
        have ⟨_, _, f, _⟩ := ($Γt).inv_app
        exact f.with_synthTp
      )
    withHave vfeq_ fun vfeq => do
    let ⟨va, vaeq_⟩ ← evalTm Δ env σ Γ k a
      q($Δenv)
      q(by as_aux_lemma =>
        have ⟨_, _, _, a, _⟩ := ($Γt).inv_app
        exact a.with_synthTp
      )
    withHave vaeq_ fun vaeq => do
    let ⟨v, veq_⟩ ←
      evalApp Δ k k'
        q((synthTp $Γ $a).subst $σ)
        q(($B).subst (Expr.up $σ))
        vf va q(($f).subst $σ) q(($a).subst $σ)
        q(by as_aux_lemma =>
          apply ($vfeq).conv_tp
          have ⟨_, _, f, a, _⟩ := ($Γt).inv_app
          have ⟨_, B⟩ := f.wf_tp.inv_pi
          apply f.tp_eq_synthTp.subst ($Δenv).wf_sb |>.symm_tp.trans_tp _
          simp only [Expr.subst]
          have := a.tp_eq_synthTp.subst ($Δenv).wf_sb
          gcongr
          exact B.subst (($Δenv).wf_sb.up B.wf_binder)
        )
        q($vaeq)
    withHave veq_ fun veq => do
    return ⟨v, ← mkHaves #[vfeq, vaeq, veq] q(by as_aux_lemma =>
      obtain ⟨rfl, _, _, _, eq⟩ := ($Γt).inv_app
      replace eq := eq.subst ($Δenv).wf_sb
      simp +zetaDelta only [Expr.subst] at eq ⊢
      apply ($veq).conv_tp
      convert eq.symm_tp using 1
      autosubst
    )⟩
  | ~q(.pair $k $k' $B $t $u) => do
    let ⟨vt, vteq_⟩ ← evalTm Δ env σ Γ k t q($Δenv)
      q(by as_aux_lemma =>
        have ⟨_, _, t, _⟩ := ($Γt).inv_pair
        exact t.with_synthTp)
    withHave vteq_ fun vteq => do
    let ⟨vu, vueq_⟩ ← evalTm Δ env σ Γ k' u q($Δenv)
      q(by as_aux_lemma =>
        have ⟨_, _, _, u, _⟩ := ($Γt).inv_pair
        exact u.with_synthTp)
    withHave vueq_ fun vueq => do
    let vp := q(.pair $k $k' $vt $vu)
    return ⟨vp, ← mkHaves #[vteq, vueq] q(by as_aux_lemma =>
      simp +zetaDelta only [synthTp, Expr.subst] at ($Γt) ⊢
      obtain ⟨rfl, _, _, u, _⟩ := ($Γt).inv_pair
      have ⟨_, B⟩ := ($Γt).wf_tp.inv_sigma
      have := B.subst (($Δenv).wf_sb.up B.wf_binder)
      apply ValEqTm.pair this $vteq
      apply ($vueq).conv_tp
      have := u.tp_eq_synthTp.subst ($Δenv).wf_sb
      convert this.symm_tp using 1; autosubst
    )⟩
  | ~q(.fst $k $k' $A $B $p) => do
    let ⟨vp, vpeq_⟩ ← evalTm Δ env σ Γ q(max $k $k') p
      q($Δenv)
      q(by as_aux_lemma => exact ($Γt).inv_fst.2.1.with_synthTp)
    withHave vpeq_ fun vpeq => do
    let ⟨v, veq_⟩ ←
      evalFst Δ k k' q(($A).subst $σ) q(($B).subst (Expr.up $σ)) vp q(($p).subst $σ)
        q(by as_aux_lemma =>
          apply ($vpeq).conv_tp
          have ⟨_, p, _⟩ := ($Γt).inv_fst
          have := p.tp_eq_synthTp.subst ($Δenv).wf_sb
          apply this.symm_tp
        )
    withHave veq_ fun veq => do
    return ⟨v, ← mkHaves #[vpeq, veq] q(by as_aux_lemma =>
      simp +zetaDelta only [Expr.subst]
      obtain ⟨rfl, p, eq⟩ := ($Γt).inv_fst
      apply ($veq).conv_tp (eq.subst ($Δenv).wf_sb).symm_tp
    )⟩
  | ~q(.snd $k $k' $A $B $p) => do
    let ⟨vp, vpeq_⟩ ← evalTm Δ env σ Γ q(max $k $k') p
      q($Δenv)
      q(by as_aux_lemma => exact ($Γt).inv_snd.2.1.with_synthTp)
    withHave vpeq_ fun vpeq => do
    let ⟨v, veq_⟩ ←
      evalSnd Δ k k' q(($A).subst $σ) q(($B).subst (Expr.up $σ)) vp q(($p).subst $σ)
        q(by as_aux_lemma =>
          apply ($vpeq).conv_tp
          have ⟨_, p, _⟩ := ($Γt).inv_snd
          have := p.tp_eq_synthTp.subst ($Δenv).wf_sb
          apply this.symm_tp
        )
    withHave veq_ fun veq => do
    return ⟨v, ← mkHaves #[vpeq, veq] q(by as_aux_lemma =>
      simp +zetaDelta only [Expr.subst]
      obtain ⟨rfl, p, eq⟩ := ($Γt).inv_snd
      apply ($veq).conv_tp
      convert eq.subst ($Δenv).wf_sb |>.symm_tp using 1
      autosubst
    )⟩
  | ~q(.code $A) => do
    let ⟨vA, vAeq_⟩ ← evalTp Δ env σ Γ q($l - 1) A
      q($Δenv)
      q(by as_aux_lemma => obtain ⟨_, rfl, h, _⟩ := ($Γt).inv_code; exact h)
    withHave vAeq_ fun vAeq => do
    let vc : Q(Val) := q(.code $vA)
    return ⟨vc, ← mkHaves #[vAeq] q(by as_aux_lemma =>
      simp +zetaDelta only [Expr.subst]
      obtain ⟨l, rfl, _, Teq⟩ := ($Γt).inv_code
      have := ($Γt).le_univMax
      have := Teq.subst ($Δenv).wf_sb
      apply ValEqTm.conv_tp _ this.symm_tp
      apply ValEqTm.code (by omega) $vAeq
    )⟩
  | t => throwError "{t} is not a term"

-- FIXME: `A` could be replaced by `synthTp Δ a`
partial def evalApp (Δ : Q(Ctx)) (l l' : Q(Nat)) (A B : Q(Expr))
    (vf va : Q(Val)) (f a : Q(Expr))
    (Δf : Q(ValEqTm $Δ (max $l $l') $vf $f (.pi $l $l' $A $B)))
    (Δa : Q(ValEqTm $Δ $l $va $a $A)) :
    Lean.MetaM ((v : Q(Val)) ×
      Q(ValEqTm $Δ $l' $v (.app $l $l' $B $f $a) (($B).subst ($a).toSb))) :=
  match vf with
  | ~q(.lam $k $k' (.mk_tm $Γ $A' $env $b)) => do
    /- To evaluate the closure in its environment `env`,
    we need to provide a substitution `σ` with `EnvEqSb Δ env σ Γ`;
    but such a substitution is difficult to construct
    because `Val`s do not contain type annotations whereas `Expr`s do
    (see now-removed `sbOfEnv`).
    We also cannot store it in `Clos.mk_tm`
    because that would make weakening non-free on values.
    Instead, we obtain one using AC;
    the choice is unique (up to `EqSb`)
    since `EnvEqSb` is functional.
    Noncomputability is not a problem
    because the evaluator never destructs substitutions
    (only environments). -/
    -- TODO: document convention on which args must be computable.
    let ex_ : Q(∃ σ, EnvEqSb $Δ $env σ $Γ) :=
      q(by as_aux_lemma =>
        have ⟨_, _, _, _, c, _⟩ := ($Δf).inv_lam
        rcases c with ⟨env, _⟩
        exact ⟨_, env⟩
      )
    withHave ex_ fun ex => do
    let ⟨v, veq_⟩ ← evalTm Δ q($va :: $env)
      q(Expr.snoc ($ex).choose $a) q(($A', $k) :: $Γ) k' b
      q(by as_aux_lemma =>
        have ⟨_, _, _, _, c, eqt, eq⟩ := ($Δf).inv_lam
        rcases c with ⟨env, Aeq', _, b⟩
        obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_pi
        have A' := b.wf_binder
        apply EnvEqSb.snoc ($ex).choose_spec A'
        apply ($Δa).conv_tp <| Aeq.trans_tp <| Aeq'.symm_tp.trans_tp <| A'.subst_eq _
        exact env.sb_uniq ($ex).choose_spec
      )
      q(by as_aux_lemma =>
        have ⟨_, _, _, _, c, eqt, eq⟩ := ($Δf).inv_lam
        rcases c with ⟨_, _, _, b⟩
        exact b.with_synthTp
      )
    withHave veq_ fun veq => do
    return ⟨v, ← mkHaves #[ex, veq] q(by as_aux_lemma =>
      have ⟨_, _, _, _, c, eqt, eq⟩ := ($Δf).inv_lam
      rcases c with ⟨env, Aeq', Beq', b⟩
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_pi
      clear eq
      have sbeq := env.sb_uniq ($ex).choose_spec
      replace sbeq := sbeq.snoc b.wf_binder <| EqTm.refl_tm <| ($Δa).wf_tm.conv <|
        Aeq.trans_tp Aeq'.symm_tp
      have := b.tp_eq_synthTp.subst_eq sbeq
      replace ($veq) := ($veq).conv_nf ((b.subst_eq sbeq).conv_eq this).symm_tm this.symm_tp
      replace Beq' := Beq'.conv_binder Aeq.symm_tp
      have := Beq'.trans_tp Beq.symm_tp |>.subst (WfSb.toSb ($Δa).wf_tm)
      simp only [autosubst] at ($veq) this ⊢
      apply ($veq).conv_nf _ this
      apply EqTm.conv_eq _ this.symm_tp
      replace b := b.subst (env.wf_sb.up b.wf_binder)
        |>.conv_binder (Aeq'.trans_tp Aeq.symm_tp)
        |>.conv (Beq'.trans_tp Beq.symm_tp)
      have := EqTm.app_lam b ($Δa).wf_tm |>.symm_tm
      simp only [autosubst] at this
      apply this.trans_tm
      apply EqTm.cong_app (EqTp.refl_tp Beq.wf_left) _ (EqTm.refl_tm ($Δa).wf_tm)
      apply EqTm.trans_tm _ eqt.symm_tm
      gcongr
      autosubst
      convert EqTm.refl_tm b using 1 <;> autosubst
    )⟩
  | ~q(.neut $n (.pi $k $k' $vA (.mk_tp $Γ $A $env $B))) => do
    let ⟨vBa, vBaeq_⟩ ← evalTp Δ q($va :: $env) q(sorry) q(($A, $k) :: $Γ) k' B
      q(sorry)
      q(sorry)
    withHave vBaeq_ fun vBaeq => do
    let na : Q(Val) := q(.neut (.app $l $l' $vA $n $va) $vBa)
    return ⟨na, ← mkHaves #[vBaeq] q(by as_aux_lemma =>
      sorry
      -- exact ValEqTm.neut_tm <| NeutEqTm.app sorry ($Δf).inv_neut $Δa
    )⟩
  | _ => throwError "unexpected normal form {vf} at type Π"

partial def evalFst (Δ : Q(Ctx)) (l l' : Q(Nat)) (A B : Q(Expr))
    (vp : Q(Val)) (p : Q(Expr))
    (Δp : Q(ValEqTm $Δ (max $l $l') $vp $p (.sigma $l $l' $A $B))) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTm $Δ $l $v (.fst $l $l' $A $B $p) $A)) :=
  match vp with
  | ~q(.pair _ _ $v _) =>
    return ⟨v, q(by as_aux_lemma =>
      have ⟨_, A', B', f, s, v, _, eqt, eq⟩ := ($Δp).inv_pair
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
      have : $Δ ⊢[$l] f ≡ Expr.fst $l $l' $A $B $p : $A := by
        have ⟨_, A'', t, u, eq'⟩ := eqt.wf_right.inv_pair
        have ⟨_, _, _, Aeq', Beq'⟩ := eq'.inv_sigma
        replace t := t.conv Aeq'.symm_tp
        replace u := u.conv <| Beq'.symm_tp.subst (WfSb.toSb t)
        apply EqTm.fst_pair Beq.wf_left t u |>.symm_tm.trans_tm
        gcongr
        apply EqTm.trans_tm _ eqt.symm_tm
        gcongr <;> assumption
      apply v.conv_nf (this.conv_eq Aeq) Aeq.symm_tp
    )⟩
  | ~q(.neut $n (.sigma $k $k' $vA $vB)) =>
    return ⟨q(.neut (.fst $l $l' $n) $vA), q(by as_aux_lemma =>
      sorry
      -- exact ValEqTm.neut_tm <| NeutEqTm.fst ($Δp).inv_neut
    )⟩
  | _ => throwError "unexpected normal form {vp} at type Σ"

partial def evalSnd (Δ : Q(Ctx)) (l l' : Q(Nat)) (A B : Q(Expr))
    (vp : Q(Val)) (p : Q(Expr))
    (Δp : Q(ValEqTm $Δ (max $l $l') $vp $p (.sigma $l $l' $A $B))) :
    Lean.MetaM ((v : Q(Val)) ×
      Q(ValEqTm $Δ $l' $v (.snd $l $l' $A $B $p) <| ($B).subst (Expr.fst $l $l' $A $B $p).toSb)) :=
  match vp with
  | ~q(.pair _ _ _ $w) =>
    return ⟨w, q(by as_aux_lemma =>
      have ⟨_, A', B', f, s, _, w, eqt, eq⟩ := ($Δp).inv_pair
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
      have ⟨_, A'', t, u, eq'⟩ := eqt.wf_right.inv_pair
      have ⟨_, _, _, Aeq', Beq'⟩ := eq'.inv_sigma
      replace t := t.conv Aeq'.symm_tp
      replace u := u.conv <| Beq'.symm_tp.subst (WfSb.toSb t)
      have feq : $Δ ⊢[$l] f ≡ Expr.fst $l $l' $A $B $p : $A := by
        apply EqTm.fst_pair Beq.wf_left t u |>.symm_tm.trans_tm
        gcongr
        apply EqTm.trans_tm _ eqt.symm_tm
        gcongr <;> assumption
      replace w := w.conv_tp <| Beq.symm_tp.subst_eq (EqSb.toSb feq)
      apply w.conv_nf _ (EqTp.refl_tp w.wf_tm.wf_tp)
      apply EqTm.snd_pair Beq.wf_left t u |>.symm_tm.conv_eq
        (Beq'.wf_left.subst_eq (EqSb.toSb feq)) |>.trans_tm _
      symm; gcongr
      apply eqt.trans_tm
      symm; gcongr <;> assumption
    )⟩
  | ~q(.neut $n (.sigma $k $k' $vA (.mk_tp $Γ $A $env $B))) => do
    let ⟨vf, vfeq_⟩ ← evalFst Δ l l' A B vp p Δp
    withHave vfeq_ fun vfeq => do
    let ⟨vBfst, vBfsteq_⟩ ← evalTp Δ q($vf :: $env) q(sorry) q(($A, $k) :: $Γ) k' B
      q(sorry)
      q(sorry)
    withHave vBfsteq_ fun vBfsteq => do
    let n : Q(Val) := q(.neut (.snd $l $l' $n) $vBfst)
    return ⟨n, ← mkHaves #[vfeq, vBfsteq] q(by as_aux_lemma =>
      sorry
      -- exact ValEqTm.neut_tm <| NeutEqTm.snd ($Δp).inv_neut
    )⟩
  | _ => throwError "unexpected normal form {vp} at type Σ"

end

/-- Evaluate a type closure on a fresh variable. -/
def evalClosTp (Γ : Q(Ctx)) (l l' : Q(Nat)) (vA : Q(Val)) (vB : Q(Clos)) (A B : Q(Expr))
    (ΓA : Q(ValEqTp $Γ $l $vA $A))
    (ΓB : Q(ClosEqTp $Γ $l $l' $A $vB $B)) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTp (($A, $l) :: $Γ) $l' $v $B)) := do
  let ~q(.mk_tp $Δ _ $env $B') := vB | throwError "invalid type closure: {vB}"
  let x : Q(Val) := q(.neut (.bvar ($Γ).length) $vA)
  let ex_ : Q(∃ σ, EnvEqSb $Γ $env σ $Δ) :=
    q(by as_aux_lemma =>
      dsimp +zetaDelta only at ($ΓB)
      have ⟨env, _, _⟩ := $ΓB
      exact ⟨_, env⟩
    )
  withHave ex_ fun ex => do
  let ⟨v, veq_⟩ ← evalTp
    -- 2027-07-30: Noncomputational use of `C`, can remove using inversion :)
    q(($A, $l) :: $Γ) q($x :: $env) q(Expr.up ($ex).choose) q((sorry, $l) :: $Δ)
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
      sorry
      --exact B'
    )
  withHave veq_ fun veq => do
  return ⟨v, ← mkHaves #[ex, veq] q(by as_aux_lemma =>
    simp +zetaDelta only at ($ΓB)
    have ⟨env, Ceq, B'⟩ := $ΓB
    have sbeq := env.sb_uniq ($ex).choose_spec
    have := (B'.subst_eq <| sbeq.up B'.wf_binder).conv_binder Ceq
    apply ($veq).conv_tp this.symm_tp
  )⟩

def evalTp' (vΓ : Q(TpEnv)) (Γ : Q(Ctx)) (l : Q(Nat)) (T : Q(Expr))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) (ΓT : Q($Γ ⊢[$l] ($T))) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTp $Γ $l $v $T)) := do
  -- TODO: WHNF `envOfTpEnv`? I think not; it will need WHNFing later anyway
  -- (WHNF doesn't eval the args). Lean essentially forces us to lazily WHNF.
  let ⟨vT, vTeq_⟩ ← evalTp Γ q(envOfTpEnv $vΓ) q(Expr.bvar) Γ l T q(envOfTpEnv_wf $vΓwf) q($ΓT)
  withHave vTeq_ fun vTeq => do
  return ⟨vT, ← mkHaves #[vTeq] q(by as_aux_lemma =>
    convert ($vTeq) using 1; autosubst
  )⟩

def evalTm' (vΓ : Q(TpEnv)) (Γ : Q(Ctx)) (l : Q(Nat)) (t : Q(Expr))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) (Γt : Q($Γ ⊢[$l] ($t) : synthTp $Γ $t)) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTm $Γ $l $v $t (synthTp $Γ $t))) := do
  -- TODO: WHNF `envOfTpEnv`?
  let ⟨vt, vteq_⟩ ← evalTm Γ q(envOfTpEnv $vΓ) q(Expr.bvar) Γ l t q(envOfTpEnv_wf $vΓwf) q($Γt)
  withHave vteq_ fun vteq => do
  return ⟨vt, ← mkHaves #[vteq] q(by as_aux_lemma =>
    convert ($vteq) using 1 <;> autosubst
  )⟩
