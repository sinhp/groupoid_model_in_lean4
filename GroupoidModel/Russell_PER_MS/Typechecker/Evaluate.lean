import Qq

import GroupoidModel.Russell_PER_MS.GCongr
import GroupoidModel.Russell_PER_MS.Synth
import GroupoidModel.Russell_PER_MS.Injectivity
import GroupoidModel.Russell_PER_MS.Typechecker.Value

/-- Shorthand for `List.length` which is used a lot in this file. -/
local notation "‖" l "‖" => List.length l

-- /-- Hacks to use during development:
-- `as_aux_lemma` blocks are not elaborated and kernel typechecking is off,
-- speeding up interactive feedback. -/
-- FIXME: make `as_aux_lemma` or general `by` elaboration async for lower interaction latency.
-- macro_rules
--   | `(tactic| as_aux_lemma => $s:tacticSeq) => `(tactic| sorry)
-- set_option linter.unusedTactic false
-- set_option linter.unreachableTactic false
-- set_option debug.skipKernelTC true

open Qq

/-! ## Evaluation -/

mutual
/-- Evaluate a type in an environment of values.

Note: Inferring implicits from `Q(...)` is pretty flaky,
so all the arguments are explicit.

Note: returning `Q(⋯ ∧ ⋯)` rather than `Q(⋯) × Q(⋯)`
makes it easier to reuse proofs between the postconditions.

Note: we use `as_aux_lemma` pervasively to minimize the size of produced proof terms. -/
-- FIXME: by using `synthLvl`, we could also get rid of the `l` args in `eval*`.
partial def evalTp (Δ : Ctx) (env : List Val) (Γ : Ctx) (l : Nat) (T : Expr)
    (Δenv : Q(WfEnv $Δ $env $Γ))
    (ΓT : Q($Γ ⊢[$l] ($T))) :
    Except String ((v : Val) ×
      Q(WfValTp $Δ $l $v ∧
        ($Δ ⊢[$l] ($v).toExpr ‖$Δ‖ ≡ ($T).subst (sbOfEnv ‖$Δ‖ $env)))) :=
  match T with
  | .pi l l' A B => do
    let ⟨vA, vApfs⟩ ← evalTp Δ env Γ l A q($Δenv) q(($ΓT).inv_pi.2.wf_ctx.inv_snoc)
    return ⟨.pi l l' vA (.mk_tp Γ A env B),
      q(by as_aux_lemma =>
        have ⟨vAwf, vAeq⟩ := $vApfs
        obtain ⟨rfl, B⟩ := ($ΓT).inv_pi
        constructor
        . apply WfValTp.pi vAwf
          exact WfClosTp.clos_tp vAeq.symm_tp $Δenv B
        . simp only [Val.toExpr, Clos.toExpr, Expr.subst]
          gcongr
          exact B.subst (WfSb.up ($Δenv).wf_sbOfEnv B.wf_ctx.inv_snoc) |>.conv_ctx
            (EqCtx.refl vAeq.wf_ctx |>.snoc vAeq.symm_tp)
      )⟩
  | .sigma l l' A B => do
    let ⟨vA, vApfs⟩ ← evalTp Δ env Γ l A q($Δenv) q(($ΓT).inv_sigma.2.wf_ctx.inv_snoc)
    return ⟨.sigma l l' vA (.mk_tp Γ A env B),
      q(by as_aux_lemma =>
        have ⟨vAwf, vAeq⟩ := $vApfs
        obtain ⟨rfl, B⟩ := ($ΓT).inv_sigma
        constructor
        . apply WfValTp.sigma vAwf
          exact WfClosTp.clos_tp vAeq.symm_tp $Δenv B
        . simp only [Val.toExpr, Clos.toExpr, Expr.subst]
          gcongr
          exact B.subst (WfSb.up ($Δenv).wf_sbOfEnv B.wf_ctx.inv_snoc) |>.conv_ctx
            (EqCtx.refl vAeq.wf_ctx |>.snoc vAeq.symm_tp)
      )⟩
  | .el a => do
    let ⟨va, vapfs⟩ ← evalTm Δ env Γ (l + 1) a q($Δenv) q(($ΓT).inv_el.with_synthTp)
    return ⟨.el va,
      q(by as_aux_lemma =>
        have ⟨vawf, vaeq⟩ := $vapfs
        have := ($ΓT).inv_el.tp_eq_synthTp.symm_tp.subst ($Δenv).wf_sbOfEnv
        simp only [Expr.subst, Val.toExpr] at this ⊢
        exact ⟨WfValTp.el <| vawf.conv_nf this, EqTp.cong_el <| vaeq.conv_eq this⟩
      )⟩
  | .univ l => return ⟨.univ l,
      q(by as_aux_lemma =>
        cases ($ΓT).inv_univ
        have Δ := ($Δenv).wf_sbOfEnv.wf_dom
        have : $l < univMax := have := ($ΓT).le_univMax; by omega
        simp only [Expr.subst, Val.toExpr]
        exact ⟨WfValTp.univ Δ this, EqTp.refl_tp <| WfTp.univ Δ this⟩
      )⟩
  | A => throw s!"{repr A} is not a type"

/-- Evaluate a term in an environment of values. -/
partial def evalTm (Δ : Ctx) (env : List Val) (Γ : Ctx) (l : Nat) (t : Expr)
    (Δenv : Q(WfEnv $Δ $env $Γ))
    (Γt : Q($Γ ⊢[$l] ($t) : synthTp $Γ $t)) :
    Except String ((v : Val) ×
      /- Potential simplification: see docstring on `Val`. -/
      Q(WfValTm $Δ $l $v (synthTp $Γ $t |>.subst (sbOfEnv ‖$Δ‖ $env)) ∧
        ($Δ ⊢[$l] ($v).toExpr ‖$Δ‖ ≡ ($t).subst (sbOfEnv ‖$Δ‖ $env) :
          (synthTp $Γ $t |>.subst (sbOfEnv ‖$Δ‖ $env))))) :=
  match t with
  | .bvar i => do
    return ⟨env[i]?.getD default,
      q(by as_aux_lemma =>
        have ⟨_, lk, eq⟩ := ($Γt).inv_bvar
        simp only [getElem?_pos, ($Δenv).lookup_lt lk, Option.getD_some, Expr.subst,
          ($Δenv).sbOfEnv_app lk]
        have iwf := ($Δenv).lookup_wf lk
        have Δeq := eq.symm_tp.subst ($Δenv).wf_sbOfEnv
        exact ⟨iwf.conv_nf Δeq, EqTm.refl_tm <| iwf.wf_toExpr.conv Δeq⟩
      )⟩
  | .lam k k' C b => do
    return ⟨.lam k k' (C.subst (sbOfEnv ‖Δ‖ env)) (.mk_tm Γ C env b),
      q(by as_aux_lemma =>
        obtain ⟨rfl, D, b, ACD⟩ := ($Γt).inv_lam
        simp only [synthTp, Expr.subst, Val.toExpr, Clos.toExpr] at ACD ⊢
        have Δb := (b.subst <| ($Δenv).wf_sbOfEnv.up b.wf_ctx.inv_snoc)
        constructor
        . obtain ⟨_, _, _, _, sbD⟩ := ACD.inv_pi
          apply WfValTm.lam <| WfClosTm.clos_tm
            (EqTp.refl_tp Δb.wf_ctx.inv_snoc)
            (sbD.symm_tp.subst <| ($Δenv).wf_sbOfEnv.up b.wf_ctx.inv_snoc)
            $Δenv
            b
        . apply EqTm.conv_eq (EqTm.refl_tm _) (ACD.subst ($Δenv).wf_sbOfEnv).symm_tp
          apply WfTm.lam Δb
      )⟩
  | .app k k' B f a => do
    let ⟨vf, vfpfs⟩ ← evalTm Δ env Γ (max k k') f
      q($Δenv)
      q(by as_aux_lemma =>
        obtain ⟨_, _, f, _⟩ := ($Γt).inv_app
        apply f.conv f.tp_eq_synthTp
      )
    let ⟨va, vapfs⟩ ← evalTm Δ env Γ k a
      q($Δenv)
      q(by as_aux_lemma =>
        obtain ⟨_, _, _, a, _⟩ := ($Γt).inv_app
        apply a.conv a.tp_eq_synthTp
      )
    let ⟨v, vpfs⟩ ←
      evalApp Δ k k'
        (synthTp Γ a |>.subst (sbOfEnv ‖Δ‖ env))
        (B.subst (Expr.up (sbOfEnv ‖Δ‖ env)))
        vf
        va
        q(by as_aux_lemma =>
          obtain ⟨_, _, f, a, eq⟩ := ($Γt).inv_app
          have := EqTp.cong_pi a.tp_eq_synthTp (EqTp.refl_tp f.wf_tp.inv_pi.2)
            |>.symm_tp.trans_tp f.tp_eq_synthTp
          apply ($vfpfs).1.conv_nf (this.subst ($Δenv).wf_sbOfEnv).symm_tp
        )
        q(($vapfs).1)
    return ⟨v,
      q(by as_aux_lemma =>
        have ⟨vfwf, vfeq⟩ := $vfpfs
        have ⟨vawf, vaeq⟩ := $vapfs
        have ⟨vwf, veq⟩ := $vpfs
        obtain ⟨rfl, _, f, a, _⟩ := ($Γt).inv_app
        simp only [synthTp, Expr.subst]
        have BvaBa : $Δ ⊢[$l]
            (($B).subst (Expr.up (sbOfEnv ‖$Δ‖ $env))).subst (($va).toExpr ‖$Δ‖).toSb ≡
            (($B).subst ($a).toSb).subst (sbOfEnv ‖$Δ‖ $env) := by
          have ΓB := f.wf_tp.inv_pi.2.conv_binder a.tp_eq_synthTp
          have ΔB := ΓB.subst <| ($Δenv).wf_sbOfEnv.up ΓB.wf_ctx.inv_snoc
          convert ΔB.subst_eq <| EqSb.toSb vaeq using 1; autosubst
        constructor
        . exact (vwf).conv_nf BvaBa
        . apply (veq).trans_tm _ |>.conv_eq BvaBa
          have sfeq := f.tp_eq_synthTp.subst ($Δenv).wf_sbOfEnv
          have saeq := a.tp_eq_synthTp.subst ($Δenv).wf_sbOfEnv
          simp only [Expr.subst] at sfeq saeq
          have B := f.wf_tp.inv_pi.2
          apply EqTm.cong_app
            (EqTp.refl_tp <| B.subst <| ($Δenv).wf_sbOfEnv.up B.wf_ctx.inv_snoc)
            (vfeq.conv_eq sfeq.symm_tp)
            (vaeq.conv_eq saeq.symm_tp)
      )⟩
  | .pair k k' B t u => do
    let ⟨vt, vtpfs⟩ ← evalTm Δ env Γ k t q($Δenv) q(($Γt).inv_pair.2.2.1.with_synthTp)
    let ⟨vu, vupfs⟩ ← evalTm Δ env Γ k' u q($Δenv) q(($Γt).inv_pair.2.2.2.1.with_synthTp)
    return ⟨.pair k k' (B.subst <| Expr.up <| sbOfEnv ‖Δ‖ env) vt vu,
      q(by as_aux_lemma =>
        have ⟨vtwf, vteq⟩ := $vtpfs
        have ⟨vuwf, vueq⟩ := $vupfs
        simp only [synthTp, Expr.subst, Val.toExpr] at ($Γt) ⊢
        obtain ⟨rfl, _, t, u, eq⟩ := ($Γt).inv_pair
        have ⟨_, B⟩ := eq.wf_left.inv_sigma
        have ΔB := B.subst <| ($Δenv).wf_sbOfEnv.up B.wf_ctx.inv_snoc
        have suenv : $Δ ⊢[$k'] (synthTp $Γ $u).subst (sbOfEnv ‖$Δ‖ $env) ≡
            (($B).subst (Expr.up (sbOfEnv ‖$Δ‖ $env)) |>.subst (($vt).toExpr ‖$Δ‖).toSb) := by
          apply u.tp_eq_synthTp.subst ($Δenv).wf_sbOfEnv |>.symm_tp.trans_tp
          autosubst
          apply B.subst_eq <| ($Δenv).wf_sbOfEnv.eq_self.snoc t.with_synthTp.wf_tp (vteq).symm_tm
        constructor
        . apply WfValTm.pair ΔB vtwf ((vuwf).conv_nf suenv)
        . apply EqTm.cong_pair (EqTp.refl_tp ΔB) vteq ((vueq).conv_eq suenv)
      )⟩
  | .fst l l' A B p => do
    let ⟨vp, vppfs⟩ ← evalTm Δ env Γ (max l l') p
      q($Δenv)
      q(($Γt).inv_fst.2.1.with_synthTp)
    let ⟨v, vpfs⟩ ←
      evalFst Δ l l' (A.subst (sbOfEnv ‖Δ‖ env)) (B.subst (Expr.up (sbOfEnv ‖Δ‖ env))) vp
        q(by as_aux_lemma =>
          have ⟨_, p, eq⟩ := ($Γt).inv_fst
          have := p.tp_eq_synthTp.subst ($Δenv).wf_sbOfEnv
          simp only [Expr.subst] at this
          exact ($vppfs).1.conv_nf this.symm_tp
        )
    return ⟨v,
      q(by as_aux_lemma =>
        have ⟨_, vpeq⟩ := $vppfs
        have ⟨vwf, veq⟩ := $vpfs
        obtain ⟨rfl, p, _⟩ := ($Γt).inv_fst
        constructor
        . convert vwf using 1; simp [synthTp]
        . have eq := p.tp_eq_synthTp.subst ($Δenv).wf_sbOfEnv
          simp only [Expr.subst, synthTp] at eq ⊢
          apply veq.trans_tm
          gcongr
          apply vpeq.conv_eq eq.symm_tp
      )⟩
  | .snd k k' A B p => do
    let ⟨vp, vppfs⟩ ← evalTm Δ env Γ (max k k') p
      q($Δenv)
      q(($Γt).inv_snd.2.1.with_synthTp)
    let ⟨v, vpfs⟩ ←
      evalSnd Δ k k' (A.subst (sbOfEnv ‖Δ‖ env)) (B.subst (Expr.up (sbOfEnv ‖Δ‖ env))) vp
        q(by as_aux_lemma =>
          have ⟨_, p, eq⟩ := ($Γt).inv_snd
          have := p.tp_eq_synthTp.subst ($Δenv).wf_sbOfEnv
          simp only [Expr.subst] at this
          exact ($vppfs).1.conv_nf this.symm_tp
        )
    return ⟨v,
      q(by as_aux_lemma =>
        have ⟨_, vpeq⟩ := $vppfs
        have ⟨vwf, veq⟩ := $vpfs
        obtain ⟨rfl, p, _⟩ := ($Γt).inv_snd
        have B := p.wf_tp.inv_sigma.2
        have speq := p.tp_eq_synthTp.subst ($Δenv).wf_sbOfEnv
        simp only [synthTp, Expr.subst] at speq ⊢
        have bigEq : $Δ ⊢[$l]
              (($B).subst (Expr.up (sbOfEnv ‖$Δ‖ $env)) |>.subst
                (Expr.fst $k $l
                  (($A).subst (sbOfEnv ‖$Δ‖ $env))
                  (($B).subst (Expr.up (sbOfEnv ‖$Δ‖ $env)))
                  (($vp).toExpr ‖$Δ‖)).toSb) ≡
              (($B).subst (Expr.fst $k $l $A $B $p).toSb |>.subst (sbOfEnv ‖$Δ‖ $env)) := by
          autosubst
          apply B.subst_eq <| ($Δenv).wf_sbOfEnv.eq_self.snoc B.wf_ctx.inv_snoc _
          gcongr
          convert vpeq.conv_eq speq.symm_tp using 1; autosubst
        constructor
        . apply vwf.conv_nf bigEq
        . apply EqTm.conv_eq _ bigEq
          apply veq.trans_tm
          gcongr
          apply vpeq.conv_eq speq.symm_tp
      )⟩
  | .code A => do
    let ⟨vA, vApfs⟩ ← evalTp Δ env Γ (l - 1) A
      q($Δenv)
      q(by as_aux_lemma => obtain ⟨_, rfl, h, _⟩ := ($Γt).inv_code; exact h
      )
    return ⟨.code vA,
      q(by as_aux_lemma =>
        have ⟨vAwf, vAeq⟩ := $vApfs
        simp only [Val.toExpr, Expr.subst, synthTp]
        obtain ⟨_, rfl, A, _⟩ := ($Γt).inv_code
        have := ($Γt).le_univMax
        cases A.lvl_eq_synthLvl
        exact ⟨WfValTm.code (by omega) vAwf, EqTm.cong_code (by omega) vAeq⟩
      )⟩
  | t => throw s!"{repr t} is not a term"

-- FIXME: `A` could be replaced by `synthTp Δ a`
partial def evalApp (Δ : Ctx) (l l' : Nat) (A B : Expr) (f a : Val)
    (Δf : Q(WfValTm $Δ (max $l $l') $f (.pi $l $l' $A $B)))
    (Δa : Q(WfValTm $Δ $l $a $A)) :
    Except String ((v : Val) ×
      Q(WfValTm $Δ $l' $v (($B).subst (($a).toExpr ‖$Δ‖).toSb) ∧
        ($Δ ⊢[$l'] ($v).toExpr ‖$Δ‖ ≡
          .app $l $l' $B (($f).toExpr ‖$Δ‖) (($a).toExpr ‖$Δ‖) :
          (($B).subst (($a).toExpr ‖$Δ‖).toSb)))) :=
  match f with
  | .lam m m' _ (.mk_tm Γ A' env b) => do
    let ⟨v, vpfs⟩ ← evalTm Δ (a :: env) ((A', m) :: Γ) m' b
      q(by as_aux_lemma =>
        have ⟨_, B, b, eq⟩ := ($Δf).inv_lam
        rcases b with ⟨A'env, _, env, b⟩
        obtain ⟨_, rfl, rfl, Aeq, _⟩ := eq.inv_pi
        apply env.snoc b.wf_ctx.inv_snoc (($Δa).conv_nf <| Aeq.trans_tp A'env.symm_tp)
      )
      q(by as_aux_lemma =>
        have ⟨_, B, b, eq⟩ := ($Δf).inv_lam
        rcases b with ⟨A'env, _, env, b⟩
        exact b.with_synthTp
      )
    return ⟨v,
      q(by as_aux_lemma =>
        have ⟨vwf, veq⟩ := $vpfs
        have ⟨_, B, b, eq⟩ := ($Δf).inv_lam
        rcases b with ⟨A'env, Benv, env, b⟩
        obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_pi
        have bigEq : $Δ ⊢[$l'] (synthTp (($A', $l) :: $Γ) $b).subst (sbOfEnv ‖$Δ‖ ($a :: $env)) ≡
            ($B).subst (Val.toExpr ‖$Δ‖ $a).toSb := by
          have := b.tp_eq_synthTp.symm_tp.subst (env.wf_sbOfEnv.up b.wf_ctx.inv_snoc)
            |>.conv_binder (A'env.trans_tp Aeq.symm_tp)
            |>.trans_tp (Benv.conv_binder Aeq.symm_tp)
            |>.trans_tp Beq.symm_tp
          convert this.subst <| WfSb.toSb ($Δa).wf_toExpr using 1
          autosubst
          apply sb_irrel.1 b.with_synthTp.wf_tp
          intro i lt
          cases i
          . simp
          . dsimp; apply sbOfEnv_get_eq; simpa [env.eq_length] using lt
        constructor
        . apply vwf.conv_nf bigEq
        . apply veq.conv_eq bigEq |>.trans_tm
          have Δb := b.subst (env.wf_sbOfEnv.up b.wf_ctx.inv_snoc)
            |>.conv_binder A'env |>.conv (Benv.trans_tp <| Beq.symm_tp.conv_binder Aeq)
          have Δa := ($Δa).conv_nf Aeq
          simp only [Val.toExpr, Clos.toExpr]
          convert EqTm.app_lam Δb Δa.wf_toExpr |>.symm_tm.trans_tm _ using 1
          . autosubst
            apply sb_irrel.2 b
            intro i lt
            cases i
            . simp
            . dsimp; apply sbOfEnv_get_eq; simpa [env.eq_length] using lt
          apply EqTm.refl_tm <| WfTm.app (WfTm.lam Δb) Δa.wf_toExpr
      )⟩
  | .neut n => do
    let n : Val := .neut <| .app l l' B n a
    return ⟨n,
      q(by as_aux_lemma =>
        constructor
        . exact WfValTm.neut_tm <| WfNeutTm.app ($Δf).inv_neut ($Δa)
        . simp +zetaDelta only [Val.toExpr, Neut.toExpr]
          exact EqTm.refl_tm <| WfTm.app ($Δf).inv_neut.wf_toExpr ($Δa).wf_toExpr
      )⟩
  | _ => throw s!"unexpected normal form {repr f} at type Π"

partial def evalFst (Δ : Ctx) (l l' : Nat) (A B : Expr) (p : Val)
    (Δp : Q(WfValTm $Δ (max $l $l') $p (.sigma $l $l' $A $B))) :
    Except String ((v : Val) ×
      Q(WfValTm $Δ $l $v $A ∧
        ($Δ ⊢[$l] ($v).toExpr ‖$Δ‖ ≡ .fst $l $l' $A $B (($p).toExpr ‖$Δ‖) : $A))) :=
  match p with
  | .pair _ _ _ v _ =>
    return ⟨v,
      q(by as_aux_lemma =>
        simp only [Val.toExpr]
        have ⟨_, _, v, w, eq⟩ := ($Δp).inv_pair
        obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
        replace v := v.conv_nf Aeq.symm_tp
        refine ⟨v, ?_⟩
        apply EqTm.fst_pair Beq.wf_right v.wf_toExpr w.wf_toExpr |>.symm_tm.trans_tm
        gcongr
        apply WfTm.pair Beq.wf_right v.wf_toExpr w.wf_toExpr
      )⟩
  | .neut n =>
    return ⟨.neut (.fst l l' A B n),
      q(by as_aux_lemma =>
        constructor
        . exact WfValTm.neut_tm <| WfNeutTm.fst ($Δp).inv_neut
        . convert EqTm.refl_tm <| WfTm.fst ($Δp).wf_toExpr using 1
          simp [Val.toExpr, Neut.toExpr]
      )⟩
  | _ => throw s!"unexpected normal form {repr p} at type Σ"

partial def evalSnd (Δ : Ctx) (l l' : Nat) (A B : Expr) (p : Val)
    (Δp : Q(WfValTm $Δ (max $l $l') $p (.sigma $l $l' $A $B))) :
    Except String ((v : Val) ×
      Q(WfValTm $Δ $l' $v (($B).subst (Expr.fst $l $l' $A $B (($p).toExpr ‖$Δ‖)).toSb) ∧
        ($Δ ⊢[$l'] ($v).toExpr ‖$Δ‖ ≡ .snd $l $l' $A $B (($p).toExpr ‖$Δ‖) :
          ($B).subst (Expr.fst $l $l' $A $B (($p).toExpr ‖$Δ‖)).toSb))) :=
  match p with
  | .pair _ _ B' v w =>
    return ⟨w,
      q(by as_aux_lemma =>
        simp only [Val.toExpr]
        have ⟨_, _, v, w, eq⟩ := ($Δp).inv_pair
        obtain ⟨_, rfl, rfl, Aeq,Beq⟩ := eq.inv_sigma
        replace v := v.conv_nf Aeq.symm_tp
        have fstPair : $Δ ⊢[$l]
            (Expr.fst $l $l' $A $B (Expr.pair $l $l' $B' (($v).toExpr ‖$Δ‖) (($w).toExpr ‖$Δ‖))) ≡
              (($v).toExpr ‖$Δ‖) : $A := by
          apply EqTm.trans_tm _ <| EqTm.fst_pair Beq.wf_right v.wf_toExpr w.wf_toExpr
          gcongr
          apply WfTm.pair Beq.wf_right v.wf_toExpr w.wf_toExpr |>.conv
          gcongr
        have BFstPair := Beq.symm_tp.subst_eq <| EqSb.toSb fstPair.symm_tm
        constructor
        . apply w.conv_nf BFstPair
        . have := EqTm.snd_pair Beq.wf_right v.wf_toExpr w.wf_toExpr |>.symm_tm
          apply this.conv_eq BFstPair |>.trans_tm
          symm; gcongr
          apply WfTm.pair Beq.wf_right v.wf_toExpr w.wf_toExpr |>.conv
          gcongr
      )⟩
  | .neut n =>
    return ⟨.neut (.snd l l' A B n),
      q(by as_aux_lemma =>
        simp only [Val.toExpr, Neut.toExpr]
        constructor
        . exact WfValTm.neut_tm <| WfNeutTm.snd ($Δp).inv_neut
        . convert EqTm.refl_tm <| WfTm.snd ($Δp).wf_toExpr using 1 <;> simp [Val.toExpr]
      )⟩
  | _ => throw s!"unexpected normal form {repr p} at type Σ"

end
