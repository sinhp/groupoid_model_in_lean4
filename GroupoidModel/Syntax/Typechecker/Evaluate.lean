import Qq

import GroupoidModel.Syntax.Synth
import GroupoidModel.Syntax.Typechecker.ValueInversion
import GroupoidModel.Syntax.Typechecker.Util

open Qq

/-! ## Evaluation -/

-- Qq bug: shadowing by `u : Q(Expr)` below causes 'unbound level param' errors.
variable {_u : Lean.Level} {χ : Q(Type _u)}

mutual

/-- Evaluate a type in an environment of values.

Note: we use `as_aux_lemma` pervasively to minimize the size of produced proof terms. -/
partial def evalTp (env : Q(List (Val $χ))) (T' : Q(Expr $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ Δ σ l}, [Fact E.Wf] → EnvEqSb E Δ $env σ Γ → (E ∣ Γ ⊢[l] ($T')) →
      ValEqTp E Δ l $v (($T').subst σ))) := do
  /- TODO: establish a convention for when inputs are supposed to be in WHNF.
  Should `evalTp` reject types not in WHNF?
  Then we'd need to evaluate them in `lookup`,
  and other places where compound quotations are produced.
  On the other hand, lazy evaluation may be more efficient. -/
  let T : Q(Expr $χ) ← Lean.Meta.whnf T'
  have _ : $T =Q $T' := .unsafeIntro
  match T with
  | ~q(.pi $l $l' $A $B) => do
    let ⟨vA, vApost⟩ ← evalTp q($env) q($A)
    return ⟨q(.pi $l $l' $vA (.of_expr $env $B)), q(by as_aux_lemma =>
      introv _ env T
      obtain ⟨rfl, B⟩ := T.inv_pi
      have vAeq := $vApost env B.wf_binder
      apply ValEqTp.pi vAeq
      apply ClosEqTp.clos_tp env (EqTp.refl_tp vAeq.wf_tp) B
    )⟩
  | ~q(.sigma $l $l' $A $B) => do
    let ⟨vA, vApost⟩ ← evalTp q($env) q($A)
    return ⟨q(.sigma $l $l' $vA (.of_expr $env $B)), q(by as_aux_lemma =>
      introv _ env T
      obtain ⟨rfl, B⟩ := T.inv_sigma
      have vAeq := $vApost env B.wf_binder
      apply ValEqTp.sigma vAeq
      apply ClosEqTp.clos_tp env (EqTp.refl_tp vAeq.wf_tp) B
    )⟩
  | ~q(.Id $l $A $t $u) => do
    let ⟨vA, vApost⟩ ← evalTp q($env) q($A)
    let ⟨vt, vtpost⟩ ← evalTm q($env) q($t)
    let ⟨vu, vupost⟩ ← evalTm q($env) q($u)
    return ⟨q(.Id $l $vA $vt $vu), q(by as_aux_lemma =>
      introv _ env T
      simp +zetaDelta only [Expr.subst]
      have ⟨_, t, u⟩ := T.inv_Id
      subst_vars
      apply ValEqTp.Id ($vApost env t.wf_tp) ($vtpost env t) ($vupost env u)
    )⟩
  | ~q(.el $a) => do
    let ⟨va, vapost⟩ ← evalTm q($env) q($a)
    let ⟨v, vpost⟩ ← evalEl q($va)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env T
      have := $vapost env T.inv_el
      exact $vpost this
    )⟩
  | ~q(.univ $l) =>
    return ⟨q(.univ $l), q(by as_aux_lemma =>
      introv _ env T
      cases T.inv_univ
      have := T.le_univMax
      exact ValEqTp.univ env.wf_dom (by omega)
    )⟩
  | T => throwError "expected a type, got{Lean.indentExpr T}"

/-- Evaluate a term in an environment of values. -/
partial def evalTm (env : Q(List (Val $χ))) (t' : Q(Expr $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ Δ σ A l}, [Fact E.Wf] → EnvEqSb E Δ $env σ Γ → (E ∣ Γ ⊢[l] ($t') : A) →
      ValEqTm E Δ l $v (($t').subst σ) (A.subst σ))) := do
  -- TODO: see comment at `evalTp`.
  let t : Q(Expr $χ) ← Lean.Meta.whnf t'
  have _ : $t =Q $t' := .unsafeIntro
  match t with
  | ~q(.ax $c) =>
    return ⟨q(.ax $c), q(by as_aux_lemma =>
      introv _ env t
      have ⟨Al, Ec, _, eq⟩ := t.inv_ax
      subst_vars
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ValEqTm.ax env.wf_dom Ec using 1
      simp [Expr.subst_of_isClosed _ Al.2.1]
    )⟩
  | ~q(.bvar $i) => do
    /- We evaluate the list access and error if a concrete element doesn't pop out.
    We do this (instead of producing e.g. `q($env[$i]? |>.getD default)`) to catch errors here,
    rather than when the value is weak-head normalized and inspected at a later point. -/
    let v : Q(Option (Val $χ)) ← Lean.Meta.whnf q($env[$i]?)
    let ~q(some $v') := v
      | throwError "bvar {i} may be out of range\
        in evaluation environment{Lean.indentExpr env}\n\
        note: expected 'some _', got{Lean.indentExpr v}"
    have : $v =Q $env[$i]? := .unsafeIntro -- FIXME: `whnfQ`?
    return ⟨v', q(by as_aux_lemma =>
      introv _ env t
      have ⟨_, lk, eq⟩ := t.inv_bvar
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert env.lookup_eq lk using 1
      subst $v
      have ⟨_, h⟩ := List.getElem?_eq_some_iff.mp ($this).symm
      rw [h]
    )⟩
  | ~q(.lam $k $k' $C $b) => do
    let ⟨vC, vCpost⟩ ← evalTp q($env) q($C)
    return ⟨q(.lam $k $k' $vC (.of_expr $env $b)), q(by as_aux_lemma =>
      introv _ env t
      obtain ⟨rfl, B, b, eq⟩ := t.inv_lam
      have C := b.wf_binder
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTm.lam ($vCpost env C) <| ClosEqTm.clos_tm env _ _ b
      . exact EqTp.refl_tp <| C.subst env.wf_sb
      . exact EqTp.refl_tp <| b.wf_tp.subst (env.wf_sb.up C)
    )⟩
  | ~q(.app $k $k' $B $f $a) => do
    let ⟨vf, vfpost⟩ ← evalTm q($env) q($f)
    let ⟨va, vapost⟩ ← evalTm q($env) q($a)
    let ⟨v, vpost⟩ ← evalApp q($vf) q($va)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env t
      obtain ⟨rfl, _, f, a, eq⟩ := t.inv_app
      apply $vpost ($vfpost env f) ($vapost env a) |>.conv_tp
      convert eq.subst env.wf_sb |>.symm_tp using 1
      autosubst
    )⟩
  | ~q(.pair $k $k' $B $f $s) => do
    let ⟨vf, vfpost⟩ ← evalTm q($env) q($f)
    let ⟨vs, vspost⟩ ← evalTm q($env) q($s)
    return ⟨q(.pair $k $k' $vf $vs), q(by as_aux_lemma =>
      introv _ env t
      obtain ⟨rfl, _, t, u, eq⟩ := t.inv_pair
      have ⟨_, B⟩ := eq.wf_right.inv_sigma
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTm.pair (B.subst (env.wf_sb.up B.wf_binder)) ($vfpost env t)
      convert ($vspost env u) using 1
      autosubst
    )⟩
  | ~q(.fst $k $k' $A $B $p) => do
    let ⟨vp, vppost⟩ ← evalTm q($env) q($p)
    let ⟨v, vpost⟩ ← evalFst q($vp)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env t
      obtain ⟨rfl, p, eq⟩ := t.inv_fst
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      exact $vpost ($vppost env p)
    )⟩
  | ~q(.snd $k $k' $A $B $p) => do
    let ⟨vp, vppost⟩ ← evalTm q($env) q($p)
    let ⟨v, vpost⟩ ← evalSnd q($vp)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env t
      obtain ⟨rfl, p, eq⟩ := t.inv_snd
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ($vpost) ($vppost env p) using 1
      autosubst
    )⟩
  | ~q(.refl $l $u) => do
    let ⟨vu, vupost⟩ ← evalTm q($env) q($u)
    return ⟨q(.refl $l $vu), q(by as_aux_lemma =>
      introv _ env t
      have ⟨_, _, u, eq⟩ := t.inv_refl
      subst_vars
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTm.refl ($vupost env u)
    )⟩
  | ~q(.idRec $l $l' _ $M $r _ $h) => do
    let ⟨vr, vrpost⟩ ← evalTm q($env) q($r)
    let ⟨vh, vhpost⟩ ← evalTm q($env) q($h)
    let ⟨v, vpost⟩ ← evalIdRec q($l') q(.of_expr $env $M) q($vr) q($vh)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env rec
      have ⟨_, _, t, M, r, u, h, eq⟩ := rec.inv_idRec
      subst_vars
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      rw [Expr.subst_snoc_toSb_subst]
      have tE := t.subst env.wf_sb
      apply $vpost _ (autosubst% $vrpost env r) ($vhpost env h)
      apply Clos₂EqTp.clos₂_tp env (.refl_tp tE.wf_tp) _ M
      autosubst; apply EqTp.refl_tp <| autosubst% WfTp.Id_bvar tE
    )⟩
  | ~q(.code $A) => do
    let ⟨vA, vApost⟩ ← evalTp q($env) q($A)
    return ⟨q(.code $vA), q(by as_aux_lemma =>
      introv _ env t
      obtain ⟨_, rfl, A, eq⟩ := t.inv_code
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have := t.le_univMax
      apply ValEqTm.code (by omega) ($vApost env A)
    )⟩
  | t => throwError "expected a term, got{Lean.indentExpr t}"

/-- Evaluate a type value in a new environment.

This operation is not commonly implemented in NbE variants.
We need it as an alternative to readback:
when having to produce a type closure from a type value,
instead of reading back and storing `Clos.of_expr`,
we store `Clos.of_val`.
However, that means we may later need to evaluate the stored value in a new environment,
and `evalValTp` does that. -/
partial def evalValTp (env : Q(List (Val $χ))) (vT : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ Δ A σ l}, [Fact E.Wf] → EnvEqSb E Δ $env σ Γ → ValEqTp E Γ l $vT A →
      ValEqTp E Δ l $v (A.subst σ))) := do
  match vT with
  | ~q(.pi $k $k' $vA $vB) =>
    let ⟨vB, vBpost⟩ ← forceClosTp q(($env).length) q($vA) q($vB)
    let ⟨vA, vApost⟩ ← evalValTp q($env) q($vA)
    return ⟨q(.pi $k $k' $vA (.of_val $env $vB)), q(by as_aux_lemma =>
      introv _ env vT
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_pi
      subst_vars
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have vAσ := $vApost env vA
      apply ValEqTp.pi vAσ
      apply ClosEqTp.clos_val_tp env (EqTp.refl_tp vAσ.wf_tp) <|
        $vBpost env.eq_length vA vB
    )⟩
  | ~q(.sigma $k $k' $vA $vB) =>
    let ⟨vB, vBpost⟩ ← forceClosTp q(($env).length) q($vA) q($vB)
    let ⟨vA, vApost⟩ ← evalValTp q($env) q($vA)
    return ⟨q(.sigma $k $k' $vA (.of_val $env $vB)), q(by as_aux_lemma =>
      introv _ env vT
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_sigma
      subst_vars
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have vAσ := $vApost env vA
      apply ValEqTp.sigma vAσ
      apply ClosEqTp.clos_val_tp env (EqTp.refl_tp vAσ.wf_tp) <|
        $vBpost env.eq_length vA vB
    )⟩
  | ~q(.Id $k $vA $vt $vu) =>
    let ⟨vA, vApost⟩ ← evalValTp q($env) q($vA)
    let ⟨vt, vtpost⟩ ← evalValTm q($env) q($vt)
    let ⟨vu, vupost⟩ ← evalValTm q($env) q($vu)
    return ⟨q(.Id $k $vA $vt $vu), q(by as_aux_lemma =>
      introv _ env vT
      have ⟨_, _, _, _, vA, vt, vu, eq⟩ := vT.inv_Id
      subst_vars
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTp.Id ($vApost env vA) ($vtpost env vt) ($vupost env vu)
    )⟩
  | ~q(.univ $l) => return ⟨q(.univ $l), q(by as_aux_lemma =>
      introv _ env vT
      have ⟨_, eq⟩ := vT.inv_univ
      have := eq.le_univMax
      subst_vars
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTp.univ env.wf_dom (by omega)
    )⟩
  | ~q(.el $na) =>
    let ⟨va, vapost⟩ ← evalNeutTm q($env) q($na)
    let ⟨v, vpost⟩ ← evalEl q($va)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env vT
      have ⟨_, na, eq⟩ := vT.inv_el
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      exact $vpost ($vapost env na)
    )⟩
  | vT => throwError "expected a normal type, got{Lean.indentExpr vT}"

/-- Evaluate a term value in a new environment. -/
partial def evalValTm (env : Q(List (Val $χ))) (vt : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ Δ A t σ l}, [Fact E.Wf] → EnvEqSb E Δ $env σ Γ → ValEqTm E Γ l $vt t A →
      ValEqTm E Δ l $v (t.subst σ) (A.subst σ))) := do
  match vt with
  | ~q(.ax $c) =>
    return ⟨q(.ax $c), q(by as_aux_lemma =>
      introv _ env vt
      have ⟨Al, Ec, _, eqt, eq⟩ := vt.inv_ax
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ValEqTm.ax env.wf_dom Ec using 1
      simp [Expr.subst_of_isClosed _ Al.2.1]
    )⟩
  | ~q(.lam $k $k' $vA $b) =>
    -- NOTE: the binder type argument to `forceClosTm` is the only reason we annotate `Val.lam`.
    let ⟨vb, vbpost⟩ ← forceClosTm q(($env).length) q($vA) q($b)
    let ⟨vA, vApost⟩ ← evalValTp q($env) q($vA)
    return ⟨q(.lam $k $k' $vA (.of_val $env $vb)), q(by as_aux_lemma =>
      introv _ env vt
      have ⟨_, _, _, _, vA, vb, eqt, eq⟩ := vt.inv_lam
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have vAσ := $vApost env vA
      apply ValEqTm.lam vAσ
      apply ClosEqTm.clos_val_tm env (EqTp.refl_tp vAσ.wf_tp)
        (EqTp.refl_tp <| vb.wf_tm.wf_tp.subst (env.wf_sb.up vA.wf_tp))
        ($vbpost env.eq_length vA vb)
    )⟩
  | ~q(.pair $k $k' $vf $vs) =>
    let ⟨vf, vfpost⟩ ← evalValTm q($env) q($vf)
    let ⟨vs, vspost⟩ ← evalValTm q($env) q($vs)
    return ⟨q(.pair $k $k' $vf $vs), q(by as_aux_lemma =>
      introv _ env vt
      have ⟨_, _, _, _, _, vf, vs, eqt, eq⟩ := vt.inv_pair
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have ⟨_, B⟩ := eq.wf_right.inv_sigma
      apply ValEqTm.pair (B.subst (env.wf_sb.up B.wf_binder)) ($vfpost env vf)
      convert ($vspost env vs) using 1; autosubst
    )⟩
  | ~q(.refl $k $va) =>
    let ⟨va, vapost⟩ ← evalValTm q($env) q($va)
    return ⟨q(.refl $k $va), q(by as_aux_lemma =>
      introv _ env vt
      have ⟨_, _, _, va, eqt, eq⟩ := vt.inv_refl
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTm.refl ($vapost env va)
    )⟩
  | ~q(.code $vA) =>
    let ⟨vA, vApost⟩ ← evalValTp q($env) q($vA)
    return ⟨q(.code $vA), q(by as_aux_lemma =>
      introv _ env vt
      have ⟨_, _, _, vA, eqt, eq⟩ := vt.inv_code
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have := eq.le_univMax
      apply ValEqTm.code (by omega) ($vApost env vA)
    )⟩
  | ~q(.neut $n _) =>
    let ⟨v, vpost⟩ ← evalNeutTm q($env) q($n)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env vt
      have ⟨_, n⟩ := vt.inv_neut
      exact $vpost env n
    )⟩
  | vt => throwError "expected a normal term, got{Lean.indentExpr vt}"

/-- Evaluate a neutral term in a new environment. -/
partial def evalNeutTm (env : Q(List (Val $χ))) (nt : Q(Neut $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ Δ A t σ l}, [Fact E.Wf] → EnvEqSb E Δ $env σ Γ → NeutEqTm E Γ l $nt t A →
      ValEqTm E Δ l $v (t.subst σ) (A.subst σ))) := do
  match nt with
  | ~q(.bvar $i) =>
    let v : Q(Option (Val $χ)) ← Lean.Meta.whnf q($env[($env).length - $i - 1]?)
    let ~q(some $v') := v
      | throwError "bvar {i} may be out of range in evaluation environment{Lean.indentExpr env}\n\
        note: expected 'some _', got{Lean.indentExpr v}"
    have : $v =Q $env[($env).length - $i - 1]? := .unsafeIntro -- FIXME: `whnfQ`?
    return ⟨v', q(by as_aux_lemma =>
      introv _ env nt
      have ⟨_, lk, eqt, eq⟩ := nt.inv_bvar
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert env.lookup_eq lk using 1
      subst $v
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp ($this).symm
      congr 3
      exact env.eq_length
    )⟩
  | ~q(.app _ _ _ $nf $va) =>
    let ⟨vf, vfpost⟩ ← evalNeutTm q($env) q($nf)
    let ⟨va, vapost⟩ ← evalValTm q($env) q($va)
    let ⟨v, vpost⟩ ← evalApp q($vf) q($va)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env nt
      have ⟨_, _, _, _, _, _, nf, va, eqt, eq⟩ := nt.inv_app
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ($vpost ($vfpost env nf) ($vapost env va)) using 1
      autosubst
    )⟩
  | ~q(.fst $k $k' $np) =>
    let ⟨vp, vppost⟩ ← evalNeutTm q($env) q($np)
    let ⟨v, vpost⟩ ← evalFst q($vp)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env nt
      have ⟨_, _, _, _, np_eq, eqt, eq⟩ := nt.inv_fst
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      exact $vpost ($vppost env np_eq)
    )⟩
  | ~q(.snd $k $k' $np) =>
    let ⟨vp, vppost⟩ ← evalNeutTm q($env) q($np)
    let ⟨v, vpost⟩ ← evalSnd q($vp)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env nt
      have ⟨_, _, _, _, np_eq, eqt, eq⟩ := nt.inv_snd
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ($vpost ($vppost env np_eq)) using 1
      autosubst
    )⟩
  | ~q(.idRec $k $k' $vA $va $cM $vr $vh) =>
    /- NOTE: the type arguments to `forceClos₂Tp`
    are the only reason we annotate `Neut.idRec` with `vA`, `va`. -/
    let ⟨cM, cMpost⟩ ← forceClos₂Tp q(($env).length)
      q($vA) q(.Id $k $vA $va (.neut (.bvar ($env).length) $vA)) q($cM)
    let ⟨vr, vrpost⟩ ← evalValTm q($env) q($vr)
    let ⟨vh, vhpost⟩ ← evalNeutTm q($env) q($vh)
    let ⟨v, vpost⟩ ← evalIdRec q($k') q(.of_val $env $cM) q($vr) q($vh)
    return ⟨v, q(by as_aux_lemma =>
      introv _ env nt
      have ⟨_, _, _, _, _, _, _, vA, va, cM, vr, vh, eqt, eq⟩ := nt.inv_idRec
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      rw [Expr.subst_snoc_toSb_subst]
      apply $vpost _ (autosubst% $vrpost env vr) ($vhpost env vh)
      have w := vA.wf_tp
      refine have vId := ?_;
        Clos₂EqTp.clos₂_val_tp
          env
          (.refl_tp <| vA.wf_tp.subst env.wf_sb)
          ?_
          ($cMpost env.eq_length vA vId cM)
      . rw [env.eq_length]; apply ValEqTp.Id_bvar vA va
      . exact autosubst% EqTp.refl_tp <| vId.wf_tp.subst (env.wf_sb.up w)
    )⟩
  | vt => throwError "expected a normal term, got{Lean.indentExpr vt}"

/-- Evaluate a type closure on an argument. -/
partial def evalClosTp (vB : Q(Clos $χ)) (vt : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ A B t l l'}, [Fact E.Wf] → ClosEqTp E Γ l l' A $vB B → ValEqTm E Γ l $vt t A →
      ValEqTp E Γ l' $v (B.subst t.toSb))) := do
  match vB with
  | ~q(.of_expr $env $B) => do
    let ⟨v, vpost⟩ ← evalTp q($vt :: $env) q($B)
    return ⟨v, q(by as_aux_lemma =>
      introv _ vB vt
      simp +zetaDelta only at vB
      rcases vB with ⟨env, Aeq, B⟩
      convert ($vpost (env.snoc B.wf_binder (vt.conv_tp Aeq.symm_tp)) B) using 1
      autosubst
    )⟩
  | ~q(.of_val $env $vB') => do
    let ⟨v, vpost⟩ ← evalValTp q($vt :: $env) q($vB')
    return ⟨v, q(by as_aux_lemma =>
      introv _ vB vt
      simp +zetaDelta only at vB
      rcases vB with _ | ⟨env, Aeq, B⟩
      have := env.snoc B.wf_tp.wf_binder (vt.conv_tp Aeq.symm_tp)
      convert ($vpost this B) using 1
      autosubst
    )⟩
  | vB => throwError "expected a type closure, got{Lean.indentExpr vB}"

/-- Evaluate a type closure on a fresh variable. -/
partial def forceClosTp (d : Q(Nat)) (vA : Q(Val $χ)) (vB : Q(Clos $χ)) :
    Lean.MetaM ((v : Q(Val $χ)) × Q(∀ {E Γ A B l l'}, [Fact E.Wf] → $d = Γ.length →
      ValEqTp E Γ l $vA A →
      ClosEqTp E Γ l l' A $vB B →
      ValEqTp E ((A, l) :: Γ) l' $v B)) := do
  let ⟨v, vpost⟩ ← evalClosTp q($vB) q(.neut (.bvar $d) $vA)
  return ⟨v, q(by as_aux_lemma =>
    introv _ deq vA vB
    replace vB := vB.wk vA.wf_tp
    replace vA := vA.wk vA.wf_tp
    have := NeutEqTm.bvar vA.wf_tp.wf_ctx (Lookup.zero ..)
    simp only [List.length_cons, ← deq, Nat.sub_zero, Nat.add_one_sub_one] at this
    have := ValEqTm.neut_tm vA this
    convert ($vpost vB this) using 1
    autosubst
  )⟩

/-- Evaluate a type closure on two arguments. -/
partial def evalClos₂Tp (vC : Q(Clos $χ)) (vt vu : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ A B C t u l l' l''}, [Fact E.Wf] → Clos₂EqTp E Γ A l B l' l'' $vC C →
      ValEqTm E Γ l $vt t A →
      ValEqTm E Γ l' $vu u (B.subst t.toSb) →
      ValEqTp E Γ l'' $v (C.subst (.snoc t.toSb u)))) := do
  match vC with
  | ~q(.of_expr $env $C) => do
    let ⟨v, vpost⟩ ← evalTp q($vu :: $vt :: $env) q($C)
    return ⟨v, q(by as_aux_lemma =>
      introv _ vC vt vu
      simp +zetaDelta only at vC
      rcases vC with ⟨env, Aeq, Beq, C⟩
      have B := C.wf_binder
      have A := B.wf_binder
      have Bteq := Beq.subst <| WfSb.toSb vt.wf_tm
      have := env.snoc A (vt.conv_tp Aeq.symm_tp)
        |>.snoc B (vu.conv_tp <| autosubst% Bteq.symm_tp)
      exact autosubst% $vpost this C
    )⟩
  | ~q(.of_val $env $vC') => do
    let ⟨v, vpost⟩ ← evalValTp q($vu :: $vt :: $env) q($vC')
    return ⟨v, q(by as_aux_lemma =>
      introv _ vC vt vu
      simp +zetaDelta only at vC
      rcases vC with _ | ⟨env, Aeq, Beq, C⟩
      have B := C.wf_tp.wf_binder
      have A := B.wf_binder
      have Bteq := Beq.subst <| WfSb.toSb vt.wf_tm
      have := env.snoc A (vt.conv_tp Aeq.symm_tp)
        |>.snoc B (vu.conv_tp <| autosubst% Bteq.symm_tp)
      exact autosubst% $vpost this C
    )⟩
  | vB => throwError "expected a type closure₂, got{Lean.indentExpr vC}"

partial def forceClos₂Tp (d : Q(Nat)) (vA vB : Q(Val $χ)) (vC : Q(Clos $χ)) :
    Lean.MetaM ((v : Q(Val $χ)) × Q(∀ {E Γ A B C l l' l''}, [Fact E.Wf] → $d = Γ.length →
      ValEqTp E Γ l $vA A →
      ValEqTp E ((A, l) :: Γ) l' $vB B →
      Clos₂EqTp E Γ A l B l' l'' $vC C →
      ValEqTp E ((B, l') :: (A, l) :: Γ) l'' $v C)) := do
  let ⟨v, vpost⟩ ← evalClos₂Tp q($vC) q(.neut (.bvar $d) $vA) q(.neut (.bvar ($d + 1)) $vB)
  return ⟨v, q(by as_aux_lemma =>
    introv _ deq vA vB vC
    replace vC := vC.wk vA.wf_tp |>.wk vB.wf_tp
    replace vA := vA.wk vA.wf_tp |>.wk vB.wf_tp
    replace vB := vB.wk vB.wf_tp
    have ΓAB := vA.wf_tp.wf_ctx
    have xA := NeutEqTm.bvar ΓAB (Lookup.succ _ _ <| Lookup.zero ..)
    have xB := NeutEqTm.bvar ΓAB (Lookup.zero ..)
    simp only [List.length_cons, Nat.zero_add, Nat.add_one_sub_one, Nat.sub_zero, ← deq] at xA xB
    exact autosubst% $vpost vC (.neut_tm vA xA) (.neut_tm (autosubst% vB) (autosubst% xB))
  )⟩

/-- Evaluate a term closure on an argument. -/
partial def evalClosTm (vb : Q(Clos $χ)) (vt : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ A B b t l l'}, [Fact E.Wf] → ClosEqTm E Γ l l' A B $vb b → ValEqTm E Γ l $vt t A →
      ValEqTm E Γ l' $v (b.subst t.toSb) (B.subst t.toSb))) := do
  match vb with
  | ~q(.of_expr $env $b) => do
    let ⟨v, vpost⟩ ← evalTm q($vt :: $env) q($b)
    return ⟨v, q(by as_aux_lemma =>
      introv _ vb vt
      simp +zetaDelta only at vb
      rcases vb with ⟨env, Aeq, Beq, b⟩
      have := env.snoc b.wf_binder (vt.conv_tp Aeq.symm_tp)
      have Beq := Beq.subst <| WfSb.toSb vt.wf_tm
      convert ($vpost this b |>.conv_tp (by convert Beq using 1; autosubst)) using 1
      autosubst
    )⟩
  | ~q(.of_val $env $vb') => do
    let ⟨v, vpost⟩ ← evalValTm q($vt :: $env) q($vb')
    return ⟨v, q(by as_aux_lemma =>
      introv _ vb vt
      simp +zetaDelta only at vb
      rcases vb with _ | ⟨env, Aeq, Beq, b⟩
      have := env.snoc b.wf_tm.wf_binder (vt.conv_tp Aeq.symm_tp)
      have Beq := Beq.subst <| WfSb.toSb vt.wf_tm
      convert ($vpost this b |>.conv_tp (by convert Beq using 1; autosubst)) using 1
      autosubst
    )⟩
  | vB => throwError "expected a type closure, got{Lean.indentExpr vB}"

/-- Evaluate a term closure on a fresh variable. -/
partial def forceClosTm (d : Q(Nat)) (vA : Q(Val $χ)) (vb : Q(Clos $χ)) :
    Lean.MetaM ((v : Q(Val $χ)) × Q(∀ {E Γ A B b l l'}, [Fact E.Wf] → $d = Γ.length →
        ValEqTp E Γ l $vA A → ClosEqTm E Γ l l' A B $vb b →
        ValEqTm E ((A, l) :: Γ) l' $v b B)) := do
  let ⟨v, vpost⟩ ← evalClosTm q($vb) q(.neut (.bvar $d) $vA)
  return ⟨v, q(by as_aux_lemma =>
    introv _ deq vA vb
    replace vb := vb.wk vA.wf_tp
    replace vA := vA.wk vA.wf_tp
    have := NeutEqTm.bvar vA.wf_tp.wf_ctx (Lookup.zero ..)
    simp only [List.length_cons, ← deq, Nat.sub_zero, Nat.add_one_sub_one] at this
    have := ValEqTm.neut_tm vA this
    convert ($vpost vb this) using 1 <;> autosubst
  )⟩

partial def evalEl (va : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Δ a l}, [Fact E.Wf] → ValEqTm E Δ (l + 1) $va a (.univ l) →
      ValEqTp E Δ l $v (.el a))) :=
  match va with
  | ~q(.code $vA) =>
    return ⟨vA, q(by as_aux_lemma =>
      introv _ va
      have ⟨_, _, h, vA, eqt, eq⟩ := va.inv_code
      cases h
      apply vA.conv_tp
      have := eq.le_univMax
      symm
      apply EqTp.cong_el eqt |>.trans_tp
      apply EqTp.el_code (by omega) vA.wf_tp
    )⟩
  | ~q(.neut $na _) =>
    return ⟨q(.el $na), q(by as_aux_lemma =>
      introv _ va
      have ⟨_, na⟩ := va.inv_neut
      apply ValEqTp.el na
    )⟩
  | va => throwError "expected a normal form at type Univ, got{Lean.indentExpr va}"

partial def evalApp (vf va : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Δ A B f a l l'}, [Fact E.Wf] → ValEqTm E Δ (max l l') $vf f (.pi l l' A B) →
      ValEqTm E Δ l $va a A →
      ValEqTm E Δ l' $v (.app l l' B f a) (B.subst a.toSb))) :=
  match vf with
  | ~q(.lam $k $k' _ $vb) => do
    let ⟨v, vpost⟩ ← evalClosTm q($vb) q($va)
    return ⟨v, q(by as_aux_lemma =>
      introv _ vf va
      have ⟨_, _, _, _, _, vb, eqt, eq⟩ := vf.inv_lam
      have ⟨_, _, _, Aeq, Beq⟩ := eq.inv_pi
      subst_vars
      have := $vpost vb (va.conv_tp Aeq) |>.conv_tp (Beq.subst <| WfSb.toSb va.wf_tm).symm_tp
      apply this.conv_tm
      have b := vb.wf_tm |>.conv_binder Aeq.symm_tp |>.conv Beq.symm_tp
      apply (EqTm.app_lam b va.wf_tm).symm_tm.trans_tm
      apply EqTm.cong_app (EqTp.refl_tp b.wf_tp) _ (EqTm.refl_tm va.wf_tm)
      apply EqTm.symm_tm; apply eqt.trans_tm
      apply EqTm.symm_tm; gcongr
      assumption
    )⟩
  | ~q(.neut $n (.pi $k $k' $vA $vB)) => do
    let ⟨vBa, vBpost⟩ ← evalClosTp q($vB) q($va)
    return ⟨q(.neut (.app $k $k' $vA $n $va) $vBa), q(by as_aux_lemma =>
      introv _ vf va
      have ⟨P, n⟩ := vf.inv_neut
      have ⟨_, _, _, vA, vB, eq⟩ := P.inv_pi
      have ⟨_, _, _, Aeq, Beq⟩ := eq.inv_pi
      subst_vars
      have := $vBpost vB (va.conv_tp Aeq) |>.conv_tp (Beq.subst <| WfSb.toSb va.wf_tm).symm_tp
      apply ValEqTm.neut_tm this
      apply NeutEqTm.app (vA.conv_tp Aeq.symm_tp) n va
    )⟩
  | vf => throwError "expected a normal form at type Π, got{Lean.indentExpr vf}"

partial def evalFst (vp : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Δ A B p l l'}, [Fact E.Wf] → ValEqTm E Δ (max l l') $vp p (.sigma l l' A B) →
      ValEqTm E Δ l $v (.fst l l' A B p) A)) :=
  match vp with
  | ~q(.pair _ _ $v _) =>
    return ⟨v, q(by as_aux_lemma =>
      introv _ vp
      have ⟨_, A', B', f, s, v, _, eqt, eq⟩ := vp.inv_pair
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
      have : E ∣ Δ ⊢[l] f ≡ Expr.fst l l' A B p : A := by
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
    return ⟨q(.neut (.fst $k $k' $n) $vA), q(by as_aux_lemma =>
      introv _ vp
      have ⟨S, p⟩ := vp.inv_neut
      have ⟨_, _, _, vA, vB, eq⟩ := S.inv_sigma
      obtain ⟨_, rfl, rfl, Aeq, _⟩ := eq.inv_sigma
      apply ValEqTm.neut_tm (vA.conv_tp Aeq.symm_tp) (NeutEqTm.fst p)
    )⟩
  | vp => throwError "expected a normal form at type Σ, got{Lean.indentExpr vp}"

partial def evalSnd (vp : Q(Val $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Δ A B p l l'}, [Fact E.Wf] → ValEqTm E Δ (max l l') $vp p (.sigma l l' A B) →
      ValEqTm E Δ l' $v (.snd l l' A B p) (B.subst (Expr.fst l l' A B p).toSb))) :=
  match vp with
  | ~q(.pair _ _ _ $w) =>
    return ⟨w, q(by as_aux_lemma =>
      introv _ vp
      have ⟨_, A', B', f, s, _, w, eqt, eq⟩ := vp.inv_pair
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
      have ⟨_, A'', t, u, eq'⟩ := eqt.wf_right.inv_pair
      have ⟨_, _, _, Aeq', Beq'⟩ := eq'.inv_sigma
      replace t := t.conv Aeq'.symm_tp
      replace u := u.conv <| Beq'.symm_tp.subst (WfSb.toSb t)
      have feq : E ∣ Δ ⊢[l] f ≡ Expr.fst l l' A B p : A := by
        apply EqTm.fst_pair Beq.wf_left t u |>.symm_tm.trans_tm
        gcongr
        apply EqTm.trans_tm _ eqt.symm_tm
        gcongr <;> assumption
      replace w := w.conv_tp <| Beq.symm_tp.subst_eq (EqSb.toSb feq)
      apply w.conv_tm
      apply EqTm.snd_pair Beq.wf_left t u |>.symm_tm.conv_eq
        (Beq'.wf_left.subst_eq (EqSb.toSb feq)) |>.trans_tm _
      apply EqTm.symm_tm; gcongr
      apply eqt.trans_tm
      apply EqTm.symm_tm; gcongr <;> assumption
    )⟩
  | ~q(.neut $n (.sigma $k $k' $vA $vB)) => do
    let ⟨vf, vfpost⟩ ← evalFst q($vp)
    let ⟨vBfst, vBpost⟩ ← evalClosTp q($vB) q($vf)
    return ⟨q(.neut (.snd $k $k' $n) $vBfst), q(by as_aux_lemma =>
      introv _ vp
      have ⟨S, p⟩ := vp.inv_neut
      have ⟨_, _, _, vA, vB, eq⟩ := S.inv_sigma
      have ⟨_, _, _, Aeq, Beq⟩ := eq.inv_sigma
      subst_vars
      apply ValEqTm.neut_tm
      . have vf := $vfpost vp
        exact $vBpost vB (vf.conv_tp Aeq) |>.conv_tp (Beq.subst <| WfSb.toSb vf.wf_tm).symm_tp
      . apply NeutEqTm.snd p
    )⟩
  | vp => throwError "expected a normal form at type Σ, got{Lean.indentExpr vp}"

partial def evalIdRec (l' : Q(Nat)) (cM : Q(Clos $χ)) (vr vh : Q(Val $χ)) :
    Lean.MetaM ((v : Q(Val $χ)) × Q(∀ {E Δ A M t r u h l}, [Fact E.Wf] →
      Clos₂EqTp E Δ A l (.Id l (A.subst Expr.wk) (t.subst Expr.wk) (.bvar 0)) l $l' $cM M →
      ValEqTm E Δ $l' $vr r (M.subst (.snoc t.toSb <| .refl l t)) →
      ValEqTm E Δ l $vh h (.Id l A t u) →
      ValEqTm E Δ $l' $v (.idRec l $l' t M r u h) (M.subst (.snoc u.toSb h)))) :=
  match vh with
  | ~q(.refl $l $va) =>
    return ⟨vr, q(by as_aux_lemma =>
      introv _ cM vr vh
      have M := cM.wf_tp
      have ⟨_, _, _, va, eqt, eq⟩ := vh.inv_refl
      have ⟨_, _, _, tw, uw⟩ := eq.inv_Id
      subst_vars
      have tu := tw.trans_tm uw.symm_tm
      have t := tu.wf_left
      have := tu.symm_tm
      apply vr.conv_nf
      . apply EqTm.symm_tm
        apply EqTm.trans_tm _ <| EqTm.idRec_refl t M vr.wf_tm
        apply EqTm.symm_tm
        apply EqTm.cong_idRec (.refl_tm t) (.refl_tp M) (.refl_tm vr.wf_tm) tu
        refine ?eq
        apply EqTm.trans_tm _ <| eqt.symm_tm.conv_eq _ <;> gcongr; assumption
      . apply M.subst_eq <| EqSb.snoc (EqSb.toSb tu) (.Id_bvar t) (autosubst% ?eq)
    )⟩
  | ~q(.neut $nh (.Id $l $vA $va $vb)) => do
    let ⟨vT, vTpost⟩ ← evalClos₂Tp q($cM) q($vb) q($vh)
    return ⟨q(.neut (.idRec $l $l' $vA $va $cM $vr $nh) $vT), q(by as_aux_lemma =>
      introv _ cM vr vh
      have ⟨vId, nh⟩ := vh.inv_neut
      have ⟨_, _, _, _, vA, va, vb, eq⟩ := vId.inv_Id
      have ⟨_, _, _, teq, ueq⟩ := eq.inv_Id
      subst_vars
      have wA := vb.wf_tm.uniq_tp ueq.wf_right
      replace vb := vb.conv_nf (ueq.symm_tm.conv_eq wA.symm_tp) wA
      have := $vTpost cM vb (autosubst% vh)
      apply ValEqTm.neut_tm this
      apply NeutEqTm.idRec (vA.conv_tp wA) (va.conv_tp wA |>.conv_tm teq.symm_tm) cM vr nh
    )⟩
  | vh => throwError "expected a normal form at type Id, got{Lean.indentExpr vh}"

end

/-- Evaluate a type in the identity evaluation environment. -/
def evalTpId (vΓ : Q(TpEnv $χ)) (T : Q(Expr $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ l}, [Fact E.Wf] → TpEnvEqCtx E $vΓ Γ → (E ∣ Γ ⊢[l] ($T)) →
      ValEqTp E Γ l $v $T)) := do
  -- TODO: WHNF `envOfTpEnv`? I think not; it will need WHNFing later anyway
  -- (WHNF doesn't eval the args). Lean essentially forces us to lazily WHNF.
  let ⟨vT, vTpost⟩ ← evalTp q(envOfTpEnv $vΓ) q($T)
  return ⟨vT, q(by as_aux_lemma =>
    introv _ vΓ T
    convert ($vTpost (envOfTpEnv_wf vΓ) T) using 1; autosubst
  )⟩

/-- Evaluate a term in the identity evaluation environment. -/
def evalTmId (vΓ : Q(TpEnv $χ)) (t : Q(Expr $χ)) : Lean.MetaM ((v : Q(Val $χ)) ×
    Q(∀ {E Γ A l}, [Fact E.Wf] → TpEnvEqCtx E $vΓ Γ → (E ∣ Γ ⊢[l] ($t) : A) →
      ValEqTm E Γ l $v $t A)) := do
  let ⟨vt, vtpost⟩ ← evalTm q(envOfTpEnv $vΓ) q($t)
  return ⟨vt, q(by as_aux_lemma =>
    introv _ vΓ t
    convert ($vtpost (envOfTpEnv_wf vΓ) t) using 1 <;> autosubst
  )⟩
