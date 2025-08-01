import Qq

import GroupoidModel.Syntax.Synth
import GroupoidModel.Syntax.Typechecker.Value
import GroupoidModel.Syntax.Typechecker.Util

open Qq

/-! ## Evaluation -/

mutual
/-- Evaluate a type in an environment of values.

Note: we use `as_aux_lemma` pervasively to minimize the size of produced proof terms.
See also `withHave`. -/
/- TODO: is `withHave` still relevant with postcondition-only formulation?
If it is, because the proofs are not passed to subcalls anymore,
we can use `withHaves` instead.

But then we'd be calling `withHaves #[....] fun fs => mkHaves fs (mkAppM .. fs)`
which is obviously not doing anything! -/
partial def evalTp (env : Q(List Val)) (T' : Q(Expr)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ Δ σ l}, EnvEqSb Δ $env σ Γ → (Γ ⊢[l] ($T')) → ValEqTp Δ l $v (($T').subst σ))) := do
  /- TODO: establish a convention for when inputs are supposed to be in WHNF.
  Should `evalTp` reject types not in WHNF?
  Then we'd need to evaluate them in `lookup`,
  and other places where compound quotations are produced.
  On the other hand, lazy evaluation may be more efficient. -/
  let T : Q(Expr) ← Lean.Meta.whnf T'
  have _ : $T =Q $T' := .unsafeIntro
  match T with
  | ~q(.pi $l $l' $A $B) => do
    let ⟨vA, vApost_⟩ ← evalTp q($env) q($A)
    withHave vApost_ fun vApost => do
    let vT : Q(Val) := q(.pi $l $l' $vA (.of_expr $env $B))
    -- HACK: without the explicit annotation,
    -- `← mkHaves #[..] q(by _)` has an mvar for the goal at `_`.
    let pf : Q(∀ Γ Δ σ l, EnvEqSb Δ $env σ Γ → (Γ ⊢[l] ($T')) →
      ValEqTp Δ l $vT (($T').subst σ)) := q(by as_aux_lemma =>
        introv env T
        obtain ⟨rfl, B⟩ := T.inv_pi
        have vAeq := $vApost env B.wf_binder
        apply ValEqTp.pi vAeq
        apply ClosEqTp.clos_tp env (EqTp.refl_tp vAeq.wf_tp) B
      )
    return ⟨vT, ← mkHaves #[vApost] pf⟩
  | ~q(.sigma $l $l' $A $B) => do
    let ⟨vA, vApost_⟩ ← evalTp q($env) q($A)
    withHave vApost_ fun vApost => do
    let vT : Q(Val) := q(.sigma $l $l' $vA (.of_expr $env $B))
    -- HACK: without the explicit annotation,
    -- `← mkHaves #[..] q(by _)` has an mvar for the goal at `_`.
    let pf : Q(∀ Γ Δ σ l, EnvEqSb Δ $env σ Γ → (Γ ⊢[l] ($T')) →
      ValEqTp Δ l $vT (($T').subst σ)) := q(by as_aux_lemma =>
        introv env T
        obtain ⟨rfl, B⟩ := T.inv_sigma
        have vAeq := $vApost env B.wf_binder
        apply ValEqTp.sigma vAeq
        apply ClosEqTp.clos_tp env (EqTp.refl_tp vAeq.wf_tp) B
      )
    return ⟨vT, ← mkHaves #[vApost] pf⟩
  | ~q(.el $a) => do
    let ⟨va, vapost_⟩ ← evalTm q($env) q($a)
    withHave vapost_ fun vapost => do
    let vT : Q(Val) := q(.el $va)
    return ⟨vT, ← mkHaves #[vapost] q(by as_aux_lemma =>
      introv env T
      have := $vapost env T.inv_el
      exact ValEqTp.el this
    )⟩
  | ~q(.univ $l) =>
    let vT : Q(Val) := q(.univ $l)
    return ⟨vT, q(by as_aux_lemma =>
      introv env T
      cases T.inv_univ
      have := T.le_univMax
      exact ValEqTp.univ env.wf_dom (by omega)
    )⟩
  | T => throwError "expected a type, got{Lean.indentExpr T}"

/-- Evaluate a term in an environment of values. -/
partial def evalTm (env : Q(List Val)) (t' : Q(Expr)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ Δ σ A l}, EnvEqSb Δ $env σ Γ → (Γ ⊢[l] ($t') : A) →
      ValEqTm Δ l $v (($t').subst σ) (A.subst σ))) := do
  -- TODO: see comment at `evalTp`.
  let t : Q(Expr) ← Lean.Meta.whnf t'
  have _ : $t =Q $t' := .unsafeIntro
  match t with
  | ~q(.bvar $i) => do
    /- We evaluate the list access and error if a concrete element doesn't pop out.
    We do this (instead of producing e.g. `q($env[$i]? |>.getD default)`) to catch errors here,
    rather than when the value is weak-head normalized and inspected at a later point. -/
    let v : Q(Option Val) ← Lean.Meta.whnf q($env[$i]?)
    let ~q(some $v') := v
      | throwError "bvar {i} may be out of range in evaluation environment{Lean.indentExpr env}\n\
        note: expected 'some _', got{Lean.indentExpr v}"
    have : $v =Q $env[$i]? := .unsafeIntro -- FIXME: `whnfQ`?
    return ⟨v', q(by as_aux_lemma =>
      introv env t
      have ⟨_, lk, eq⟩ := t.inv_bvar
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert env.lookup_eq lk using 1
      subst $v
      have ⟨_, h⟩ := List.getElem?_eq_some_iff.mp ($this).symm
      rw [h]
    )⟩
  | ~q(.lam $k $k' $C $b) => do
    let ⟨vC, vCpost⟩ ← evalTp q($env) q($C)
    return ⟨q(.lam $k $k' $vC (.of_expr $env $b)),
      q(by as_aux_lemma =>
        introv env t
        obtain ⟨rfl, B, b, eq⟩ := t.inv_lam
        have C := b.wf_binder
        apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
        apply ValEqTm.lam ($vCpost env C) <| ClosEqTm.clos_tm env _ _ b
        . exact EqTp.refl_tp <| C.subst env.wf_sb
        . exact EqTp.refl_tp <| b.wf_tp.subst (env.wf_sb.up C)
      )⟩
  | ~q(.app $k $k' $B $f $a) => do
    let ⟨vf, vfpost_⟩ ← evalTm q($env) q($f)
    withHave vfpost_ fun vfpost => do
    let ⟨va, vapost_⟩ ← evalTm q($env) q($a)
    withHave vapost_ fun vapost => do
    let ⟨v, vpost_⟩ ← evalApp q($vf) q($va)
    withHave vpost_ fun vpost => do
    return ⟨v, ← mkHaves #[vfpost, vapost, vpost] q(by as_aux_lemma =>
      introv env t
      obtain ⟨rfl, _, f, a, eq⟩ := t.inv_app
      apply $vpost ($vfpost env f) ($vapost env a) |>.conv_tp
      convert eq.subst env.wf_sb |>.symm_tp using 1
      autosubst
    )⟩
  | ~q(.pair $k $k' $B $f $s) => do
    let ⟨vf, vfpost_⟩ ← evalTm q($env) q($f)
    withHave vfpost_ fun vfpost => do
    let ⟨vs, vspost_⟩ ← evalTm q($env) q($s)
    withHave vspost_ fun vspost => do
    let vp : Q(Val) := q(.pair $k $k' $vf $vs)
    return ⟨vp, ← mkHaves #[vfpost, vspost] q(by as_aux_lemma =>
      introv env t
      obtain ⟨rfl, _, t, u, eq⟩ := t.inv_pair
      have ⟨_, B⟩ := eq.wf_right.inv_sigma
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTm.pair (B.subst (env.wf_sb.up B.wf_binder)) ($vfpost env t)
      convert ($vspost env u) using 1
      autosubst
    )⟩
  | ~q(.fst $k $k' $A $B $p) => do
    let ⟨vp, vppost_⟩ ← evalTm q($env) q($p)
    withHave vppost_ fun vppost => do
    let ⟨v, vpost_⟩ ← evalFst q($vp)
    withHave vpost_ fun vpost => do
    return ⟨v, ← mkHaves #[vppost, vpost] q(by as_aux_lemma =>
      introv env t
      obtain ⟨rfl, p, eq⟩ := t.inv_fst
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      exact $vpost ($vppost env p)
    )⟩
  | ~q(.snd $k $k' $A $B $p) => do
    let ⟨vp, vppost_⟩ ← evalTm q($env) q($p)
    withHave vppost_ fun vppost => do
    let ⟨v, vpost_⟩ ← evalSnd q($vp)
    withHave vpost_ fun vpost => do
    return ⟨v, ← mkHaves #[vppost, vpost] q(by as_aux_lemma =>
      introv env t
      obtain ⟨rfl, p, eq⟩ := t.inv_snd
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ($vpost) ($vppost env p) using 1
      autosubst
    )⟩
  | ~q(.code $A) => do
    let ⟨vA, vApost_⟩ ← evalTp q($env) q($A)
    withHave vApost_ fun vApost => do
    let vc : Q(Val) := q(.code $vA)
    return ⟨vc, ← mkHaves #[vApost] q(by as_aux_lemma =>
      introv env t
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
partial def evalValTp (env : Q(List Val)) (vT : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ Δ A σ l}, EnvEqSb Δ $env σ Γ → ValEqTp Γ l $vT A → ValEqTp Δ l $v (A.subst σ))) := do
  match vT with
  | ~q(.pi $k $k' $vA $vB) =>
    let ⟨vB, vBpost_⟩ ← forceClosTp q(($env).length) q($vA) q($vB)
    withHave vBpost_ fun vBpost => do
    let ⟨vA, vApost_⟩ ← evalValTp q($env) q($vA)
    withHave vApost_ fun vApost => do
    let v : Q(Val) := q(.pi $k $k' $vA (.of_val $env $vB))
    return ⟨v, ← mkHaves #[vBpost, vApost] q(by as_aux_lemma =>
      introv env vT
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_pi
      subst_vars
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have vAσ := $vApost env vA
      apply ValEqTp.pi vAσ
      apply ClosEqTp.clos_val_tp env (EqTp.refl_tp vAσ.wf_tp) <|
        $vBpost env.eq_length vA vB
    )⟩
  | ~q(.sigma $k $k' $vA $vB) =>
    let ⟨vB, vBpost_⟩ ← forceClosTp q(($env).length) q($vA) q($vB)
    withHave vBpost_ fun vBpost => do
    let ⟨vA, vApost_⟩ ← evalValTp q($env) q($vA)
    withHave vApost_ fun vApost => do
    let v : Q(Val) := q(.sigma $k $k' $vA (.of_val $env $vB))
    return ⟨v, ← mkHaves #[vBpost, vApost] q(by as_aux_lemma =>
      introv env vT
      have ⟨_, _, _, vA, vB, eq⟩ := vT.inv_sigma
      subst_vars
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have vAσ := $vApost env vA
      apply ValEqTp.sigma vAσ
      apply ClosEqTp.clos_val_tp env (EqTp.refl_tp vAσ.wf_tp) <|
        $vBpost env.eq_length vA vB
    )⟩
  | ~q(.univ $l) => return ⟨q(.univ $l), q(by as_aux_lemma =>
      introv env vT
      have ⟨_, eq⟩ := vT.inv_univ
      have := eq.le_univMax
      subst_vars
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTp.univ env.wf_dom (by omega)
    )⟩
  | ~q(.el $va) =>
    let ⟨va, vapost_⟩ ← evalValTm q($env) q($va)
    withHave vapost_ fun vapost => do
    let v : Q(Val) := q(.el $va)
    return ⟨v, ← mkHaves #[vapost] q(by as_aux_lemma =>
      introv env vT
      have ⟨_, va, eq⟩ := vT.inv_el
      apply ValEqTp.conv_tp _ (eq.subst env.wf_sb).symm_tp
      apply ValEqTp.el ($vapost env va)
    )⟩
  | vT => throwError "expected a normal type, got{Lean.indentExpr vT}"

/-- Evaluate a term value in a new environment. -/
partial def evalValTm (env : Q(List Val)) (vt : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ Δ A t σ l}, EnvEqSb Δ $env σ Γ → ValEqTm Γ l $vt t A →
      ValEqTm Δ l $v (t.subst σ) (A.subst σ))) := do
  match vt with
  | ~q(.lam $k $k' $vA $b) =>
    -- NOTE: the binder type argument to `forceClosTm` is the only reason we annotate `Val.lam`.
    let ⟨vb, vbpost⟩ ← forceClosTm q(($env).length) q($vA) q($b)
    let ⟨vA, vApost⟩ ← evalValTp q($env) q($vA)
    return ⟨q(.lam $k $k' $vA (.of_val $env $vb)), q(by as_aux_lemma =>
      introv env vt
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
      introv env vt
      have ⟨_, _, _, _, _, vf, vs, eqt, eq⟩ := vt.inv_pair
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      have ⟨_, B⟩ := eq.wf_right.inv_sigma
      apply ValEqTm.pair (B.subst (env.wf_sb.up B.wf_binder)) ($vfpost env vf)
      convert ($vspost env vs) using 1; autosubst
    )⟩
  | ~q(.code $vA) =>
    let ⟨vA, vApost_⟩ ← evalValTp q($env) q($vA)
    withHave vApost_ fun vApost => do
    let v : Q(Val) := q(.code $vA)
    return ⟨v, ← mkHaves #[vApost] q(by as_aux_lemma =>
      introv env vt
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
      introv env vt
      have ⟨_, n⟩ := vt.inv_neut
      exact $vpost env n
    )⟩
  | vt => throwError "expected a normal term, got{Lean.indentExpr vt}"

/-- Evaluate a neutral term in a new environment. -/
partial def evalNeutTm (env : Q(List Val)) (nt : Q(Neut)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ Δ A t σ l}, EnvEqSb Δ $env σ Γ → NeutEqTm Γ l $nt t A →
      ValEqTm Δ l $v (t.subst σ) (A.subst σ))) := do
  match nt with
  | ~q(.bvar $i) =>
    let v : Q(Option Val) ← Lean.Meta.whnf q($env[($env).length - $i - 1]?)
    let ~q(some $v') := v
      | throwError "bvar {i} may be out of range in evaluation environment{Lean.indentExpr env}\n\
        note: expected 'some _', got{Lean.indentExpr v}"
    have : $v =Q $env[($env).length - $i - 1]? := .unsafeIntro -- FIXME: `whnfQ`?
    return ⟨v', q(by as_aux_lemma =>
      introv env nt
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
    let ⟨vf, vfpost_⟩ ← evalNeutTm q($env) q($nf)
    withHave vfpost_ fun vfpost => do
    let ⟨va, vapost_⟩ ← evalValTm q($env) q($va)
    withHave vapost_ fun vapost => do
    let ⟨v, vpost⟩ ← evalApp q($vf) q($va)
    return ⟨v, ← mkHaves #[vfpost, vapost] q(by as_aux_lemma =>
      introv env nt
      have ⟨_, _, _, _, _, _, nf, va, eqt, eq⟩ := nt.inv_app
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ($vpost ($vfpost env nf) ($vapost env va)) using 1
      autosubst
    )⟩
  | ~q(.fst $k $k' $np) =>
    let ⟨vp, vppost_⟩ ← evalNeutTm q($env) q($np)
    withHave vppost_ fun vppost => do
    let ⟨v, vpost⟩ ← evalFst q($vp)
    return ⟨v, ← mkHaves #[vppost, vpost] q(by as_aux_lemma =>
      introv env nt
      have ⟨_, _, _, _, np_eq, eqt, eq⟩ := nt.inv_fst
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      exact $vpost ($vppost env np_eq)
    )⟩
  | ~q(.snd $k $k' $np) =>
    let ⟨vp, vppost_⟩ ← evalNeutTm q($env) q($np)
    withHave vppost_ fun vppost => do
    let ⟨v, vpost⟩ ← evalSnd q($vp)
    return ⟨v, ← mkHaves #[vppost, vpost] q(by as_aux_lemma =>
      introv env nt
      have ⟨_, _, _, _, np_eq, eqt, eq⟩ := nt.inv_snd
      subst_vars
      apply ValEqTm.conv_tm _ (eqt.subst env.wf_sb).symm_tm
      apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
      convert ($vpost ($vppost env np_eq)) using 1
      autosubst
    )⟩
  | vt => throwError "expected a normal term, got{Lean.indentExpr vt}"

/-- Evaluate a type closure on an argument. -/
partial def evalClosTp (vB : Q(Clos)) (vt : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ A B t l l'}, ClosEqTp Γ l l' A $vB B → ValEqTm Γ l $vt t A →
      ValEqTp Γ l' $v (B.subst t.toSb))) := do
  match vB with
  | ~q(.of_expr $env $B) => do
    let ⟨v, vpost_⟩ ← evalTp q($vt :: $env) q($B)
    withHave vpost_ fun vpost => do
    let pf : Q(∀ {Γ A B t l l'}, ClosEqTp Γ l l' A $vB B → ValEqTm Γ l $vt t A →
          ValEqTp Γ l' $v (B.subst t.toSb)) := q(by as_aux_lemma =>
        introv vB vt
        simp +zetaDelta only at vB
        rcases vB with ⟨env, Aeq, B⟩
        convert ($vpost (env.snoc B.wf_binder (vt.conv_tp Aeq.symm_tp)) B) using 1
        autosubst
      )
    return ⟨v, ← mkHaves #[vpost] pf⟩
  | ~q(.of_val $env $vB') => do
    let ⟨v, vpost_⟩ ← evalValTp q($vt :: $env) q($vB')
    withHave vpost_ fun vpost => do
    return ⟨v, ← mkHaves #[vpost] q(by as_aux_lemma =>
      introv vB vt
      simp +zetaDelta only at vB
      rcases vB with _ | ⟨env, Aeq, B⟩
      have := env.snoc B.wf_tp.wf_binder (vt.conv_tp Aeq.symm_tp)
      convert ($vpost this B) using 1
      autosubst
    )⟩
  | vB => throwError "expected a type closure, got{Lean.indentExpr vB}"

/-- Evaluate a type closure on a fresh variable. -/
partial def forceClosTp (d : Q(Nat)) (vA : Q(Val)) (vB : Q(Clos)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ A B l l'}, $d = Γ.length → ValEqTp Γ l $vA A → ClosEqTp Γ l l' A $vB B →
      ValEqTp ((A, l) :: Γ) l' $v B)) := do
  let ⟨v, vpost_⟩ ← evalClosTp q($vB) q(.neut (.bvar $d) $vA)
  withHave vpost_ fun vpost => do
  let pf : Q(∀ {Γ A B l l'}, $d = Γ.length → ValEqTp Γ l $vA A → ClosEqTp Γ l l' A $vB B →
        ValEqTp ((A, l) :: Γ) l' $v B) := q(by as_aux_lemma =>
      introv deq vA vB
      replace vB := vB.wk vA.wf_tp
      replace vA := vA.wk vA.wf_tp
      have := NeutEqTm.bvar vA.wf_tp.wf_ctx (Lookup.zero ..)
      simp only [List.length_cons, ← deq, Nat.sub_zero, Nat.add_one_sub_one] at this
      have := ValEqTm.neut_tm vA this
      convert ($vpost vB this) using 1
      autosubst
    )
  return ⟨v, ← mkHaves #[vpost] pf⟩

/-- Evaluate a term closure on an argument. -/
partial def evalClosTm (vb : Q(Clos)) (vt : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ A B b t l l'}, ClosEqTm Γ l l' A B $vb b → ValEqTm Γ l $vt t A →
      ValEqTm Γ l' $v (b.subst t.toSb) (B.subst t.toSb))) := do
  match vb with
  | ~q(.of_expr $env $b) => do
    let ⟨v, vpost_⟩ ← evalTm q($vt :: $env) q($b)
    withHave vpost_ fun vpost => do
    let pf : Q(∀ {Γ A B b t l l'}, ClosEqTm Γ l l' A B $vb b → ValEqTm Γ l $vt t A →
          ValEqTm Γ l' $v (b.subst t.toSb) (B.subst t.toSb)) := q(by as_aux_lemma =>
        introv vb vt
        simp +zetaDelta only at vb
        rcases vb with ⟨env, Aeq, Beq, b⟩
        have := env.snoc b.wf_binder (vt.conv_tp Aeq.symm_tp)
        have Beq := Beq.subst <| WfSb.toSb vt.wf_tm
        convert ($vpost this b |>.conv_tp (by convert Beq using 1; autosubst)) using 1
        autosubst
      )
    return ⟨v, ← mkHaves #[vpost] pf⟩
  | ~q(.of_val $env $vb') => do
    let ⟨v, vpost_⟩ ← evalValTm q($vt :: $env) q($vb')
    withHave vpost_ fun vpost => do
    return ⟨v, ← mkHaves #[vpost] q(by as_aux_lemma =>
      introv vb vt
      simp +zetaDelta only at vb
      rcases vb with _ | ⟨env, Aeq, Beq, b⟩
      have := env.snoc b.wf_tm.wf_binder (vt.conv_tp Aeq.symm_tp)
      have Beq := Beq.subst <| WfSb.toSb vt.wf_tm
      convert ($vpost this b |>.conv_tp (by convert Beq using 1; autosubst)) using 1
      autosubst
    )⟩
  | vB => throwError "expected a type closure, got{Lean.indentExpr vB}"

/-- Evaluate a term closure on a fresh variable. -/
partial def forceClosTm (d : Q(Nat)) (vA : Q(Val)) (vb : Q(Clos)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ A B b l l'}, $d = Γ.length → ValEqTp Γ l $vA A → ClosEqTm Γ l l' A B $vb b →
      ValEqTm ((A, l) :: Γ) l' $v b B)) := do
  let ⟨v, vpost_⟩ ← evalClosTm q($vb) q(.neut (.bvar $d) $vA)
  withHave vpost_ fun vpost => do
  let pf : Q(∀ {Γ A B b l l'}, $d = Γ.length → ValEqTp Γ l $vA A → ClosEqTm Γ l l' A B $vb b →
        ValEqTm ((A, l) :: Γ) l' $v b B) := q(by as_aux_lemma =>
      introv deq vA vb
      replace vb := vb.wk vA.wf_tp
      replace vA := vA.wk vA.wf_tp
      have := NeutEqTm.bvar vA.wf_tp.wf_ctx (Lookup.zero ..)
      simp only [List.length_cons, ← deq, Nat.sub_zero, Nat.add_one_sub_one] at this
      have := ValEqTm.neut_tm vA this
      convert ($vpost vb this) using 1 <;> autosubst
    )
  return ⟨v, ← mkHaves #[vpost] pf⟩

partial def evalApp (vf va : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Δ A B f a l l'}, ValEqTm Δ (max l l') $vf f (.pi l l' A B) → ValEqTm Δ l $va a A →
      ValEqTm Δ l' $v (.app l l' B f a) (B.subst a.toSb))) :=
  match vf with
  | ~q(.lam $k $k' _ $vb) => do
    let ⟨v, vpost_⟩ ← evalClosTm q($vb) q($va)
    withHave vpost_ fun vpost => do
    let pf : Q(∀ {Δ A B f a l l'},
          ValEqTm Δ (max l l') $vf f (.pi l l' A B) → ValEqTm Δ l $va a A →
          ValEqTm Δ l' $v (.app l l' B f a) (B.subst a.toSb)) := q(by as_aux_lemma =>
        introv vf va
        have ⟨_, _, _, _, _, vb, eqt, eq⟩ := vf.inv_lam
        have ⟨_, _, _, Aeq, Beq⟩ := eq.inv_pi
        subst_vars
        have := $vpost vb (va.conv_tp Aeq) |>.conv_tp (Beq.subst <| WfSb.toSb va.wf_tm).symm_tp
        apply this.conv_tm
        have b := vb.wf_tm |>.conv_binder Aeq.symm_tp |>.conv Beq.symm_tp
        apply (EqTm.app_lam b va.wf_tm).symm_tm.trans_tm
        apply EqTm.cong_app (EqTp.refl_tp b.wf_tp) _ (EqTm.refl_tm va.wf_tm)
        symm; apply eqt.trans_tm
        symm; gcongr
        assumption
      )
    return ⟨v, ← mkHaves #[vpost] pf⟩
  | ~q(.neut $n (.pi $k $k' $vA $vB)) => do
    let ⟨vBa, vBpost_⟩ ← evalClosTp q($vB) q($va)
    withHave vBpost_ fun vBpost => do
    let v : Q(Val) := q(.neut (.app $k $k' $vA $n $va) $vBa)
    let pf : Q(∀ {Δ A B f a l l'},
          ValEqTm Δ (max l l') $vf f (.pi l l' A B) → ValEqTm Δ l $va a A →
          ValEqTm Δ l' $v (.app l l' B f a) (B.subst a.toSb)) := q(by as_aux_lemma =>
        introv vf va
        have ⟨P, n⟩ := vf.inv_neut
        have ⟨_, _, _, vA, vB, eq⟩ := P.inv_pi
        have ⟨_, _, _, Aeq, Beq⟩ := eq.inv_pi
        subst_vars
        have := $vBpost vB (va.conv_tp Aeq) |>.conv_tp (Beq.subst <| WfSb.toSb va.wf_tm).symm_tp
        apply ValEqTm.neut_tm this
        apply NeutEqTm.app (vA.conv_tp Aeq.symm_tp) n va
      )
    return ⟨v, ← mkHaves #[vBpost] pf⟩
  | vf => throwError "expected a normal form at type Π, got{Lean.indentExpr vf}"

partial def evalFst (vp : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Δ A B p l l'}, ValEqTm Δ (max l l') $vp p (.sigma l l' A B) →
      ValEqTm Δ l $v (.fst l l' A B p) A)) :=
  match vp with
  | ~q(.pair _ _ $v _) =>
    return ⟨v, q(by as_aux_lemma =>
      introv vp
      have ⟨_, A', B', f, s, v, _, eqt, eq⟩ := vp.inv_pair
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
      have : Δ ⊢[l] f ≡ Expr.fst l l' A B p : A := by
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
      introv vp
      have ⟨S, p⟩ := vp.inv_neut
      have ⟨_, _, _, vA, vB, eq⟩ := S.inv_sigma
      obtain ⟨_, rfl, rfl, Aeq, _⟩ := eq.inv_sigma
      apply ValEqTm.neut_tm (vA.conv_tp Aeq.symm_tp) (NeutEqTm.fst p)
    )⟩
  | vp => throwError "expected a normal form at type Σ, got{Lean.indentExpr vp}"

partial def evalSnd (vp : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Δ A B p l l'}, ValEqTm Δ (max l l') $vp p (.sigma l l' A B) →
      ValEqTm Δ l' $v (.snd l l' A B p) (B.subst (Expr.fst l l' A B p).toSb))) :=
  match vp with
  | ~q(.pair _ _ _ $w) =>
    return ⟨w, q(by as_aux_lemma =>
      introv vp
      have ⟨_, A', B', f, s, _, w, eqt, eq⟩ := vp.inv_pair
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
      have ⟨_, A'', t, u, eq'⟩ := eqt.wf_right.inv_pair
      have ⟨_, _, _, Aeq', Beq'⟩ := eq'.inv_sigma
      replace t := t.conv Aeq'.symm_tp
      replace u := u.conv <| Beq'.symm_tp.subst (WfSb.toSb t)
      have feq : Δ ⊢[l] f ≡ Expr.fst l l' A B p : A := by
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
  | ~q(.neut $n (.sigma $k $k' $vA $vB)) => do
    let ⟨vf, vfpost_⟩ ← evalFst q($vp)
    withHave vfpost_ fun vfpost => do
    let ⟨vBfst, vBpost_⟩ ← evalClosTp q($vB) q($vf)
    withHave vBpost_ fun vBpost => do
    let n : Q(Val) := q(.neut (.snd $k $k' $n) $vBfst)
    return ⟨n, ← mkHaves #[vfpost, vBpost] q(by as_aux_lemma =>
      introv vp
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
end

/-- Evaluate a type in the identity evaluation environment. -/
def evalTpId (vΓ : Q(TpEnv)) (T : Q(Expr)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ l}, TpEnvEqCtx $vΓ Γ → (Γ ⊢[l] ($T)) → ValEqTp Γ l $v $T)) := do
  -- TODO: WHNF `envOfTpEnv`? I think not; it will need WHNFing later anyway
  -- (WHNF doesn't eval the args). Lean essentially forces us to lazily WHNF.
  let ⟨vT, vTpost_⟩ ← evalTp q(envOfTpEnv $vΓ) q($T)
  withHave vTpost_ fun vTpost => do
  return ⟨vT, ← mkHaves #[vTpost] q(by as_aux_lemma =>
    introv vΓ T
    convert ($vTpost (envOfTpEnv_wf vΓ) T) using 1; autosubst
  )⟩

/-- Evaluate a term in the identity evaluation environment. -/
def evalTmId (vΓ : Q(TpEnv)) (t : Q(Expr)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ A l}, TpEnvEqCtx $vΓ Γ → (Γ ⊢[l] ($t) : A) → ValEqTm Γ l $v $t A)) := do
  let ⟨vt, vtpost_⟩ ← evalTm q(envOfTpEnv $vΓ) q($t)
  withHave vtpost_ fun vtpost => do
  return ⟨vt, ← mkHaves #[vtpost] q(by as_aux_lemma =>
    introv vΓ t
    convert ($vtpost (envOfTpEnv_wf vΓ) t) using 1 <;> autosubst
  )⟩
