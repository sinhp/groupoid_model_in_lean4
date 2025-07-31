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
    let vT : Q(Val) := q(.pi $l $l' $vA (.mk_tp $env $B))
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
    let vT : Q(Val) := q(.sigma $l $l' $vA (.mk_tp $env $B))
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
    return ⟨q(.lam $k $k' (.mk_tm $env $b)),
      q(by as_aux_lemma =>
        introv env t
        obtain ⟨rfl, B, b, eq⟩ := t.inv_lam
        have C := b.wf_binder
        apply ValEqTm.conv_tp _ (eq.subst env.wf_sb).symm_tp
        apply ValEqTm.lam <| ClosEqTm.clos_tm env _ _ b
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

partial def evalApp (vf va : Q(Val)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Δ A B f a l l'}, ValEqTm Δ (max l l') $vf f (.pi l l' A B) → ValEqTm Δ l $va a A →
      ValEqTm Δ l' $v (.app l l' B f a) (B.subst a.toSb))) :=
  match vf with
  | ~q(.lam $k $k' (.mk_tm $env $b)) => do
    let ⟨v, vpost_⟩ ← evalTm q($va :: $env) q($b)
    withHave vpost_ fun vpost => do
    let pf : Q(∀ {Δ A B f a l l'},
          ValEqTm Δ (max l l') $vf f (.pi l l' A B) → ValEqTm Δ l $va a A →
          ValEqTm Δ l' $v (.app l l' B f a) (B.subst a.toSb)) := q(by as_aux_lemma =>
        introv vf va
        have ⟨_, _, _, _, ⟨env, Aeq', Beq', b⟩, eqt, eq⟩ := vf.inv_lam
        obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_pi
        -- normalize to A, B
        replace Beq' := Beq'.conv_binder Aeq.symm_tp
        replace Aeq := Aeq.trans_tp Aeq'.symm_tp
        replace Beq := Beq.trans_tp Beq'.symm_tp
        -- apply postcondition
        have := env.snoc b.wf_binder (va.conv_tp Aeq)
        have veq := $vpost this b |>.conv_tp
          (by convert Beq.subst (WfSb.toSb va.wf_tm) |>.symm_tp using 1; autosubst)
        apply veq.conv_tm
        -- convert term
        replace b := b.subst (env.wf_sb.up b.wf_binder) |>.conv_binder Aeq.symm_tp
          |>.conv Beq.symm_tp
        convert (EqTm.app_lam b va.wf_tm).symm_tm.trans_tm _ using 1
        . autosubst
        apply EqTm.cong_app (EqTp.refl_tp Beq.wf_left) _ (EqTm.refl_tm va.wf_tm)
        symm; apply eqt.trans_tm
        symm; gcongr
        . assumption
        . exact Aeq.trans_tp Aeq'
      )
    return ⟨v, ← mkHaves #[vpost] pf⟩
  | ~q(.neut $n (.pi $k $k' $vA (.mk_tp $env $B))) => do
    let ⟨vBa, vBpost_⟩ ← evalTp q($va :: $env) q($B)
    withHave vBpost_ fun vBpost => do
    let v : Q(Val) := q(.neut (.app $k $k' $vA $n $va) $vBa)
    let pf : Q(∀ {Δ A B f a l l'},
          ValEqTm Δ (max l l') $vf f (.pi l l' A B) → ValEqTm Δ l $va a A →
          ValEqTm Δ l' $v (.app l l' B f a) (B.subst a.toSb)) := q(by as_aux_lemma =>
        introv vf va
        have ⟨P, n⟩ := vf.inv_neut
        have ⟨_, _, _, vA, ⟨env, Aeq', B⟩, eq⟩ := P.inv_pi
        obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_pi

        replace vA := vA.conv_tp Aeq.symm_tp
        replace Aeq := Aeq.trans_tp Aeq'.symm_tp
        have := env.snoc B.wf_binder (va.conv_tp Aeq)
        have := $vBpost this B |>.conv_tp
          (by convert Beq.subst (WfSb.toSb va.wf_tm) |>.symm_tp using 1; autosubst)
        apply ValEqTm.neut_tm this
        apply NeutEqTm.app vA n va
      )
    return ⟨v, ← mkHaves #[vBpost] pf⟩
  | vf => throwError "expected normal form at type Π, got{Lean.indentExpr vf}"

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
  | vp => throwError "expected normal form at type Σ, got{Lean.indentExpr vp}"

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
  | ~q(.neut $n (.sigma $k $k' $vA (.mk_tp $env $B))) => do
    let ⟨vf, vfpost_⟩ ← evalFst q($vp)
    withHave vfpost_ fun vfpost => do
    let ⟨vBfst, vBpost_⟩ ← evalTp q($vf :: $env) q($B)
    withHave vBpost_ fun vBpost => do
    let n : Q(Val) := q(.neut (.snd $k $k' $n) $vBfst)
    return ⟨n, ← mkHaves #[vfpost, vBpost] q(by as_aux_lemma =>
      introv vp
      have ⟨S, p⟩ := vp.inv_neut
      have ⟨_, _, _, vA, ⟨env, Aeq', B⟩, eq⟩ := S.inv_sigma
      obtain ⟨_, rfl, rfl, Aeq, Beq⟩ := eq.inv_sigma
      apply ValEqTm.neut_tm
      . have vf := $vfpost vp
        have := $vBpost (env.snoc B.wf_binder (vf.conv_tp <| Aeq.trans_tp Aeq'.symm_tp)) B
        apply this.conv_tp
        convert Beq.symm_tp.subst (WfSb.toSb vf.wf_tm) using 1
        autosubst
      . apply NeutEqTm.snd p
    )⟩
  | vp => throwError "expected normal form at type Σ, got{Lean.indentExpr vp}"
end

/-- Evaluate a type closure on a fresh variable. -/
def evalClosTp (d : Q(Nat)) (vA : Q(Val)) (vB : Q(Clos)) : Lean.MetaM ((v : Q(Val)) ×
    Q(∀ {Γ A B l l'}, $d = Γ.length → ValEqTp Γ l $vA A → ClosEqTp Γ l l' A $vB B →
      ValEqTp ((A, l) :: Γ) l' $v B)) := do
  let ~q(.mk_tp $env $B) := vB | throwError "expected a type closure, got{Lean.indentExpr vB}"
  let x : Q(Val) := q(.neut (.bvar $d) $vA)
  let ⟨v, vpost_⟩ ← evalTp q($x :: $env) q($B)
  withHave vpost_ fun vpost => do
  let pf : Q(∀ {Γ A B l l'}, $d = Γ.length → ValEqTp Γ l $vA A → ClosEqTp Γ l l' A $vB B →
        ValEqTp ((A, l) :: Γ) l' $v B) := q(by as_aux_lemma =>
      introv deq vA
      simp +zetaDelta only
      rintro ⟨env, Aeq, B⟩
      replace env := env.wk vA.wf_tp
      have := NeutEqTm.bvar env.wf_dom (Lookup.zero ..)
      simp only [List.length_cons, ← deq, Nat.sub_zero, Nat.add_one_sub_one] at this
      have := ValEqTm.neut_tm (vA.wk vA.wf_tp) this
      have := env.snoc B.wf_binder <|
        by convert this.conv_tp <| Aeq.symm_tp.subst (WfSb.wk vA.wf_tp) using 1; autosubst
      convert ($vpost this B) using 1
      autosubst
    )
  return ⟨v, ← mkHaves #[vpost] pf⟩

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
