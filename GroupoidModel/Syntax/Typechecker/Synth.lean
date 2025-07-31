import GroupoidModel.Syntax.Typechecker.Equate

open Qq

partial def lookup (vΓ : Q(TpEnv)) (i : Q(Nat)) : Lean.MetaM ((vA : Q(Val)) × (l : Q(Nat)) ×
    Q(∀ {Γ}, TpEnvEqCtx $vΓ Γ → ∃ A, ValEqTp Γ $l $vA A ∧ Lookup Γ $i A $l)) :=
  match i, vΓ with
  | _, ~q([]) => throwError "bvar {i} out of range in type environment{Lean.indentExpr vΓ}"
  | ~q(.zero), ~q(($vA, $l) :: _) => do
    return ⟨q($vA), q($l), q(by as_aux_lemma =>
      introv vΓ
      simp +zetaDelta only at vΓ
      rcases vΓ with _ | ⟨vΓ, vA⟩
      exact ⟨_, vA.wk vA.wf_tp, Lookup.zero ..⟩
    )⟩
  | ~q($i' + 1), ~q(_ :: $vΓ') => do
    let ⟨vA, l, pf⟩ ← lookup q($vΓ') q($i')
    return ⟨q($vA), q($l), q(by as_aux_lemma =>
      introv vΓ
      simp +zetaDelta only at vΓ ⊢
      rcases vΓ with _ | ⟨vΓ', vB⟩
      have ⟨_, vA, lk⟩ := $pf vΓ'
      exact ⟨_, vA.wk vB.wf_tp, lk.succ ..⟩
    )⟩

mutual
partial def checkTp (vΓ : Q(TpEnv)) (l : Q(Nat)) (T : Q(Expr)) :
    Lean.MetaM Q(∀ {Γ}, TpEnvEqCtx $vΓ Γ → Γ ⊢[$l] ($T)) :=
  match T with
  | ~q(.pi $k $k' $A $B) => do
    let leq_ ← equateNat q($l) q(max $k $k')
    withHave leq_ fun leq => do
    let Awf_ ← checkTp q($vΓ) q($k) A
    withHave Awf_ fun Awf => do
    let ⟨vA, vAeq_⟩ ← evalTpId q($vΓ) q($A)
    withHave vAeq_ fun vAeq => do
    let Bwf_ ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    withHave Bwf_ fun Bwf => do
    mkHaves #[leq, Awf, vAeq, Bwf] q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      apply WfTp.pi <| $Bwf <| vΓ.snoc <| $vAeq vΓ <| $Awf vΓ
    )
  | ~q(.sigma $k $k' $A $B) => do
    let leq_ ← equateNat q($l) q(max $k $k')
    withHave leq_ fun leq => do
    let Awf_ ← checkTp q($vΓ) q($k) A
    withHave Awf_ fun Awf => do
    let ⟨vA, vAeq_⟩ ← evalTpId q($vΓ) q($A)
    withHave vAeq_ fun vAeq => do
    let Bwf_ ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    withHave Bwf_ fun Bwf => do
    mkHaves #[leq, Awf, vAeq, Bwf] q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      apply WfTp.sigma <| $Bwf <| vΓ.snoc <| $vAeq vΓ <| $Awf vΓ
    )
  | ~q(.univ $n) => do
    let ln_ ← equateNat q($l) q($n + 1)
    withHave ln_ fun ln => do
    let nmax_ ← ltNat q($n) q(univMax)
    withHave nmax_ fun nmax => do
    mkHaves #[ln, nmax] q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      apply WfTp.univ vΓ.wf_ctx $nmax
    )
  | ~q(.el $a) => do
    let lmax_ ← ltNat q($l) q(univMax)
    withHave lmax_ fun lmax => do
    let awf_ ← checkTm q($vΓ) q($l + 1) q(.univ $l) q($a)
    withHave awf_ fun awf => do
    mkHaves #[lmax, awf] q(by as_aux_lemma =>
      introv vΓ
      simp +zetaDelta only
      apply WfTp.el <| $awf vΓ (ValEqTp.univ vΓ.wf_ctx $lmax)
    )
  | T => throwError "expected a type, got{Lean.indentExpr T}"

partial def checkTm (vΓ : Q(TpEnv)) (l : Q(Nat)) (vT : Q(Val)) (t : Q(Expr)) :
    Lean.MetaM Q(∀ {Γ T}, TpEnvEqCtx $vΓ Γ → ValEqTp Γ $l $vT T → Γ ⊢[$l] ($t) : T) := do
  /- We could do something more bidirectional,
  but all terms synthesize (thanks to extensive annotations). -/
  let ⟨vU, tU_⟩ ← synthTm q($vΓ) q($l) q($t)
  withHave tU_ fun tU => do
  let eq ← equateTp q(($vΓ).length) q($l) q($vU) q($vT)
  mkHaves #[tU] q(by as_aux_lemma =>
    introv vΓ vT
    have ⟨_, vU, t⟩ := $tU vΓ
    apply t.conv <| $eq vΓ.length_eq vU vT
  )

-- TODO: infer rather than check universe level?
partial def synthTm (vΓ : Q(TpEnv)) (l : Q(Nat)) (t : Q(Expr)) : Lean.MetaM ((vT : Q(Val)) ×
    Q(∀ {Γ}, TpEnvEqCtx $vΓ Γ → ∃ T, ValEqTp Γ $l $vT T ∧ (Γ ⊢[$l] ($t) : T))) :=
  match t with
  | ~q(.bvar $i) => do
    let ⟨vA, m, lk⟩ ← lookup q($vΓ) q($i)
    let lm ← equateNat q($l) q($m)
    return ⟨vA, q(by as_aux_lemma =>
      introv vΓ
      have ⟨_, vA, lk⟩ := $lk vΓ
      subst_vars
      exact ⟨_, vA, WfTm.bvar vΓ.wf_ctx lk⟩
    )⟩
  | ~q(.lam $k $k' $A $b) => do
    let Awf_ ← checkTp q($vΓ) q($k) q($A)
    withHave Awf_ fun Awf => do
    let ⟨vA, vAeq_⟩ ← evalTpId q($vΓ) q($A)
    withHave vAeq_ fun vAeq => do
    let ⟨vB, bB_⟩ ← synthTm q(($vA, $k) :: $vΓ) q($k') q($b)
    withHave bB_ fun bB => do
    let lmax_ ← equateNat q($l) q(max $k $k')
    withHave lmax_ fun lmax => do
    /- TODO: we currently cannot synthesize the type of a lambda because we don't know `B`. options:
    1. readback from `vB`
    2. store the codomain in `Expr.lam`
    3. add bidirectional-style `coe` to `Expr` -/
    let vP : Q(Val) := q(.pi $k $k' $vA (.mk_tp (envOfTpEnv $vΓ) sorry))
    let pf : Q(∀ {Γ}, TpEnvEqCtx $vΓ Γ → ∃ T, ValEqTp Γ $l $vP T ∧ (Γ ⊢[$l] ($t) : T)) :=
      q(by as_aux_lemma =>
        introv vΓ
        subst_vars
        have A := $Awf vΓ
        have vA := $vAeq vΓ A
        have ⟨B, vB, b⟩ := $bB (vΓ.snoc vA)
        refine ⟨.pi $k $k' $A B, ?_, WfTm.lam b⟩
        apply ValEqTp.pi vA
        convert ClosEqTp.clos_tp (envOfTpEnv_wf vΓ) _ b.wf_tp using 1
        . congr 1; sorry
        . autosubst
        . convert EqTp.refl_tp A using 1; autosubst
      )
    return ⟨vP, ← mkHaves #[Awf, vAeq, bB, lmax] pf⟩
  | ~q(.app $k $k' $B $f $a) => do
    let lk'_ ← equateNat q($l) q($k')
    withHave lk'_ fun lk' => do
    let ⟨vA, vApost_⟩ ← synthTm q($vΓ) q($k) q($a)
    withHave vApost_ fun vApost => do
    let Bwf_ ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    withHave Bwf_ fun Bwf => do
    let fwf_ ← checkTm q($vΓ) q(max $k $k') q(.pi $k $k' $vA (.mk_tp (envOfTpEnv $vΓ) $B)) q($f)
    withHave fwf_ fun fwf => do
    let ⟨va, vaeq_⟩ ← evalTmId q($vΓ) q($a)
    withHave vaeq_ fun vaeq => do
    let ⟨vBa, vBaeq_⟩ ← evalTp q($va :: envOfTpEnv $vΓ) q($B)
    withHave vBaeq_ fun vBaeq => do
    return ⟨vBa, ← mkHaves #[lk', vApost, Bwf, fwf, vaeq, vBaeq] q(by as_aux_lemma =>
      introv vΓ
      have ⟨_, vA, a⟩ := $vApost vΓ
      have B := $Bwf <| vΓ.snoc vA
      have f := $fwf vΓ <| ValEqTp.pi vA <|
        ClosEqTp.clos_tp (envOfTpEnv_wf vΓ) (by convert EqTp.refl_tp a.wf_tp using 1; autosubst) B
      have va := $vaeq vΓ a
      have := (envOfTpEnv_wf vΓ).snoc va.wf_tm.wf_tp (by convert va using 1; autosubst)
      subst_vars
      refine ⟨_, $vBaeq this B, ?_⟩
      convert WfTm.app f a using 1 <;> simp +zetaDelta only [autosubst]
    )⟩
  | ~q(.pair $k $k' $B $f $s) => do
    let lmax_ ← equateNat q($l) q(max $k $k')
    withHave lmax_ fun lmax => do
    let ⟨vA, fA_⟩ ← synthTm q($vΓ) q($k) q($f)
    withHave fA_ fun fA => do
    let Bwf_ ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    withHave Bwf_ fun Bwf => do
    let ⟨vf, vfpost_⟩ ← evalTmId q($vΓ) q($f)
    withHave vfpost_ fun vfpost => do
    let ⟨vBf, vBfpost_⟩ ← evalTp q($vf :: envOfTpEnv $vΓ) q($B)
    withHave vBfpost_ fun vBfpost => do
    let swf_ ← checkTm q($vΓ) q($k') q($vBf) q($s)
    withHave swf_ fun swf => do
    let vT : Q(Val) := q(.sigma $k $k' $vA (.mk_tp (envOfTpEnv $vΓ) $B))
    return ⟨vT, ← mkHaves #[lmax, fA, Bwf, vfpost, vBfpost, swf] q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have ⟨_, vA, f⟩ := $fA vΓ
      have B := $Bwf <| vΓ.snoc vA
      have vf := $vfpost vΓ f
      have vBf := $vBfpost ((envOfTpEnv_wf vΓ).snoc f.wf_tp (by convert vf using 1; autosubst)) B
      have s := $swf vΓ vBf
      have := ValEqTp.sigma vA <|
        ClosEqTp.clos_tp (envOfTpEnv_wf vΓ) (by convert EqTp.refl_tp vA.wf_tp using 1; autosubst) B
      refine ⟨_, this, ?_⟩
      simp +zetaDelta only [autosubst]
      apply WfTm.pair B f s
    )⟩
  | ~q(.fst ..) | ~q(.snd ..) =>
    throwError "TODO: fst and snd"
  | ~q(.code $A) => do
    -- TODO: WHNF `l`? See comment at `evalTp`.
    let ~q(.succ $k) := l | throwError "expected _+1, got{Lean.indentExpr l}"
    let lmax_ ← ltNat q($k) q(univMax)
    withHave lmax_ fun lmax => do
    let Awf_ ← checkTp q($vΓ) q($k) q($A)
    withHave Awf_ fun Awf => do
    let vU : Q(Val) := q(.univ $k)
    return ⟨vU, ← mkHaves #[lmax, Awf] q(by as_aux_lemma =>
      introv vΓ
      exact ⟨_, ValEqTp.univ vΓ.wf_ctx $lmax, WfTm.code $lmax ($Awf vΓ)⟩
    )⟩
  | t =>
    throwError "expected a term, got{Lean.indentExpr t}"
end
