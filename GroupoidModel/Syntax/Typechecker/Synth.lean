import GroupoidModel.Syntax.Typechecker.Equate

open Qq

partial def evalTp' (vΓ : Q(List Val)) (Γ : Q(Ctx)) (l : Q(Nat)) (T : Q(Expr))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) (ΓT : Q($Γ ⊢[$l] ($T))) :
    Lean.MetaM ((v : Q(Val)) × Q(ValEqTp $Γ $l $v $T)) := do
  -- TODO: WHNF `envOfTpEnv`?
  let ⟨vT, vTeq_⟩ ← evalTp Γ q(envOfTpEnv $vΓ) q(Expr.bvar) Γ l T q(envOfTpEnv_wf $vΓwf) q($ΓT)
  withHave vTeq_ fun vTeq => do
  return ⟨vT, ← mkHaves #[vTeq] q(by as_aux_lemma =>
    convert ($vTeq) using 1; autosubst
  )⟩

partial def lookup (Γ : Q(Ctx)) (i : Q(Nat)) :
    Lean.MetaM ((A : Q(Expr)) × (l : Q(Nat)) × Q(Lookup $Γ $i $A $l)) :=
  -- TODO: should this WHNF the weakening? See comment at `evalTp`.
  match i, Γ with
  | _, ~q([]) => throwError "bvar out of range: {i} ∉ {Γ}"
  | ~q(.zero), ~q(($A, $l) :: $Γ') => do
    return ⟨q(($A).subst Expr.wk), l, q(.zero $Γ' $A $l)⟩
  | ~q(.succ $i), ~q(($B, $l') :: $Γ') => do
    let ⟨A, l, lk⟩ ← lookup Γ' i
    return ⟨q(($A).subst Expr.wk), l, q(($lk).succ $B $l')⟩

mutual
-- TODO: infer rather than check universe level?
partial def checkTp (vΓ : Q(List Val)) (Γ : Q(Ctx)) (l : Q(Nat)) (T : Q(Expr))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) :
    Lean.MetaM Q($Γ ⊢[$l] ($T)) :=
  match T with
  | ~q(.pi $k $k' $A $B) => do
    let leq_ ← equateNat l q(max $k $k')
    withHave leq_ fun leq => do
    let Awf_ ← checkTp vΓ Γ k A vΓwf
    withHave Awf_ fun Awf => do
    let ⟨vA, vAeq_⟩ ← evalTp' vΓ Γ k A vΓwf Awf
    withHave vAeq_ fun vAeq => do
    let Bwf_ ← checkTp q($vA :: $vΓ) q(($A, $k) :: $Γ) k' B q(sorry)
    withHave Bwf_ fun Bwf => do
    mkHaves #[leq, Awf, vAeq, Bwf] q(by as_aux_lemma =>
      cases ($leq)
      exact WfTp.pi $Bwf
    )
  | ~q(.sigma $k $k' $A $B) => do
    let leq_ ← equateNat l q(max $k $k')
    withHave leq_ fun leq => do
    let Awf_ ← checkTp vΓ Γ k A vΓwf
    withHave Awf_ fun Awf => do
    let ⟨vA, vAeq_⟩ ← evalTp' vΓ Γ k A vΓwf Awf
    withHave vAeq_ fun vAeq => do
    let Bwf_ ← checkTp q($vA :: $vΓ) q(($A, $k) :: $Γ) k' B q(sorry)
    withHave Bwf_ fun Bwf => do
    mkHaves #[leq, Awf, vAeq, Bwf] q(by as_aux_lemma =>
      cases ($leq)
      exact WfTp.sigma $Bwf
    )
  | ~q(.univ $n) => do
    let ln_ ← equateNat l q($n + 1)
    withHave ln_ fun ln => do
    let nmax_ ← ltNat n q(univMax)
    withHave nmax_ fun nmax => do
    mkHaves #[ln, nmax] q(by as_aux_lemma =>
      cases ($ln)
      exact WfTp.univ ($vΓwf).wf_ctx $nmax
    )
  | ~q(.el $a) => do
    let lmax_ ← ltNat l q(univMax)
    withHave lmax_ fun lmax => do
    let awf_ ← checkTm vΓ Γ q($l + 1) a q(.univ $l) vΓwf q(.univ ($vΓwf).wf_ctx $lmax)
    withHave awf_ fun awf => do
    mkHaves #[lmax, awf] q(WfTp.el $awf)
  | _ =>
    throwError "not implemented: {Γ} ⊢[{l}]? {T}"

partial def checkTm
    (vΓ : Q(List Val)) (Γ : Q(Ctx)) (l : Q(Nat)) (t T : Q(Expr))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) (Twf : Q($Γ ⊢[$l] ($T))) :
    Lean.MetaM Q(($Γ ⊢[$l] ($t) : $T)) := do
  /- We could do something more bidirectional,
  but all terms synthesize (thanks to extensive annotations). -/
  withHave q(($Twf).wf_ctx) fun Γwf => do
  let ⟨U, tU_⟩ ← synthTm vΓ Γ l t vΓwf
  withHave tU_ fun tU => do
  let ⟨vT, vTeq_⟩ ← evalTp' vΓ Γ l T vΓwf q($Twf)
  withHave vTeq_ fun vTeq => do
  let ⟨vU, vUeq_⟩ ← evalTp' vΓ Γ l U vΓwf q(($tU).wf_tp)
  withHave vUeq_ fun vUeq => do
  let eq ← equateTp Γ l vU vT q(⟨_, $vUeq⟩) q(⟨_, $vTeq⟩)
  mkHaves #[Γwf, tU, vTeq, vUeq] q(by as_aux_lemma =>
    exact ($tU).conv <| ($eq).tp_uniq $vUeq $vTeq
  )

partial def synthTm (vΓ : Q(List Val)) (Γ : Q(Ctx)) (l : Q(Nat)) (t : Q(Expr))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) :
    Lean.MetaM ((T : Q(Expr)) × Q($Γ ⊢[$l] ($t) : $T)) :=
  match t with
  | ~q(.bvar $i) => do
    -- TODO: lookup in `vΓ` instead?
    let ⟨A, m, lk_⟩ ← lookup Γ i
    withHave lk_ fun lk => do
    let lm_ ← equateNat l m
    withHave lm_ fun lm => do
    return ⟨A, ← mkHaves #[lk, lm] q(by as_aux_lemma =>
      cases ($lm); exact WfTm.bvar ($vΓwf).wf_ctx $lk
    )⟩
  | ~q(.lam $k $k' $A $b) => do
    let Awf_ ← checkTp vΓ Γ k A vΓwf
    withHave Awf_ fun Awf => do
    let ⟨vA, vAeq_⟩ ← evalTp' vΓ Γ k A vΓwf Awf
    withHave vAeq_ fun vAeq => do
    let ⟨B, bB_⟩ ← synthTm q($vA :: $vΓ) q(($A, $k) :: $Γ) k' b q(sorry)
    withHave bB_ fun bB => do
    let lmax_ ← equateNat l q(max $k $k')
    withHave lmax_ fun lmax => do
    return ⟨q(.pi $k $k' $A $B), ← mkHaves #[Awf, vAeq, bB, lmax] q(by as_aux_lemma =>
      cases ($lmax)
      exact WfTm.lam $bB
    )⟩
  | ~q(.app $k $k' $B $f $a) => do
    let lk'_ ← equateNat l k'
    withHave lk'_ fun lk' => do
    let ⟨A, aA_⟩ ← synthTm vΓ Γ k a q($vΓwf)
    withHave aA_ fun aA => do
    -- TODO: if we synthesized NF types, then no need to eval here.
    -- may need to do that to avoid WHNFing `subst` below.
    let ⟨vA, vAeq_⟩ ← evalTp' vΓ Γ k A vΓwf q(sorry)
    withHave vAeq_ fun vAeq => do
    let Bwf_ ← checkTp q($vA :: $vΓ) q(($A, $k) :: $Γ) k' B q(sorry)
    withHave Bwf_ fun Bwf => do
    let fp_ ← checkTm vΓ Γ q(max $k $k') f q(.pi $k $k' $A $B) vΓwf q(.pi $Bwf)
    withHave fp_ fun fp => do
    let Ba : Q(Expr) := q(($B).subst ($a).toSb)
    /- FIXME: computing a substitution here! should `eval`.
    But if we evaluate, then we have to either:
    - implement readback to get back an `Expr`; or
    - return synthesized types in NF
      which requires a lot more calls to `eval`. -/
    let Ba' : Q(Expr) ← Lean.Meta.whnf Ba
    have _ : $Ba' =Q $Ba := .unsafeIntro
    return ⟨Ba', ← mkHaves #[lk', aA, vAeq, Bwf, fp] q(by as_aux_lemma =>
      cases ($lk')
      apply WfTm.app $fp $aA
    )⟩
  | ~q(.pair ..) | ~q(.fst ..) | ~q(.snd ..) =>
    throwError "not implemented: {Γ} ⊢[{l}] {t} : ?"
  | ~q(.code $A) => do
    -- TODO: WHNF `l`? See comment at `evalTp`.
    let ~q(.succ $k) := l | throwError "abcd"
    let lmax_ ← ltNat k q(univMax)
    withHave lmax_ fun lmax => do
    let Awf_ ← checkTp vΓ Γ k A vΓwf
    withHave Awf_ fun Awf => do
    return ⟨q(.univ $k), ← mkHaves #[lmax, Awf] q(WfTm.code $lmax $Awf)⟩
  | _ =>
    throwError "{t} is not a term in {Γ} ⊢[{l}] {t} : ?"
end
