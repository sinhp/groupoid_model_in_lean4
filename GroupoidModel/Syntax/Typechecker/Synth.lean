import GroupoidModel.Syntax.Typechecker.Equate

open Qq

-- partial def lookup (vΓ : Q(TpEnv)) (Γ : Q(Ctx)) (i : Q(Nat)) :
--     Lean.MetaM ((vA : Q(Val)) × (l : Q(Nat)) × Q(Lookup $Γ $i $A $l)) :=
--   -- TODO: should this WHNF the weakening? See comment at `evalTp`.
--   sorry
  -- match i, Γ with
  -- | _, ~q([]) => throwError "bvar out of range: {i} ∉ {Γ}"
  -- | ~q(.zero), ~q(($A, $l) :: $Γ') => do
  --   return ⟨q(($A).subst Expr.wk), l, q(.zero $Γ' $A $l)⟩
  -- | ~q(.succ $i), ~q(($B, $l') :: $Γ') => do
  --   let ⟨A, l, lk⟩ ← lookup Γ' i
  --   return ⟨q(($A).subst Expr.wk), l, q(($lk).succ $B $l')⟩

mutual
-- TODO: infer rather than check universe level?
partial def checkTp (vΓ : Q(TpEnv)) (Γ : Q(Ctx)) (l : Q(Nat)) (T : Q(Expr))
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
    let Bwf_ ← checkTp q(($vA, $k) :: $vΓ) q(($A, $k) :: $Γ) k' B q(($vΓwf).snoc $vAeq)
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
    let Bwf_ ← checkTp q(($vA, $k) :: $vΓ) q(($A, $k) :: $Γ) k' B q(($vΓwf).snoc $vAeq)
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
    let awf_ ← checkTm vΓ Γ q($l + 1) a q(.univ $l) vΓwf
      q(by as_aux_lemma => exact ⟨_, .univ ($vΓwf).wf_ctx $lmax⟩)
    withHave awf_ fun awf => do
    mkHaves #[lmax, awf] q(sorry)
  | _ =>
    throwError "not implemented: {Γ} ⊢[{l}]? {T}"

partial def checkTm (vΓ : Q(TpEnv)) (Γ : Q(Ctx)) (l : Q(Nat)) (t : Q(Expr)) (vT : Q(Val))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) (vTwf : Q(∃ T, ValEqTp $Γ $l $vT T)) :
    Lean.MetaM Q(∃ T, ValEqTp $Γ $l $vT T ∧ ($Γ ⊢[$l] ($t) : T)) := do
  /- We could do something more bidirectional,
  but all terms synthesize (thanks to extensive annotations). -/
  let ⟨vU, tU_⟩ ← synthTm vΓ Γ l t vΓwf
  withHave tU_ fun tU => do
  let eq ← equateTp Γ l vU vT q(sorry) q(sorry)
  mkHaves #[tU] q(by as_aux_lemma =>
    sorry
    -- exact ($tU).conv <| ($eq).tp_uniq $vUeq $vTeq
  )

partial def synthTm (vΓ : Q(TpEnv)) (Γ : Q(Ctx)) (l : Q(Nat)) (t : Q(Expr))
    (vΓwf : Q(TpEnvEqCtx $vΓ $Γ)) :
    Lean.MetaM ((vT : Q(Val)) × Q(∃ T, ValEqTp $Γ $l $vT T ∧ ($Γ ⊢[$l] ($t) : T))) :=
  match t with
  | ~q(.bvar $i) => do
    return ⟨q(sorry), q(sorry)⟩
    -- TODO: lookup in `vΓ` instead?
    -- let ⟨A, m, lk_⟩ ← lookup Γ i
    -- withHave lk_ fun lk => do
    -- let lm_ ← equateNat l m
    -- withHave lm_ fun lm => do
    -- return ⟨A, ← mkHaves #[lk, lm] q(by as_aux_lemma =>
    --   cases ($lm); exact WfTm.bvar ($vΓwf).wf_ctx $lk
    -- )⟩
  | ~q(.lam $k $k' $A $b) => do
    let Awf_ ← checkTp vΓ Γ k A vΓwf
    withHave Awf_ fun Awf => do
    let ⟨vA, vAeq_⟩ ← evalTp' vΓ Γ k A vΓwf Awf
    withHave vAeq_ fun vAeq => do
    let ⟨vB, bB_⟩ ← synthTm q(($vA, $k) :: $vΓ) q(($A, $k) :: $Γ) k' b q(sorry)
    withHave bB_ fun bB => do
    let lmax_ ← equateNat l q(max $k $k')
    withHave lmax_ fun lmax => do
    -- TODO: oh no! What do we synth for the type of a lam?!??! need value-closures >.<
    -- or readback. or storing the codomain type in `lam`.
    -- or `coe` and bidir typechecking.
    let vP : Q(Val) := q(.pi $k $k' $vA sorry)
    return ⟨vP, ← mkHaves #[Awf, vAeq, bB, lmax] q(by as_aux_lemma =>
      sorry
      -- cases ($lmax)
      -- exact WfTm.lam $bB
    )⟩
  | ~q(.app $k $k' $B $f $a) => do
    let lk'_ ← equateNat l k'
    withHave lk'_ fun lk' => do
    let ⟨vP, aP_⟩ ← synthTm vΓ Γ q(max $k $k') f q($vΓwf)
    withHave aP_ fun aP => do
    let ~q(.pi _ _ $vA _) := vP |
      throwError "expected a Π-type but got{Lean.indentExpr vP}\nin the type of{Lean.indentExpr f}"
    let awf_ ← checkTm vΓ Γ k a vA q($vΓwf) q(sorry)
    withHave awf_ fun awf => do
    let Bwf_ ← checkTp q(($vA, $k) :: $vΓ) q(sorry :: $Γ) k' B q(sorry)
    withHave Bwf_ fun Bwf => do
    let ⟨va, vaeq_⟩ ← evalTm' vΓ Γ k a q($vΓwf) q(sorry)
    withHave vaeq_ fun vaeq => do
    -- TODO: WHNF envOfTpEnv?
    let ⟨vBa, vBaeq_⟩ ← evalTp Γ q($va :: envOfTpEnv $vΓ) q(($a).toSb) q(sorry :: $Γ) k' B
      q(sorry) q(sorry)
    return ⟨vBa, ← mkHaves #[lk', aP, awf, Bwf, vaeq] q(by as_aux_lemma =>
      -- cases ($lk')
      -- apply WfTm.app $fp $aA
      sorry
    )⟩
  | ~q(.pair $k $k' $B $t $u) => do
    let lmax_ ← equateNat l q(max $k $k')
    withHave lmax_ fun lmax => do
    let ⟨vA, tA_⟩ ← synthTm vΓ Γ k t q($vΓwf)
    withHave tA_ fun tA => do
    let ⟨vU, uU_⟩ ← synthTm vΓ Γ k' u q($vΓwf)
    withHave uU_ fun uU => do
    -- Oh no! Don't have `A`! But don't need it :)
    let vT : Q(Val) := q(.sigma $k $k' $vA (.mk_tp $Γ sorry sorry $B))
    throwError "not implemented: {Γ} ⊢[{l}] {t} : ?"
  | ~q(.fst ..) | ~q(.snd ..) =>
    throwError "not implemented: {Γ} ⊢[{l}] {t} : ?"
  | ~q(.code $A) => do
    -- TODO: WHNF `l`? See comment at `evalTp`.
    let ~q(.succ $k) := l | throwError "expected _+1, got{Lean.indentExpr l}"
    let lmax_ ← ltNat k q(univMax)
    withHave lmax_ fun lmax => do
    let Awf_ ← checkTp vΓ Γ k A vΓwf
    withHave Awf_ fun Awf => do
    let vU : Q(Val) := q(.univ $k)
    return ⟨vU, ← mkHaves #[lmax, Awf] q(sorry)⟩
  | _ =>
    throwError "{t} is not a term in {Γ} ⊢[{l}] {t} : ?"
end
