import GroupoidModel.Syntax.Typechecker.Equate

open Qq

def traceClsTypechecker : Lean.Name := `HoTT0.Typechecker

initialize
  Lean.registerTraceClass traceClsTypechecker

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
  Lean.withTraceNode traceClsTypechecker (fun e =>
    return m!"{Lean.exceptEmoji e} {vΓ} ⊢[{l}] {T}") do
  match T with
  | ~q(.pi $k $k' $A $B) => do
    let leq ← equateNat q($l) q(max $k $k')
    let Awf ← checkTp q($vΓ) q($k) q($A)
    let ⟨vA, vAeq⟩ ← evalTpId q($vΓ) q($A)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    return q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      apply WfTp.pi <| $Bwf <| vΓ.snoc <| $vAeq vΓ <| $Awf vΓ
    )
  | ~q(.sigma $k $k' $A $B) => do
    let leq ← equateNat q($l) q(max $k $k')
    let Awf ← checkTp q($vΓ) q($k) q($A)
    let ⟨vA, vAeq⟩ ← evalTpId q($vΓ) q($A)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    return q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      apply WfTp.sigma <| $Bwf <| vΓ.snoc <| $vAeq vΓ <| $Awf vΓ
    )
  | ~q(.Id $k $A $a $b) => do
    let leq ← equateNat q($l) q($k)
    let Awf ← checkTp q($vΓ) q($k) q($A)
    let ⟨vA, vAeq⟩ ← evalTpId q($vΓ) q($A)
    let awf ← checkTm q($vΓ) q($k) q($vA) q($a)
    let bwf ← checkTm q($vΓ) q($k) q($vA) q($b)
    return q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have := $vAeq vΓ ($Awf vΓ)
      apply WfTp.Id ($awf vΓ this) ($bwf vΓ this)
    )
  | ~q(.univ $n) => do
    let ln ← equateNat q($l) q($n + 1)
    let nmax ← ltNat q($n) q(univMax)
    return q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      apply WfTp.univ vΓ.wf_ctx $nmax
    )
  | ~q(.el $a) => do
    let lmax ← ltNat q($l) q(univMax)
    let awf ← checkTm q($vΓ) q($l + 1) q(.univ $l) q($a)
    return q(by as_aux_lemma =>
      introv vΓ
      simp +zetaDelta only
      apply WfTp.el <| $awf vΓ (ValEqTp.univ vΓ.wf_ctx $lmax)
    )
  | T => throwError "expected a type, got{Lean.indentExpr T}"

partial def checkTm (vΓ : Q(TpEnv)) (l : Q(Nat)) (vT : Q(Val)) (t : Q(Expr)) :
    Lean.MetaM Q(∀ {Γ T}, TpEnvEqCtx $vΓ Γ → ValEqTp Γ $l $vT T → Γ ⊢[$l] ($t) : T) := do
  Lean.withTraceNode traceClsTypechecker (fun e =>
    return m!"{Lean.exceptEmoji e} {vΓ} ⊢[{l}] {t} ⇐ {vT}") do
  /- We could do something more bidirectional,
  but all terms synthesize (thanks to extensive annotations). -/
  let ⟨vU, tU⟩ ← synthTm q($vΓ) q($l) q($t)
  let eq ← equateTp q(($vΓ).length) q($l) q($vU) q($vT)
  return q(by as_aux_lemma =>
    introv vΓ vT
    have ⟨_, vU, t⟩ := $tU vΓ
    apply t.conv <| $eq vΓ.length_eq vU vT
  )

-- TODO: infer rather than check universe level?
partial def synthTm (vΓ : Q(TpEnv)) (l : Q(Nat)) (t : Q(Expr)) : Lean.MetaM ((vT : Q(Val)) ×
    Q(∀ {Γ}, TpEnvEqCtx $vΓ Γ → ∃ T, ValEqTp Γ $l $vT T ∧ (Γ ⊢[$l] ($t) : T))) :=
  Lean.withTraceNode (ε := Lean.Exception) traceClsTypechecker (fun
    | .ok vT => return m!"✅️ {vΓ} ⊢[{l}] {t} ⇒ {vT}"
    | .error e => return m!"❌️ {vΓ} ⊢[{l}] {t} ⇒ _") do
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
    let Awf ← checkTp q($vΓ) q($k) q($A)
    let ⟨vA, vAeq⟩ ← evalTpId q($vΓ) q($A)
    let ⟨vB, bB⟩ ← synthTm q(($vA, $k) :: $vΓ) q($k') q($b)
    let lmax ← equateNat q($l) q(max $k $k')
    return ⟨q(.pi $k $k' $vA (.of_val (envOfTpEnv $vΓ) $vB)), q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have A := $Awf vΓ
      have vA := $vAeq vΓ A
      have ⟨B, vB, b⟩ := $bB (vΓ.snoc vA)
      refine ⟨.pi $k $k' $A B, ?_, WfTm.lam b⟩
      apply ValEqTp.pi vA
      convert ClosEqTp.clos_val_tp (envOfTpEnv_wf vΓ) _ vB using 1
      . autosubst
      . autosubst; apply EqTp.refl_tp A
    )⟩
  | ~q(.app $k $k' $B $f $a) => do
    let lk' ← equateNat q($l) q($k')
    let ⟨vA, vApost⟩ ← synthTm q($vΓ) q($k) q($a)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    let fwf ← checkTm q($vΓ) q(max $k $k') q(.pi $k $k' $vA (.of_expr (envOfTpEnv $vΓ) $B)) q($f)
    let ⟨va, vaeq⟩ ← evalTmId q($vΓ) q($a)
    let ⟨vBa, vBaeq⟩ ← evalTp q($va :: envOfTpEnv $vΓ) q($B)
    return ⟨vBa, q(by as_aux_lemma =>
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
    let lmax ← equateNat q($l) q(max $k $k')
    let ⟨vA, fA⟩ ← synthTm q($vΓ) q($k) q($f)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    let ⟨vf, vfpost⟩ ← evalTmId q($vΓ) q($f)
    let ⟨vBf, vBfpost⟩ ← evalTp q($vf :: envOfTpEnv $vΓ) q($B)
    let swf ← checkTm q($vΓ) q($k') q($vBf) q($s)
    return ⟨q(.sigma $k $k' $vA (.of_expr (envOfTpEnv $vΓ) $B)), q(by as_aux_lemma =>
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
  | ~q(.fst $k $k' $A $B $p) => do
    let leq ← equateNat q($l) q($k)
    let Awf ← checkTp q($vΓ) q($k) q($A)
    let ⟨vA, vApost⟩ ← evalTpId q($vΓ) q($A)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    let pwf ← checkTm
      q($vΓ) q(max $k $k') q(.sigma $k $k' $vA (.of_expr (envOfTpEnv $vΓ) $B)) q($p)
    return ⟨vA, q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have A := $Awf vΓ
      have vA := $vApost vΓ A
      have B := $Bwf <| vΓ.snoc vA
      have p := $pwf vΓ <| ValEqTp.sigma vA <|
        ClosEqTp.clos_tp (envOfTpEnv_wf vΓ) (by convert EqTp.refl_tp vA.wf_tp using 1; autosubst) B
      refine ⟨_, vA, ?_⟩
      simp +zetaDelta only [autosubst] at p ⊢
      apply WfTm.fst p
    )⟩
  | ~q(.snd $k $k' $A $B $p) => do
    let leq ← equateNat q($l) q($k')
    let Awf ← checkTp q($vΓ) q($k) q($A)
    let ⟨vA, vApost⟩ ← evalTpId q($vΓ) q($A)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    let pwf ←
      checkTm q($vΓ) q(max $k $k') q(.sigma $k $k' $vA (.of_expr (envOfTpEnv $vΓ) $B)) q($p)
    let ⟨vp, vppost⟩ ← evalTmId q($vΓ) q($p)
    let ⟨vf, vfpost⟩ ← evalFst q($vp)
    let ⟨vBf, vBfpost⟩ ← evalTp q($vf :: envOfTpEnv $vΓ) q($B)
    return ⟨vBf, q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have A := $Awf vΓ
      have vA := $vApost vΓ A
      have B := $Bwf <| vΓ.snoc vA
      have p := $pwf vΓ <| ValEqTp.sigma vA <|
        ClosEqTp.clos_tp (envOfTpEnv_wf vΓ) (by convert EqTp.refl_tp vA.wf_tp using 1; autosubst) B
      have vp := $vppost vΓ p
      have vf := $vfpost vp
      have vBf :=
        $vBfpost ((envOfTpEnv_wf vΓ).snoc vf.wf_tm.wf_tp (by convert vf using 1; autosubst)) B
      refine ⟨_, vBf, ?_⟩
      simp +zetaDelta only [autosubst] at p ⊢
      apply WfTm.snd p
    )⟩
  | ~q(.refl $k $a) => do
    let leq ← equateNat q($l) q($k)
    let ⟨vA, vApost⟩ ← synthTm q($vΓ) q($l) q($a)
    let ⟨va, vapost⟩ ← evalTmId q($vΓ) q($a)
    return ⟨q(.Id $k $vA $va $va), q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have ⟨_, vA, a⟩ := $vApost vΓ
      have va := $vapost vΓ a
      refine ⟨_, ValEqTp.Id vA va va, WfTm.refl a⟩
    )⟩
  | ~q(.idRec $k $k' $a $M $r $b $h) => do
    let leq ← equateNat q($l) q($k')
    let ⟨vA, vApost⟩ ← synthTm q($vΓ) q($k) q($a)
    let ⟨va, vapost⟩ ← evalTmId q($vΓ) q($a)
    let Mwf ← checkTp
      q((.Id $k $vA $va (.neut (.bvar ($vΓ).length) $vA), $k) :: ($vA, $k) :: $vΓ) q($k') q($M)
    let ⟨vMa, vMapost⟩ ← evalTp q((.refl $k $va) :: $va :: envOfTpEnv $vΓ) q($M)
    let rwf ← checkTm q($vΓ) q($k') q($vMa) q($r)
    let bwf ← checkTm q($vΓ) q($k) q($vA) q($b)
    let ⟨vb, vbpost⟩ ← evalTmId q($vΓ) q($b)
    let hwf ← checkTm q($vΓ) q($k) q(.Id $k $vA $va $vb) q($h)
    let ⟨vh, vhpost⟩ ← evalTmId q($vΓ) q($h)
    let ⟨vMb, vMbpost⟩ ← evalTp q($vh :: $vb :: envOfTpEnv $vΓ) q($M)
    return ⟨q($vMb), q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have ⟨_, vA, a⟩ := $vApost vΓ
      have va := $vapost vΓ a
      have := ValEqTp.Id_bvar vA va
      rw [← vΓ.length_eq] at this
      have M := $Mwf (vΓ.snoc vA |>.snoc this)
      have := envOfTpEnv_wf vΓ
        |>.snoc a.wf_tp (autosubst% va)
        |>.snoc (WfTp.Id_bvar a) (autosubst% ValEqTm.refl va)
      have vMa := $vMapost this M
      have r := $rwf vΓ vMa
      have b := $bwf vΓ vA
      have vb := $vbpost vΓ b
      have h := $hwf vΓ (ValEqTp.Id vA va vb)
      have vh := $vhpost vΓ h
      have := envOfTpEnv_wf vΓ
        |>.snoc a.wf_tp (autosubst% vb)
        |>.snoc (WfTp.Id_bvar a) (autosubst% vh)
      have vMb := $vMbpost this M
      refine ⟨_, vMb, .idRec M r h⟩
    )⟩
  | ~q(.code $A) => do
    -- TODO: WHNF `l`? See comment at `evalTp`.
    let ~q(.succ $k) := l | throwError "expected _+1, got{Lean.indentExpr l}"
    let lmax ← ltNat q($k) q(univMax)
    let Awf ← checkTp q($vΓ) q($k) q($A)
    return ⟨q(.univ $k), q(by as_aux_lemma =>
      introv vΓ
      exact ⟨_, ValEqTp.univ vΓ.wf_ctx $lmax, WfTm.code $lmax ($Awf vΓ)⟩
    )⟩
  | t =>
    throwError "expected a term, got{Lean.indentExpr t}"
end
