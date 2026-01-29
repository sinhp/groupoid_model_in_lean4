import HoTTLean.Typechecker.Equate
import HoTTLean.Frontend.Checked

/-! ## Typechecker

This module contains the top-level typechecker implementation.

For now it is specialized to axioms named by `Lean.Name`. -/

namespace SynthLean
open Qq

def traceClsTypechecker : Lean.Name := `SynthLean.Typechecker

initialize
  Lean.registerTraceClass traceClsTypechecker

partial def lookupVar (vΓ : Q(TpEnv Lean.Name)) (i : Q(Nat)) :
    Lean.MetaM ((vA : Q(Val Lean.Name)) × (l : Q(Nat)) ×
      Q(∀ {E Γ}, TpEnvEqCtx E $vΓ Γ → ∃ A,
        ValEqTp E Γ $l $vA A ∧ Lookup Γ $i A $l)) :=
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
    let ⟨vA, l, pf⟩ ← lookupVar q($vΓ') q($i')
    return ⟨q($vA), q($l), q(by as_aux_lemma =>
      introv vΓ
      simp +zetaDelta only at vΓ ⊢
      rcases vΓ with _ | ⟨vΓ', vB⟩
      have ⟨_, vA, lk⟩ := $pf vΓ'
      exact ⟨_, vA.wk vB.wf_tp, lk.succ ..⟩
    )⟩

/-- Look up an axiom in an axiom environment. -/
partial def lookupAxiom (E : Q(Axioms Lean.Name)) (c : Q(Lean.Name)) : Lean.MetaM
    ((A : Q(Expr Lean.Name)) × (l : Q(Nat)) × Q(∃ h, $E $c = some ⟨($A, $l), h⟩) ⊕
      Q($E $c = none)) := do
  match E with
  | ~q(.empty _) => return .inr q(by rfl)
  | ~q(Axioms.snoc $E' $l $c' $A $l_le $A_cl) =>
    let b : Q(Bool) ← Lean.Meta.whnf q(decide ($c' = $c))
    have : $b =Q decide ($c' = $c) := .unsafeIntro
    match b with
    | ~q(true) =>
      return Sum.inl ⟨q($A), q($l), q(by as_aux_lemma =>
        have : $c' = $c := by rwa [decide_eq_true_iff] at *
        simp +zetaDelta [this, ($A_cl), ($l_le)]
      )⟩
    | ~q(false) =>
      match ← lookupAxiom q($E') q($c) with
      | .inl ⟨A, l, h⟩ =>
        return .inl ⟨A, l, q(by as_aux_lemma =>
          have : $c' ≠ $c := by rwa [decide_eq_false_iff_not] at *
          have ⟨h, eq⟩ := $h
          refine ⟨h, ?_⟩
          simpa +zetaDelta [CheckedAx.snocAxioms, Axioms.snoc, this.symm] using eq
        )⟩
      | .inr h =>
        return .inr q(by as_aux_lemma =>
          have : $c' ≠ $c := by rwa [decide_eq_false_iff_not] at *
          simpa +zetaDelta [CheckedAx.snocAxioms, Axioms.snoc, this.symm] using $h
        )
    | _ =>
      throwError "could not determine whether\
          {Lean.indentExpr q($c') |>.nest 2}\
        {Lean.indentD "="}\
          {Lean.indentExpr c |>.nest 2}"
  | ~q(CheckedAx.snocAxioms _) =>
    let E ← Lean.Meta.unfoldDefinition E
    lookupAxiom E c
  | _ => throwError "unsupported axiom environment{Lean.indentExpr E}"

partial def checkAxiomsLe (E E' : Q(Axioms Lean.Name)) : Lean.MetaM Q($E ≤ $E') := do
  match E with
  | ~q(.empty _) => return q(($E').empty_le)
  | ~q(Axioms.snoc $E₀ $l' $c' $A' $l_le $A_cl) =>
    let le ← checkAxiomsLe q($E₀) q($E')
    let .inl ⟨A, l, En⟩ ← lookupAxiom q($E') q($c')
      | throwError "could not prove that '{c'}' is contained in{Lean.indentExpr E'}"
    let ⟨_⟩ ← assertDefEqQ q($A) q($A')
    let ⟨_⟩ ← assertDefEqQ q($l) q($l')
    return q(by as_aux_lemma =>
      dsimp +zetaDelta only [CheckedAx.snocAxioms]
      have ⟨_, h⟩ := $En
      apply Axioms.snoc_le $le _ _ _ _ _ h
    )
  | ~q(CheckedAx.snocAxioms _) =>
    let E ← Lean.Meta.unfoldDefinition E
    checkAxiomsLe E E'
  | _ =>
    throwError "could not prove\
        {Lean.indentExpr E |>.nest 2}\
      {Lean.indentD "≤"}\
        {Lean.indentExpr E' |>.nest 2}"

mutual
variable (E : Q(Axioms Lean.Name)) (Ewf : Q(($E).Wf))

partial def checkTp (vΓ : Q(TpEnv Lean.Name)) (l : Q(Nat)) (T : Q(Expr Lean.Name)) :
    TypecheckerM Q(∀ {Γ}, TpEnvEqCtx $E $vΓ Γ → $E ∣ Γ ⊢[$l] ($T)) :=
  Lean.withTraceNode traceClsTypechecker (fun e =>
    return m!"{Lean.exceptEmoji e} {vΓ} ⊢[{l}] {T}") do
  let key := (⟨vΓ⟩, ⟨l⟩, ⟨T⟩)
  if let some pf := (← get).checkTp[key]? then return pf
  eventually (fun pf =>
    modify fun st => { st with checkTp := st.checkTp.insert key pf }) do
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

partial def checkTm (vΓ : Q(TpEnv Lean.Name)) (l : Q(Nat))
    (vT : Q(Val Lean.Name)) (t : Q(Expr Lean.Name)) :
    TypecheckerM Q(∀ {Γ T}, TpEnvEqCtx $E $vΓ Γ → ValEqTp $E Γ $l $vT T →
      $E ∣ Γ ⊢[$l] ($t) : T) := do
  Lean.withTraceNode traceClsTypechecker (fun e =>
    return m!"{Lean.exceptEmoji e} {vΓ} ⊢[{l}] {t} ⇐ {vT}") do
  let key := (⟨vΓ⟩, ⟨l⟩, ⟨vT⟩, ⟨t⟩)
  if let some pf := (← get).checkTm[key]? then return pf
  eventually (fun pf =>
    modify fun st => { st with checkTm := st.checkTm.insert key pf }) do
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
partial def synthTm (vΓ : Q(TpEnv Lean.Name)) (l : Q(Nat)) (t : Q(Expr Lean.Name)) :
    TypecheckerM ((vT : Q(Val Lean.Name)) × Q(∀ {Γ}, TpEnvEqCtx $E $vΓ Γ →
      ∃ T, ValEqTp $E Γ $l $vT T ∧ ($E ∣ Γ ⊢[$l] ($t) : T))) :=
  Lean.withTraceNode (ε := Lean.Exception) traceClsTypechecker (fun
    | .ok ⟨vT, _⟩ => return m!"✅️ {vΓ} ⊢[{l}] {t} ⇒ {vT}"
    | .error _ => return m!"❌️ {vΓ} ⊢[{l}] {t} ⇒ _") do
  let key := (⟨vΓ⟩, ⟨l⟩, ⟨t⟩)
  if let some (v, pf) := (← get).synthTm[key]? then return ⟨v, pf⟩
  eventually (fun ⟨v, pf⟩ =>
    modify fun st => { st with synthTm := st.synthTm.insert key (v, pf) }) do
  match t with
  | ~q(@CheckedDef.val _ $E' $defn) => do
    -- Ensure the definition uses a subset of the available axioms.
    let le ← checkAxiomsLe q($E') q($E)
    let _ ← equateNat q($l) q(($defn).l)
    return ⟨q(($defn).nfTp), q(by as_aux_lemma =>
      introv vΓ; have Γwf := vΓ.wf_ctx; clear vΓ
      subst_vars
      induction Γ
      . exact ⟨_, ($defn).wf_nfTp.of_axioms_le $le, ($defn).wf_val.of_axioms_le $le⟩
      . rename_i ih
        have B := Γwf.inv_snoc
        have ⟨_, vA, t⟩ := ih B.wf_ctx
        refine ⟨_, vA.wk B, ?_⟩
        convert t.subst (WfSb.wk B) using 1
        rw [Expr.subst_of_isClosed _ ($defn).wf_val.isClosed]
    )⟩
  | ~q(CheckedAx.val $ax) => do
    let le ← checkAxiomsLe q(($ax).snocAxioms) q($E)
    let _ ← equateNat q($l) q(($ax).l)
    return ⟨q(($ax).nfTp), q(by as_aux_lemma =>
      introv vΓ; have Γwf := vΓ.wf_ctx; clear vΓ
      subst_vars
      have le' := Trans.trans ($ax).le_snocAxioms $le
      induction Γ
      . exact ⟨_, ($ax).wf_nfTp.of_axioms_le le', ($ax).wf_val.of_axioms_le $le⟩
      . rename_i ih
        have B := Γwf.inv_snoc
        have ⟨_, vA, t⟩ := ih B.wf_ctx
        refine ⟨_, vA.wk B, ?_⟩
        have := t.subst (WfSb.wk B)
        rwa [Expr.subst_of_isClosed _ ($ax).wf_val.isClosed] at this
    )⟩
  | ~q(.ax $c $A) => do
    let .inl ⟨A', l', get⟩ ← lookupAxiom q($E) q($c)
      | throwError "could not find constant '{c}' in environment{Lean.indentExpr E}"
    let leq ← equateNat q($l) q($l')
    -- TODO: relax to a defeq check?
    let ⟨_⟩ ← assertDefEqQ q($A) q($A')
    -- NOTE: could also evaluate in empty environment here and then weaken `ValEqTp`;
    -- I think it makes no difference.
    let ⟨vA, vApost⟩ ← evalTpId q($vΓ) q($A)
    return ⟨vA, q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have ⟨_, Ec⟩ := $get
      have := $vApost vΓ (($Ewf).atCtx vΓ.wf_ctx Ec)
      refine ⟨_, this, .ax vΓ.wf_ctx Ec this.wf_tp⟩
    )⟩
  | ~q(.bvar $i) => do
    let ⟨vA, m, lk⟩ ← lookupVar q($vΓ) q($i)
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
    return ⟨q(.pi $k $k' $vA (.of_val ($vΓ).toEnv $vB)), q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have A := $Awf vΓ
      have vA := $vAeq vΓ A
      have ⟨B, vB, b⟩ := $bB (vΓ.snoc vA)
      refine ⟨.pi $k $k' $A B, ?_, WfTm.lam b⟩
      apply ValEqTp.pi vA
      convert ClosEqTp.clos_val_tp vΓ.toEnv_wf _ vB using 1
      . autosubst
      . autosubst; apply EqTp.refl_tp A
    )⟩
  | ~q(.app $k $k' $B $f $a) => do
    let lk' ← equateNat q($l) q($k')
    let ⟨vA, vApost⟩ ← synthTm q($vΓ) q($k) q($a)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    let fwf ← checkTm q($vΓ) q(max $k $k') q(.pi $k $k' $vA (.of_expr ($vΓ).toEnv $B)) q($f)
    let ⟨va, vaeq⟩ ← evalTmId q($vΓ) q($a)
    let ⟨vBa, vBaeq⟩ ← evalTp q($va :: ($vΓ).toEnv) q($B)
    return ⟨vBa, q(by as_aux_lemma =>
      introv vΓ
      have ⟨_, vA, a⟩ := $vApost vΓ
      have B := $Bwf <| vΓ.snoc vA
      have f := $fwf vΓ <| ValEqTp.pi vA <|
        ClosEqTp.clos_tp vΓ.toEnv_wf (by convert EqTp.refl_tp a.wf_tp using 1; autosubst) B
      have va := $vaeq vΓ a
      have := vΓ.toEnv_wf.snoc va.wf_tm.wf_tp (by convert va using 1; autosubst)
      subst_vars
      refine ⟨_, $vBaeq this B, ?_⟩
      convert WfTm.app f a using 1 <;> simp +zetaDelta only [autosubst]
    )⟩
  | ~q(.pair $k $k' $B $f $s) => do
    let lmax ← equateNat q($l) q(max $k $k')
    let ⟨vA, fA⟩ ← synthTm q($vΓ) q($k) q($f)
    let Bwf ← checkTp q(($vA, $k) :: $vΓ) q($k') q($B)
    let ⟨vf, vfpost⟩ ← evalTmId q($vΓ) q($f)
    let ⟨vBf, vBfpost⟩ ← evalTp q($vf :: ($vΓ).toEnv) q($B)
    let swf ← checkTm q($vΓ) q($k') q($vBf) q($s)
    return ⟨q(.sigma $k $k' $vA (.of_expr ($vΓ).toEnv $B)), q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have ⟨_, vA, f⟩ := $fA vΓ
      have B := $Bwf <| vΓ.snoc vA
      have vf := $vfpost vΓ f
      have vBf := $vBfpost (vΓ.toEnv_wf.snoc f.wf_tp (by convert vf using 1; autosubst)) B
      have s := $swf vΓ vBf
      have := ValEqTp.sigma vA <|
        ClosEqTp.clos_tp vΓ.toEnv_wf (by convert EqTp.refl_tp vA.wf_tp using 1; autosubst) B
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
      q($vΓ) q(max $k $k') q(.sigma $k $k' $vA (.of_expr ($vΓ).toEnv $B)) q($p)
    return ⟨vA, q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have A := $Awf vΓ
      have vA := $vApost vΓ A
      have B := $Bwf <| vΓ.snoc vA
      have p := $pwf vΓ <| ValEqTp.sigma vA <|
        ClosEqTp.clos_tp vΓ.toEnv_wf (by convert EqTp.refl_tp vA.wf_tp using 1; autosubst) B
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
      checkTm q($vΓ) q(max $k $k') q(.sigma $k $k' $vA (.of_expr ($vΓ).toEnv $B)) q($p)
    let ⟨vp, vppost⟩ ← evalTmId q($vΓ) q($p)
    let ⟨vf, vfpost⟩ ← evalFst q($vp)
    let ⟨vBf, vBfpost⟩ ← evalTp q($vf :: ($vΓ).toEnv) q($B)
    return ⟨vBf, q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have A := $Awf vΓ
      have vA := $vApost vΓ A
      have B := $Bwf <| vΓ.snoc vA
      have p := $pwf vΓ <| ValEqTp.sigma vA <|
        ClosEqTp.clos_tp vΓ.toEnv_wf (by convert EqTp.refl_tp vA.wf_tp using 1; autosubst) B
      have vp := $vppost vΓ p
      have vf := $vfpost vp
      have vBf :=
        $vBfpost (vΓ.toEnv_wf.snoc vf.wf_tm.wf_tp (by convert vf using 1; autosubst)) B
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
    let ⟨vMa, vMapost⟩ ← evalTp q((.refl $k $va) :: $va :: ($vΓ).toEnv) q($M)
    let rwf ← checkTm q($vΓ) q($k') q($vMa) q($r)
    let bwf ← checkTm q($vΓ) q($k) q($vA) q($b)
    let ⟨vb, vbpost⟩ ← evalTmId q($vΓ) q($b)
    let hwf ← checkTm q($vΓ) q($k) q(.Id $k $vA $va $vb) q($h)
    let ⟨vh, vhpost⟩ ← evalTmId q($vΓ) q($h)
    let ⟨vMb, vMbpost⟩ ← evalTp q($vh :: $vb :: ($vΓ).toEnv) q($M)
    return ⟨q($vMb), q(by as_aux_lemma =>
      introv vΓ
      subst_vars
      have ⟨_, vA, a⟩ := $vApost vΓ
      have va := $vapost vΓ a
      have := ValEqTp.Id_bvar vA va
      rw [← vΓ.length_eq] at this
      have M := $Mwf (vΓ.snoc vA |>.snoc this)
      have := vΓ.toEnv_wf
        |>.snoc a.wf_tp (autosubst% va)
        |>.snoc (WfTp.Id_bvar a) (autosubst% ValEqTm.refl va)
      have vMa := $vMapost this M
      have r := $rwf vΓ vMa
      have b := $bwf vΓ vA
      have vb := $vbpost vΓ b
      have h := $hwf vΓ (ValEqTp.Id vA va vb)
      have vh := $vhpost vΓ h
      have := vΓ.toEnv_wf
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

end SynthLean
