import Qq
import HoTTLean.Syntax.Axioms
import HoTTLean.Frontend.Checked

namespace SynthLean

open Qq Lean Meta

def traceClsTranslation : Name := `SynthLean.Translation

def reflectPostfix : Name := `reflection

initialize
  registerTraceClass traceClsTranslation
  registerTraceClass (traceClsTranslation ++ `tp) (inherited := true)
  registerTraceClass (traceClsTranslation ++ `tm) (inherited := true)

structure Context where
  /-- The position of an `FVarId` is its de Bruijn index. -/
  bvars : List FVarId := []

/-- `TranslateM` computations run in the internal environment
(otherwise operations such as type inference on internal constants wouldn't work). -/
abbrev TranslateM := ReaderT Context MetaM

def TranslateM.run {α : Type} (x : TranslateM α) : MetaM α :=
  ReaderT.run x {}

def withBinder {α : Type} (x : Lean.Expr) (k : TranslateM α) : TranslateM α := do
  withReader (fun s => { s with bvars := x.fvarId! :: s.bvars }) k

/-- Extract the level `u` in `Sort u`.
It must be monomorphic, i.e., may not contain universe variables.
It may also not contain level metavariables. -/
def getSortLevel (l : Level) : Lean.MetaM Nat := do
  let l ← instantiateLevelMVars l
  if l.hasMVar then
    throwError "unsupported universe (contains metavariables){indentExpr <| .sort l}"
  match l.toNat with
  | .some (n+1) => return n
  | .some 0 => throwError "unsupported universe{indentExpr <| .sort l}"
  | .none => throwError "unsupported polymorphic universe level in{indentExpr <| .sort l}"

/-- Syntactically check if a Lean expression should be handled by the type translator.
We use the term translator iff this returns `false`. -/
def isType : Lean.Expr → Bool
  | .mdata _ e => isType e
  | .sort .. | .forallE .. => true
  | _ => false

/-- Make the SynthLean term
`fun (A : Type l) (B : A → Type l') : Type (max l l') => code (Σ (El A) (El (B #0)))`. -/
def mkSigma {u : Level} (χ : Q(Type u)) (l l' : Nat) : Q(Expr $χ) :=
  q(.lam ($l + 1) (max $l $l' + 1) (.univ $l) <|
    .lam (max $l ($l' + 1)) (max $l $l' + 1) (.pi $l ($l' + 1) (.el <| .bvar 0) (.univ $l')) <|
      .code <|
        .sigma $l $l'
          (.el <| .bvar 1)
          (.el <| .app $l ($l' + 1) (.univ $l') (.bvar 1) (.bvar 0)))

/-- Make the SynthLean term
`fun (A : Type l) (a b : A) : Type l => code (.Id l a b)`. -/
def mkId {u : Level} (χ : Q(Type u)) (l : Nat) : Q(Expr $χ) :=
  q(.lam ($l + 1) ($l + 1) (.univ $l) <|
    .lam $l ($l + 1) (.el <| .bvar 0) <|
      .lam $l ($l + 1) (.el <| .bvar 1) <|
        .code <| .Id $l (.el <| .bvar 2) (.bvar 1) (.bvar 0))

mutual
/-- Completeness: if the argument is well-formed in Lean,
the output is well-typed in MLTT. -/
partial def translateAsTp (e : Lean.Expr) : TranslateM (Nat × Q(Expr Lean.Name)) := do
  Lean.withTraceNode (ε := Lean.Exception) (traceClsTranslation ++ `tp) (fun
    | .ok ⟨l, A⟩ => do
      return m!"✅️ {e} [{l}]⇒ {A}"
    | .error _ => return m!"❌️ {e} ⇒ _") do
  if !isType e then
    let ⟨l+1, a⟩ ← translateAsTm e
      | throwError "type code should have level > 0{indentExpr e}"
    return ⟨l, q(.el $a)⟩
  match e with
  | .mdata _ e => translateAsTp e
  | .sort l => do
    let n : Nat ← getSortLevel l
    return ⟨n+1, q(.univ $n)⟩
  | .forallE _ A .. =>
    let ⟨l, A⟩ ← translateAsTp A
    let ⟨l', B⟩ ← forallBoundedTelescope e (some 1) fun xs B => do
      let #[x] := xs | throwError "internal error (forall tp)"
      withBinder x <| translateAsTp B
    return ⟨max l l', q(.pi $l $l' $A $B)⟩
  | _ => throwError "internal error: should fail `isType`{indentExpr e}"

partial def translateAsTm (e : Lean.Expr) : TranslateM (Nat × Q(Expr Lean.Name)) := do
  Lean.withTraceNode (ε := Lean.Exception) (traceClsTranslation ++ `tm) (fun
    | .ok ⟨l, a⟩ => do
      return m!"✅️ {e} [{l}]⇒ {a}"
    | .error _ => return m!"❌️ {e} ⇒ _") do
  if isType e then
    let ⟨l, A⟩ ← translateAsTp e
    return ⟨l+1, q(.code $A)⟩
  match e with
  | .mdata _ e => translateAsTm e
  | .fvar f => do
    let eTp ← inferType e
    let .sort l ← inferType eTp | throwError "internal error (sort)"
    let n ← getSortLevel l
    match (← read).bvars.findIdx? (· == f) with
    | some i => return ⟨n, q(.bvar $i)⟩
    | none => throwError "unexpected fvar{indentExpr e}"
  | .lam _ A .. =>
    let ⟨l, A⟩ ← translateAsTp A
    let ⟨l', b⟩ ← lambdaBoundedTelescope e 1 fun xs b => do
      let #[x] := xs | throwError "internal error (lam tm)"
      withBinder x <| translateAsTm b
    return ⟨max l l', q(.lam $l $l' $A $b)⟩
  | .app fn arg => do
    if e.isAppOfArity' ``sorryAx 3 then
      let #[A, _, _] := e.getAppArgs | throwError "internalError"
      -- Recent versions of Lean generate ``sorryAx (Name → ActualType) `«sourceLocation»``.
      -- In `Frontend.Prelude` we have defined `sorryAxₗ` for `l < univMax`.
      -- We translate the former to the latter.
      let ⟨l, A⟩ ← forallBoundedTelescope A (some 1) fun xs A' => do
        let #[x] := xs | throwError "internal error (sorryAx)"
        let tp ← inferType x
        if !(← isDefEq tp q(Lean.Name)) then
          throwError "unexpected type of sorryAx{Lean.indentExpr A}"
        translateAsTp A'
      let sl : Nat := l + 1
      let name : Q(Lean.Name) := toExpr <|
        Lean.Name.anonymous.str s!"sorryAx{Nat.subDigitChar l}"
      return ⟨l,
        q(.app $sl $l (.el <| .bvar 0)
          (.ax $name (.pi $sl $l (.univ $l) (.el <| .bvar 0)))
          (.code $A))⟩
    if e.isAppOfArity' ``Sigma.mk 4 then
      let #[_, B, f, s] := e.getAppArgs | throwError "internal error"
      let ⟨l', B⟩ ← lambdaBoundedTelescope B 1 fun xs B => do
        let #[x] := xs | throwError "internal error (Sigma.mk)"
        withBinder x <| translateAsTp B
      let ⟨l, f⟩ ← translateAsTm f
      let ⟨_, s⟩ ← translateAsTm s
      return ⟨max l l', q(.pair $l $l' $B $f $s)⟩
    if e.isAppOfArity' ``Sigma.fst 3 then
      let #[A, B, p] := e.getAppArgs | throwError "internal error"
      let ⟨l, A⟩ ← translateAsTp A
      let ⟨l', B⟩ ← lambdaBoundedTelescope B 1 fun xs B => do
        let #[x] := xs | throwError "internal error (Sigma.fst)"
        withBinder x <| translateAsTp B
      let ⟨_, p⟩ ← translateAsTm p
      return ⟨l, q(.fst $l $l' $A $B $p)⟩
    if e.isAppOfArity' ``Sigma.snd 3 then
      let #[A, B, p] := e.getAppArgs | throwError "internal error"
      let ⟨l, A⟩ ← translateAsTp A
      let ⟨l', B⟩ ← lambdaBoundedTelescope B 1 fun xs B => do
        let #[x] := xs | throwError "internal error (Sigma.snd)"
        withBinder x <| translateAsTp B
      let ⟨_, p⟩ ← translateAsTm p
      return ⟨l', q(.snd $l $l' $A $B $p)⟩
    -- Defined in `Syntax.Frontend.Prelude`.
    if e.isAppOfArity' `Identity.refl 2 then
      let #[_, a] := e.getAppArgs | throwError "internal error (Id.refl)"
      let ⟨l, a⟩ ← translateAsTm a
      return ⟨l, q(.refl $l $a)⟩
    if e.isAppOfArity' `Identity.rec 6 then
      let #[_, a, M, r, b, h] := e.getAppArgs | throwError "internal error (Id.rec)"
      let ⟨l, a⟩ ← translateAsTm a
      let ⟨l', M⟩ ← lambdaBoundedTelescope M 2 fun xs M => do
        let #[x, h] := xs | throwError "internal error (Id.rec motive)"
        withBinder x <| withBinder h <| translateAsTp M
      let ⟨_, r⟩ ← translateAsTm r
      let ⟨_, b⟩ ← translateAsTm b
      let ⟨_, h⟩ ← translateAsTm h
      return ⟨l', q(.idRec $l $l' $a $M $r $b $h)⟩
    let fnTp ← inferType fn
    let ⟨_, fn⟩ ← translateAsTm fn
    let ⟨l, arg⟩ ← translateAsTm arg
    let ⟨l', B⟩ ← forallBoundedTelescope fnTp (some 1) fun xs B => do
      let #[x] := xs | throwError "internal error (app tm)"
      withBinder x <| translateAsTp B
    return ⟨l', q(.app $l $l' $B $fn $arg)⟩
  | .const ``Sigma [l, l'] =>
    /- FIXME: To simplify the translation,
    we handle `Sigma` rather than fully applied `@Sigma α β`.
    However, `mkSigma` has to use codes
    and consequently Σ in `univMax` cannot be translated.
    But the max universe is deficient anyway -
    it can't have axiomatic function extensionality -
    so maybe this is fine. -/
    let l ← getSortLevel l.succ
    let l' ← getSortLevel l'.succ
    return ⟨max l l' + 1, mkSigma _ l l'⟩
  | .const `Identity [l] =>
    let l ← getSortLevel l.succ
    return ⟨l + 1, mkId _ l⟩
  | .const nm [] =>
    let eTp ← inferType e
    let .sort l ← inferType eTp | throwError "internal error (sort)"
    let n ← getSortLevel l
    -- We translate constants to projections of reflected constants.
    let ci ← getConstInfo nm
    let nm := ci.name ++ reflectPostfix
    if !(← hasConst nm) then
      throwError "Constant '{Expr.const ci.name []}' has not been reflected. \
        Try marking it with `@[reflect]`."
    match ci with
    | .defnInfo _ => return ⟨n, ← mkAppM ``CheckedDef.val #[.const nm []]⟩
    | .axiomInfo _ => return ⟨n, ← mkAppM ``CheckedAx.val #[.const nm []]⟩
    | _ => throwError "unsupported kind of constant (not a `def` or an `axiom`){indentExpr e}"
  | .const .. => throwError "unsupported constant (universe-polymorphic){indentExpr e}"
  | e => throwError "unsupported term{indentExpr e}"

end

end SynthLean
