import Qq
import HoTTLean.Syntax.Axioms
import HoTTLean.Typechecker.Util
import HoTTLean.Frontend.Reflected
import HoTTLean.Frontend.Instances
import HoTTLean.Frontend.Shallow

namespace SynthLean

open Qq Lean Meta

namespace TraceCls
def Translation := `SynthLean.Translation
def translateAsTp := Translation ++ `asTp
def translateAsTm := Translation ++ `asTm

initialize
  registerTraceClass Translation
  registerTraceClass translateAsTp (inherited := true)
  registerTraceClass translateAsTm (inherited := true)
end TraceCls

def reflectPostfix : Name := `reflection


structure Context {u : Level} (χ : Q(Type u)) where
  /-- The `FVarId` of each active binder in the local context.
  The position of an `FVarId` here is its de Bruijn index in the translated term. -/
  bvars : List FVarId := []
  /-- The theory that the translated term should be well-formed w.r.t. to.
  We synthesize and insert theory maps to ensure this. -/
  expectedTheory : Q(Axioms $χ)

abbrev TranslateM {u : Level} (χ : Q(Type u)) := ReaderT (Context χ) MetaM

def TranslateM.run {α : Type} {u : Level} {χ : Q(Type u)} (x : TranslateM χ α)
    (expectedTheory : Q(Axioms $χ)) : MetaM α :=
  ReaderT.run x { expectedTheory }

def withBinder {α : Type} {u : Level} {χ : Q(Type u)} (x : Lean.Expr) (k : TranslateM χ α) :
    TranslateM χ α := do
  withReader (fun s => { s with bvars := x.fvarId! :: s.bvars }) k

/-- Extract the level `u` in `Sort l = Type u`.
It must be monomorphic, i.e., may not contain universe variables.
It may also not contain level metavariables. -/
def getTypeLevel (l : Level) : Lean.MetaM Nat := do
  let l ← instantiateLevelMVars l
  if l.hasMVar then
    throwError "unsupported universe (contains metavariables){indentExpr <| .sort l}"
  if l.hasParam then
    throwError "unsupported universe (contains level parameters){indentExpr <| .sort l}"
  match l.toNat with
  | .some (n+1) => return n
  | .some 0 => throwError "unsupported proof-irrelevant universe{indentExpr <| .sort l}"
  | _ => throwError "internal error"

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

/-- Get the theory w.r.t. which a checked entity is defined. -/
def getTheoryOfChecked (e : Lean.Expr) : MetaM ((u : Level) × (χ : Q(Type u)) × Q(Axioms $χ)) := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  match α with
  | ~q(@ReflectedAx $χ $E) =>
    let _ ← synthInstanceQ q(DecidableEq $χ)
    return ⟨u, q($χ), q(($e).snocAxioms)⟩
  | ~q(@ReflectedDef $χ $E) => return ⟨u, q($χ), q($E)⟩
  | _ => throwError "expected a `CheckedAx` or `CheckedDef`, got{indentExpr e}"

mutual
/-- Completeness: if the argument is well-formed in Lean,
the output is well-typed in MLTT. -/
partial def translateAsTp {u : Level} (χ : Q(Type u)) (e : Lean.Expr) :
    TranslateM χ (Nat × Q(Expr $χ)) := do
  Lean.withTraceNode (ε := Lean.Exception) TraceCls.translateAsTp (fun
    | .ok ⟨l, A⟩ => do
      return m!"✅️ {e} [{l}]⇒ {A}"
    | .error _ => return m!"❌️ {e} ⇒ _") do
  if !isType e then
    let ⟨l+1, a⟩ ← translateAsTm χ e
      | throwError "type code should have level > 0{indentExpr e}"
    return ⟨l, q(.el $a)⟩
  match e with
  | .mdata _ e => translateAsTp χ e
  | .sort l => do
    let n : Nat ← getTypeLevel l
    return ⟨n+1, q(.univ $n)⟩
  | .forallE _ A .. =>
    let ⟨l, A⟩ ← translateAsTp χ A
    let ⟨l', B⟩ ← forallBoundedTelescope e (some 1) fun xs B => do
      let #[x] := xs | throwError "internal error (forall tp)"
      withBinder x <| translateAsTp χ B
    return ⟨max l l', q(.pi $l $l' $A $B)⟩
  | _ => throwError "internal error: should fail `isType`{indentExpr e}"

partial def translateAsTm {u : Level} (χ : Q(Type u)) (e : Lean.Expr) :
    TranslateM χ (Nat × Q(Expr $χ)) := do
  Lean.withTraceNode (ε := Lean.Exception) TraceCls.translateAsTm (fun
    | .ok ⟨l, a⟩ => do
      return m!"✅️ {e} [{l}]⇒ {a}"
    | .error _ => return m!"❌️ {e} ⇒ _") do
  if isType e then
    let ⟨l, A⟩ ← translateAsTp χ e
    return ⟨l+1, q(.code $A)⟩
  match e with
  | .mdata _ e => translateAsTm χ e
  | .fvar f => do
    let eTp ← inferType e
    let .sort l ← inferType eTp | throwError "internal error (sort)"
    let n ← getTypeLevel l
    match (← read).bvars.findIdx? (· == f) with
    | some i => return ⟨n, q(.bvar $i)⟩
    | none => throwError "unexpected fvar{indentExpr e}"
  | .lam _ A .. =>
    let ⟨l, A⟩ ← translateAsTp χ A
    let ⟨l', b⟩ ← lambdaBoundedTelescope e 1 fun xs b => do
      let #[x] := xs | throwError "internal error (lam tm)"
      withBinder x <| translateAsTm χ b
    return ⟨max l l', q(.lam $l $l' $A $b)⟩
  | .app fn arg => do
    if e.isAppOfArity' ``sorryAx 3 then
      let .defEq _ ← isLevelDefEqQ u 0
        | throwError "`sorry` can only be used with Lean.Name as the signature"
      let .defEq _ ← isDefEqQ q($χ) q(Lean.Name)
        | throwError "`sorry` can only be used with Lean.Name as the signature"
      let #[A, _, _] := e.getAppArgs | throwError "internalError"
      -- Recent versions of Lean generate ``sorryAx (Name → ActualType) `«sourceLocation»``.
      -- In `Frontend.Prelude` we have defined `sorryAxₗ` for `l < univMax`.
      -- We translate the former to the latter.
      let ⟨l, A⟩ ← forallBoundedTelescope A (some 1) fun xs A' => do
        let #[x] := xs | throwError "internal error (sorryAx)"
        let tp ← inferType x
        if !(← isDefEq tp q(Lean.Name)) then
          throwError "unexpected type of sorryAx{Lean.indentExpr A}"
        translateAsTp χ A'
      let sl : Nat := l + 1
      let name : Q(Lean.Name) := toExpr <|
        Lean.Name.anonymous.str s!"sorryAx{Nat.subDigitChar l}"
      return ⟨l,
        q(.app $sl $l (.el <| .bvar 0)
          (.ax $name (.pi $sl $l (.univ $l) (.el <| .bvar 0)))
          (.code $A))⟩
    if e.isAppOfArity' ``SemAx 2 then
      let #[T, a] := e.getAppArgs | throwError "internal error"
      let ⟨l, T⟩ ← translateAsTp χ T
      let a : Q($χ) ← evalExprExpr a
      return ⟨l, q(.ax $a $T)⟩
    if e.isAppOfArity' ``Sigma.mk 4 then
      let #[_, B, f, s] := e.getAppArgs | throwError "internal error"
      let ⟨l', B⟩ ← lambdaBoundedTelescope B 1 fun xs B => do
        let #[x] := xs | throwError "internal error (Sigma.mk)"
        withBinder x <| translateAsTp χ B
      let ⟨l, f⟩ ← translateAsTm χ f
      let ⟨_, s⟩ ← translateAsTm χ s
      return ⟨max l l', q(.pair $l $l' $B $f $s)⟩
    if e.isAppOfArity' ``Sigma.fst 3 then
      let #[A, B, p] := e.getAppArgs | throwError "internal error"
      let ⟨l, A⟩ ← translateAsTp χ A
      let ⟨l', B⟩ ← lambdaBoundedTelescope B 1 fun xs B => do
        let #[x] := xs | throwError "internal error (Sigma.fst)"
        withBinder x <| translateAsTp χ B
      let ⟨_, p⟩ ← translateAsTm χ p
      return ⟨l, q(.fst $l $l' $A $B $p)⟩
    if e.isAppOfArity' ``Sigma.snd 3 then
      let #[A, B, p] := e.getAppArgs | throwError "internal error"
      let ⟨l, A⟩ ← translateAsTp χ A
      let ⟨l', B⟩ ← lambdaBoundedTelescope B 1 fun xs B => do
        let #[x] := xs | throwError "internal error (Sigma.snd)"
        withBinder x <| translateAsTp χ B
      let ⟨_, p⟩ ← translateAsTm χ p
      return ⟨l', q(.snd $l $l' $A $B $p)⟩
    -- Defined in `Syntax.Frontend.Prelude`.
    if e.isAppOfArity' `Identity.refl 2 then
      let #[_, a] := e.getAppArgs | throwError "internal error (Id.refl)"
      let ⟨l, a⟩ ← translateAsTm χ a
      return ⟨l, q(.refl $l $a)⟩
    if e.isAppOfArity' `Identity.rec 6 then
      let #[_, a, M, r, b, h] := e.getAppArgs | throwError "internal error (Id.rec)"
      let ⟨l, a⟩ ← translateAsTm χ a
      let ⟨l', M⟩ ← lambdaBoundedTelescope M 2 fun xs M => do
        let #[x, h] := xs | throwError "internal error (Id.rec motive)"
        withBinder x <| withBinder h <| translateAsTp χ M
      let ⟨_, r⟩ ← translateAsTm χ r
      let ⟨_, b⟩ ← translateAsTm χ b
      let ⟨_, h⟩ ← translateAsTm χ h
      return ⟨l', q(.idRec $l $l' $a $M $r $b $h)⟩
    let fnTp ← inferType fn
    let ⟨_, fn⟩ ← translateAsTm χ fn
    let ⟨l, arg⟩ ← translateAsTm χ arg
    let ⟨l', B⟩ ← forallBoundedTelescope fnTp (some 1) fun xs B => do
      let #[x] := xs | throwError "internal error (app tm)"
      withBinder x <| translateAsTp χ B
    return ⟨l', q(.app $l $l' $B $fn $arg)⟩
  | .const ``Sigma [l, l'] =>
    /- FIXME: To simplify the translation,
    we handle `Sigma` rather than fully applied `@Sigma α β`.
    However, `mkSigma` has to use codes
    and consequently Σ in `univMax` cannot be translated.
    But the max universe is deficient anyway -
    it can't have axiomatic function extensionality -
    so maybe this is fine. -/
    let l ← getTypeLevel l.succ
    let l' ← getTypeLevel l'.succ
    return ⟨max l l' + 1, mkSigma _ l l'⟩
  | .const `Identity [l] =>
    let l ← getTypeLevel l.succ
    return ⟨l + 1, mkId _ l⟩
  | .const nm [] =>
    let eTp ← inferType e
    let .sort l ← inferType eTp | throwError "internal error (sort)"
    let n ← getTypeLevel l
    -- We translate constants to projections of reflected constants.
    let ci ← getConstInfo nm
    let nm := ci.name ++ reflectPostfix
    if !(← hasConst nm) then
      throwError "Constant '{Expr.const ci.name []}' has not been reflected. \
        Try marking it with `@[reflect]`."
    let ⟨_, χ₀, E⟩ ← getTheoryOfChecked (.const nm [])
    let val : Q(Expr $χ₀) := ← match ci with
      | .defnInfo _ => mkAppM ``ReflectedDef.val #[.const nm []]
      | .axiomInfo _ => mkAppM ``ReflectedAx.val #[.const nm []]
      | _ => throwError "unsupported kind of constant (not a `def` or an `axiom`){indentExpr e}"
    let E' := (← read).expectedTheory
    if !(← isDefEq E E') then
      let thyMap ← synthInstanceQ q(HasTheoryMap $E $E')
      trace[SynthLean.Translation.asTm]
        m!"inserting translation from{indentExpr E}\nto{indentExpr E'}"
      return ⟨n, q(($val).map ($thyMap).map)⟩
    return ⟨n, val⟩
  | .const .. => throwError "unsupported constant (universe-polymorphic){indentExpr e}"
  | e => throwError "unsupported term{indentExpr e}"

end

end SynthLean
