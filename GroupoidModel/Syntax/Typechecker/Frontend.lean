import Lean
import Qq
import Mathlib.Util.WhatsNew
import GroupoidModel.Syntax.Typechecker.Synth

/-! ## Basic types -/

namespace HoTT0

inductive Id.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Id a a

end HoTT0

/-! ## Translation from Lean to HoTT0 -/

namespace HoTT0.Translation

open Qq Lean Meta

def traceClsTranslation : Name := `HoTT0.Translation

initialize
  registerTraceClass traceClsTranslation

-- TODO: namespace `_root_.Expr` et al to `HoTT0`

/-- Maps fvarIds to their de Bruijn index. -/
abbrev TranslateM := ReaderT (AssocList FVarId Nat) MetaM

def TranslateM.run {α : Type} (x : TranslateM α) : MetaM α := ReaderT.run x {}

def withBinder {α : Type} (x : Lean.Expr) (k : TranslateM α) : TranslateM α := do
  withReader (fun s => s.mapVal (· + 1) |>.insert x.fvarId! 0) k

/-- Extract the level `u` in `Sort u`.
It must be monomorphic, i.e., may not contain universe variables. -/
def getSortLevel (l : Level) : Lean.MetaM Nat := do
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

/-- Make the HoTT0 term
`fun (A : Type l) (B : A → Type l') : Type (max l l') => code (Σ (El A) (El (B #0)))`. -/
def mkSigma {u : Level} (χ : Q(Type u)) (l l' : Nat) : Q(_root_.Expr $χ) :=
  q(.lam ($l + 1) (max $l $l' + 1) (.univ $l) <|
    .lam (max $l ($l' + 1)) (max $l $l' + 1) (.pi $l ($l' + 1) (.el <| .bvar 0) (.univ $l')) <|
      .code <|
        .sigma $l $l'
          (.el <| .bvar 1)
          (.el <| .app $l ($l' + 1) (.univ $l') (.bvar 1) (.bvar 0)))

/-- Make the HoTT0 term
`fun (A : Type l) (a b : A) : Type l => code (.Id l a b)`. -/
def mkId {u : Level} (χ : Q(Type u)) (l : Nat) : Q(_root_.Expr $χ) :=
  q(.lam ($l + 1) ($l + 1) (.univ $l) <|
    .lam $l ($l + 1) (.el <| .bvar 0) <|
      .lam $l ($l + 1) (.el <| .bvar 1) <|
        .code <| .Id $l (.el <| .bvar 2) (.bvar 1) (.bvar 0))

mutual
variable {u : Level} (χ : Q(Type u))

/-- Completeness: if the argument is well-formed in Lean,
the output is well-typed in HoTT. -/
partial def translateAsTp (e : Lean.Expr) : TranslateM (Nat × Q(_root_.Expr $χ)) := do
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

partial def translateAsTm (e : Lean.Expr) : TranslateM (Nat × Q(_root_.Expr $χ)) := do
  if isType e then
    let ⟨l, A⟩ ← translateAsTp e
    return ⟨l+1, q(.code $A)⟩
  match e with
  | .mdata _ e => translateAsTm e
  | .fvar f => do
    let eTp ← inferType e
    let .sort l ← inferType eTp | throwError "internal error (sort)"
    let n ← getSortLevel l
    match (← read).find? f with
    | some i => return ⟨n, q(.bvar $i)⟩
    | none => throwError "unexpected fvar{indentExpr e}"
  | .lam _ A .. =>
    let ⟨l, A⟩ ← translateAsTp A
    let ⟨l', b⟩ ← lambdaBoundedTelescope e 1 fun xs b => do
      let #[x] := xs | throwError "internal error (lam tm)"
      withBinder x <| translateAsTm b
    return ⟨max l l', q(.lam $l $l' $A $b)⟩
  | .app fn arg => do
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
        let #[x] := xs | throwError "internal error (Sigma.mk)"
        withBinder x <| translateAsTp B
      let ⟨_, p⟩ ← translateAsTm p
      return ⟨l, q(.fst $l $l' $A $B $p)⟩
    if e.isAppOfArity' ``Sigma.snd 3 then
      let #[A, B, p] := e.getAppArgs | throwError "internal error"
      let ⟨l, A⟩ ← translateAsTp A
      let ⟨l', B⟩ ← lambdaBoundedTelescope B 1 fun xs B => do
        let #[x] := xs | throwError "internal error (Sigma.mk)"
        withBinder x <| translateAsTp B
      let ⟨_, p⟩ ← translateAsTm p
      return ⟨l', q(.snd $l $l' $A $B $p)⟩
    if e.isAppOfArity' ``Id.refl 2 then
      let #[_, a] := e.getAppArgs | throwError "internal error (Id.refl)"
      let ⟨l, a⟩ ← translateAsTm a
      return ⟨l, q(.refl $l $a)⟩
    if e.isAppOfArity' ``Id.rec 6 then
      let #[_, a, M, r, b, h] := e.getAppArgs | throwError "internal error (Id.rec)"
      let ⟨l, a⟩ ← translateAsTm a
      let ⟨l', M⟩ ← lambdaBoundedTelescope M 2 fun xs M => do
        let #[x, h] := xs | throwError "internal error (Id.rec)"
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
    return ⟨max l l' + 1, mkSigma χ l l'⟩
  | .const ``Id [l] =>
    let l ← getSortLevel l.succ
    return ⟨l + 1, mkId χ l⟩
  | e => throwError "unsupported term{indentExpr e}"

end

end HoTT0.Translation

/- ## Command elaborator -/

namespace HoTT0.Dsl

open Lean Elab Command
open Qq

def envDiff (old new : Environment) : Array ConstantInfo := Id.run do
  let mut ret := #[]
  for (c, i) in new.constants.map₂ do
    if old.constants.map₂.contains c then continue
    if c.isInternal then continue
    ret := ret.push i
  return ret

structure CheckedDef.{u} {χ : Type u} (E : Env χ) where
  l : Nat
  val : _root_.Expr χ
  tp : _root_.Expr χ
  wf : E ∣ [] ⊢[l] val : tp

def elabDeclaration (stx : Syntax) : CommandElabM Unit := do
  -- TODO: should `hott def` have its own `consts` set stored in an environment extension?
  let (_, newEnv) ← withoutModifyingEnv' <| Command.elabDeclaration stx
  let diff := envDiff (← getEnv) newEnv
  let #[ci] := diff
    | throwError "expected exactly one definition, got {diff.size}:\
      {Lean.indentD ""}{diff.map (·.name)}"
  Command.liftTermElabM do
    let ⟨l, T⟩ ← Translation.translateAsTp q(Nat) ci.type |>.run
    let ⟨k, t⟩ ← Translation.translateAsTm q(Nat) ci.value! |>.run
    if l != k then throwError "internal error: inferred level mismatch"
    trace[HoTT0.Translation] "translated (lvl {l}){Lean.indentD ""}{t} : {T}"
    let Twf ← checkTp q(Env.empty Nat) q(⟨Env.Wf.empty _⟩) q([]) q($l) q($T)
    let ⟨vT, vTeq⟩ ← evalTpId q(show TpEnv Nat from []) q($T)
    let twf ← checkTm q(Env.empty Nat) q(⟨Env.Wf.empty _⟩) q([]) q($l) q($vT) q($t)
    let val : Q(CheckedDef <| Env.empty Nat) := q({
      l := $l
      val := $t
      tp := $T
      wf :=
        have : Fact (Env.empty Nat).Wf := ⟨Env.Wf.empty _⟩
        $twf .nil <| $vTeq .nil <| $Twf .nil
    })
    addDecl <| .defnDecl {
      name := ci.name ++ `checked
      levelParams := []
      type := q(CheckedDef <| Env.empty Nat)
      value := val
      hints := .regular 0 -- TODO: what height?
      safety := .safe
    }

/--
The command
```lean
hott def foo $params : $type := $body
```
operates by:

1. Typechecking the definition using standard Lean rules.
   The definition is not stored in the standard Lean environment.
2. Translating the Lean expression into a HoTT0 expression.
3. Typechecking the HoTT0 expression and producing a derivation tree.
   Note: Originally we wanted to instrument the Lean typechecker to do this during step 1,
   but it seemed strictly harder than implementing our own checker.
4. Storing the `HoTT0.Expr` and its derivation tree in the Lean environment.
-/

elab "hott " cmd:command : command => do
  match cmd.raw[1].getKind with
  | ``Parser.Command.definition => elabDeclaration cmd
  | _ => throwError "unhandled command:{indentD cmd}"

end HoTT0.Dsl
