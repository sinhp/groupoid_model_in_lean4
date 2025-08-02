import Lean
import Qq
import Mathlib.Util.WhatsNew
import GroupoidModel.Syntax.Typechecker.Synth

/-! ## Translation from Lean to HoTT0 -/

namespace HoTT0.Translation

open Qq Lean Meta

-- TODO: namespace `_root_.Expr` et al to `HoTT0`

/-- Maps fvarIds to their de Bruijn index. -/
abbrev TranslateM := ReaderT (AssocList FVarId Nat) MetaM

def TranslateM.run {α : Type} (x : TranslateM α) : MetaM α := ReaderT.run x {}

def withBinder {α : Type} (x : Lean.Expr) (k : TranslateM α) : TranslateM α := do
  withReader (fun s => s.mapVal (· + 1) |>.insert x.fvarId! 0) k

def getLevel (l : Level) : Lean.MetaM Nat := do
  match l.toNat with
  | .some (n+1) => return n
  | .some 0 => throwError "unsupported universe{indentExpr <| .sort l}"
  | .none => throwError "unsupported polymorphic universe level in{indentExpr <| .sort l}"

mutual
/-- Completeness: if the argument is well-formed in Lean,
the output is well-typed in HoTT. -/
partial def translateTp : Lean.Expr → TranslateM (Nat × Q(_root_.Expr))
  | e@(.bvar ..) => throwError "unexpected bvar{indentExpr e}"
  | e@(.fvar ..) => do
    let ⟨l, f⟩ ← translateTm e
    return ⟨l-1, q(.el $f)⟩
  | .sort l => do
    let n : Nat ← getLevel l
    return ⟨n+1, q(.univ $n)⟩
  | e@(.app ..) => do
    let ⟨l+1, a⟩ ← translateTm e
      | throwError "universe level too low in{indentExpr e}"
    return ⟨l, q(.el $a)⟩
  | e@(.forallE _ A ..) =>
    Meta.forallBoundedTelescope e (some 1) fun xs B => do
      let #[x] := xs | throwError "internal error (forall tp)"
      let ⟨l, A⟩ ← translateTp A
      let ⟨l', B⟩ ← withBinder x <| translateTp B
      return ⟨max l l', q(.pi $l $l' $A $B)⟩
  | e@(.letE ..) => throwError "let-binding not supported in{indentExpr e}"
  | .mdata _ e => translateTp e
  -- | .proj .. => sorry
  | e => throwError "unsupported type{indentExpr e}"

partial def translateTm : Lean.Expr → TranslateM (Nat × Q(_root_.Expr))
  | e@(.bvar ..) => throwError "unexpected bvar{indentExpr e}"
  | e@(.fvar f) => do
    let eTp ← inferType e
    let .sort l ← inferType eTp | throwError "internal error (sort)"
    let n ← getLevel l
    match (← read).find? f with
    | some i => return ⟨n, q(.bvar $i)⟩
    | none => throwError "unexpected fvar{indentExpr e}"
  | .sort l => do
    let n : Nat ← getLevel l
    return ⟨n+2, q(.code <| .univ $n)⟩
  | .app fn arg => do
    let fnTp ← inferType fn
    let ⟨_, fn⟩ ← translateTm fn
    let ⟨l, arg⟩ ← translateTm arg
    forallBoundedTelescope fnTp (some 1) fun xs B => do
      let #[x] := xs | throwError "internal error (app tm)"
      let ⟨l', B⟩ ← withBinder x <| translateTp B
      return ⟨l', q(.app $l $l' $B $fn $arg)⟩
  | e@(.lam _ A ..) =>
    Meta.lambdaBoundedTelescope e 1 fun xs b => do
      let #[x] := xs | throwError "internal error (lam tm)"
      let ⟨l, A⟩ ← translateTp A
      let ⟨l', b⟩ ← withBinder x <| translateTm b
      return ⟨max l l', q(.lam $l $l' $A $b)⟩
  | e@(.forallE ..) => do
    let ⟨l, A⟩ ← translateTp e
    return ⟨l+1, q(.code $A)⟩
  | e@(.letE ..) => throwError "let-binding not supported in{indentExpr e}"
  -- | .lit .. => sorry
  | .mdata _ e => translateTm e
  -- | .proj .. => sorry
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

structure CheckedDef where
  l : Nat
  val : _root_.Expr
  tp : _root_.Expr
  wf : [] ⊢[l] val : tp

def elabDeclaration (stx : Syntax) : CommandElabM Unit := do
  -- TODO: should `hott def` have its own `consts` set stored in an environment extension?
  let (_, newEnv) ← withoutModifyingEnv' <| Command.elabDeclaration stx
  let diff := envDiff (← getEnv) newEnv
  let #[ci] := diff
    | throwError "expected exactly one definition, got {diff.size}:\
      {Lean.indentD ""}{diff.map (·.name)}"
  Command.liftTermElabM do
    let ⟨l, T⟩ ← Translation.translateTp ci.type |>.run
    let ⟨_, t⟩ ← Translation.translateTm ci.value! |>.run
    let Twf ← checkTp q([]) q($l) q($T)
    let ⟨vT, vTeq⟩ ← evalTpId q([]) q($T)
    let twf ← checkTm q([]) q($l) q($vT) q($t)
    let val : Q(CheckedDef) := q({
      l := $l
      val := $t
      tp := $T
      wf := $twf .nil <| $vTeq .nil <| $Twf .nil
    })
    addDecl <| .defnDecl {
      name := ci.name ++ `checked
      levelParams := []
      type := q(CheckedDef)
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

/-! ## Tests -/

-- This test ensures that `El (code A) ≡ A`.
#guard_msgs in
hott def el_code {A : Type} (a : A) : A :=
  (fun (α : Type) (x : α) => x) ((fun (α : Type 1) (x : α) => x) Type A) a
