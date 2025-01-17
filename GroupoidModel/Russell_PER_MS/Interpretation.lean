import GroupoidModel.Russell_PER_MS.Typing
import GroupoidModel.Russell_PER_MS.UHom

import GroupoidModel.ForMathlib

universe v u

open CategoryTheory Limits

noncomputable section

namespace NaturalModelBase.UHomSeq

variable {Ctx : Type u} [Category.{v, u} Ctx] [HasTerminal Ctx]

/-- `s.CtxStack Γ` witnesses a sequence of context extension operations in `s`
that built the semantic context `Γ`. -/
inductive CtxStack (s : UHomSeq Ctx) : Ctx → Type (max u v) where
  | nil : CtxStack s (⊤_ Ctx)
  | cons {Γ} {l : Nat} (llen : l < s.length + 1) (A : y(Γ) ⟶ s[l].Ty) :
    CtxStack s Γ → CtxStack s (s[l].ext A)

variable {s : UHomSeq Ctx}

protected def CtxStack.var {Γ : Ctx} {l : Nat} (llen : l < s.length + 1) :
    s.CtxStack Γ → ℕ → Part (y(Γ) ⟶ s[l].Tm)
  | .nil, _ => .none
  | .cons (l := l') _ A _, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ s[l'].var A
  | .cons (l := l') _ A S, n+1 => do
    let v ← S.var llen n
    return ym(s[l'].disp A) ≫ v

/-- A "contextual" context (as in Cartmell's contextual categories),
i.e., one of the form `1.Aₙ₋₁.….A₀`,
together with the list `[Aₙ₋₁, …, A₀]`.

This kind of context can be destructured. -/
def CCtx (s : UHomSeq Ctx) : Type (max u v) := Σ Γ : Ctx, s.CtxStack Γ

def CCtx.nil (s : UHomSeq Ctx) : s.CCtx :=
  ⟨⊤_ Ctx, .nil⟩

def CCtx.cons (Γ : s.CCtx) {i : Nat} (ilen : i < s.length + 1)
    (A : y(Γ.1) ⟶ s[i].Ty) : s.CCtx :=
  ⟨s[i].ext A, .cons ilen A Γ.2⟩

protected def CCtx.var {l : Nat} (llen : l < s.length + 1) (Γ : s.CCtx) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Tm) :=
  Γ.2.var llen i

variable [SmallCategory Ctx] [HasTerminal Ctx] (s : UHomSeqPis Ctx)

mutual

/- Recall: cannot have `ofCtx` appearing in the output types
(that would be induction-recursion or something like it),
thus the context must be an *input*. -/
def ofType (Γ : s.CCtx) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Ty)
  | .pi i j A B, _ =>
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let B ← ofType (Γ.cons ilen A) j B
    return lij ▸ s.mkPi ilen jlen A B
  | .univ i, _ =>
    Part.assert (l = i + 1) fun li => do
    return li ▸ (s.homSucc i).wkU Γ.1
  | .el t, _ => do
    Part.assert (l < s.length) fun llen => do
    let A ← ofTerm Γ (l+1) t
    Part.assert (A ≫ s[l+1].tp = (s.homSucc l).wkU Γ.1) fun A_tp => do
    return s.el llen A A_tp
  | _, _ => .none

def ofTerm (Γ : s.CCtx) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Tm)
  | .bvar i, llen => Γ.var llen i
  | .lam i j A e, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let e ← ofTerm (Γ.cons ilen A) j e
    return lij ▸ s.mkLam ilen jlen A e
  | .app i j B f a, _ => do
    Part.assert (l = j) fun lj => do
    Part.assert (i < s.length + 1) fun ilen => do
    have jlen : j < s.length + 1 := by omega
    let f ← ofTerm Γ (max i j) f
    let a ← ofTerm Γ i a
    let B ← ofType (Γ.cons ilen (a ≫ s[i].tp)) j B
    Part.assert (f ≫ s[max i j].tp = s.mkPi ilen jlen (a ≫ s[i].tp) B) fun h =>
    return lj ▸ s.mkApp ilen jlen _ B f h a rfl
  | .code t, _ =>
    Part.assert (0 < l) fun lpos => do
    let A ← ofType Γ (l-1) t
    return cast (by congr 3; omega) <| s.code (by omega) A
  | _, _ => .none

end

end NaturalModelBase.UHomSeq
