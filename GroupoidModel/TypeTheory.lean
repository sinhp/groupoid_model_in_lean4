import GroupoidModel.NaturalModel

set_option autoImplicit true

namespace Bla

inductive Expr where
  | bvar (n : Nat)
  | univ
  | app (f a : Expr)
  | lam (ty val : Expr)
  | pi (ty A : Expr)

def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

theorem liftVar_lt (h : i < k) : liftVar n i k = i := if_pos h
theorem liftVar_le (h : k ≤ i) : liftVar n i k = n + i := if_neg (Nat.not_lt.2 h)

theorem liftVar_base : liftVar n i = n + i := liftVar_le (Nat.zero_le _)
@[simp] theorem liftVar_base' : liftVar n i = i + n := Nat.add_comm .. ▸ liftVar_le (Nat.zero_le _)

@[simp] theorem liftVar_zero : liftVar n 0 (k+1) = 0 := by simp [liftVar]
@[simp] theorem liftVar_succ : liftVar n (i+1) (k+1) = liftVar n i k + 1 := by
  simp [liftVar, Nat.succ_lt_succ_iff]; split <;> simp [Nat.add_assoc]

theorem liftVar_lt_add (self : i < k) : liftVar n i j < k + n := by
  simp [liftVar]
  split <;> rename_i h
  · exact Nat.lt_of_lt_of_le self (Nat.le_add_right ..)
  · rw [Nat.add_comm]; exact Nat.add_lt_add_right self _

variable (n : Nat) in
def Expr.liftN : Expr → (k :_:= 0) → Expr
  | bvar i, k => bvar (liftVar n i k)
  | .univ, _ => .univ
  | .app fn arg, k => .app (fn.liftN k) (arg.liftN k)
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k+1))
  | .pi ty body, k => .pi (ty.liftN k) (body.liftN (k+1))

abbrev Expr.lift := Expr.liftN 1

mutual
inductive HasType : List Expr → Expr → Expr → Type
  | var {A Γ} : HasType (A :: Γ) (.bvar 0) A.lift
  | weak {e A Γ} : HasType Γ e A → HasType (A :: Γ) e.lift A.lift
  | lam {A B e Γ} : IsType Γ A → HasType (A :: Γ) e B → HasType Γ (.lam A e) (.pi A B)

inductive IsType : List Expr → Expr → Type
  | small {A Γ} : HasType Γ A .univ → IsType Γ A
  | univ {Γ} : IsType Γ .univ
end

example : HasType [] (Expr.lam .univ (.bvar 0)) (Expr.pi .univ .univ) :=
  .lam .univ .var

universe u v
open CategoryTheory NaturalModel IsPresentable
open Functor Limits Opposite Representable
noncomputable section

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]
variable {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) [NaturalModel tp]

def wU : Ty.obj (op Γ) := Ty.map (terminal.from Γ).op (U tp)

inductive CtxStack [IsPresentable tp] : Ctx → Type u where
  | nil : CtxStack (⊤_ Ctx)
  | cons {Γ} (A : Ty.obj (op Γ)) : CtxStack Γ → CtxStack (ext tp Γ A)

def Context [IsPresentable tp] : Type u := Σ Γ, CtxStack tp Γ
section variable {tp}
abbrev Context.ty (Γ : Context tp) := Ty.obj (op Γ.1)
abbrev Context.tm (Γ : Context tp) := Tm.obj (op Γ.1)
def Context.nil : Context tp := ⟨_, .nil⟩
def Context.cons (Γ : Context tp) (A : Γ.ty) : Context tp := ⟨_, .cons A Γ.2⟩
def Context.weak (Γ : Context tp) (A : Γ.ty)
  {P : Psh Ctx} : P.obj (op Γ.1) → P.obj (op (cons Γ A).1) :=
  P.map (X := op Γ.1) (op (disp Γ.1 A))

protected def Context.var (Γ : Context tp) (i : ℕ) : Part Γ.tm :=
  match Γ, i with
  | ⟨_, .nil⟩, _ => .none
  | ⟨_, .cons _ _⟩, 0 => pure <| var ..
  | ⟨_, .cons _ Γ⟩, n+1 => Context.weak ⟨_, Γ⟩ _ <$> Context.var ⟨_, Γ⟩ n

def substCons (Γ Δ : Ctx) (A : Ty.obj (op Δ)) (σ : Γ ⟶ Δ)
    (e : Tm.obj (op Γ)) (eTy : tp.app (op Γ) e = Ty.map σ.op A) :
    Γ ⟶ ext tp Δ A := by
  refine Yoneda.fullyFaithful.1 <| (disp_pullback (tp := tp) A).isLimit.lift <|
    PullbackCone.mk (yonedaEquiv.2 e) (yoneda.map σ) ?_
  sorry

def el {Γ : Context tp} (A : Γ.tm) (tyA : tp.app (op Γ.1) A = wU tp) : Γ.ty :=
  (El (tp := tp)).app _ <| sorry

end


mutual

def ofCtx : List Expr → Part (Context tp)
  | [] => pure .nil
  | A :: Γ => do let Γ ← ofCtx Γ; Γ.cons (← ofType Γ A)

def ofType (Γ : Context tp) : Expr → Part Γ.ty
  | .bvar i =>
    sorry -- Context.var _ i
  | _ => .none

end
