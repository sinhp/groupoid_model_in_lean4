import Lean.Meta.Tactic.Simp

/-- A HoTT0 expression. -/
inductive Expr where
  /-- De Bruijn index. -/
  | bvar (i : Nat)
  /-- Dependent product. -/
  | pi (l l' : Nat) (A B : Expr)
  /-- Dependent sum. -/
  | sigma (l l' : Nat) (A B : Expr)
  /-- Lambda with the specified argument type. -/
  | lam (l l' : Nat) (A b : Expr)
  /-- Application at the specified input type `A` and output type family `B`.

  `A` is needed for NbE, but not for interpretation. -/
  | app (l l' : Nat) (A B fn arg : Expr)
  /-- Pair formation. -/
  | pair (l l' : Nat) (B t u : Expr)
  /-- First component of a pair. -/
  | fst (l l' : Nat) (A B p : Expr)
  /-- Second component of a pair. -/
  | snd (l l' : Nat) (A B p : Expr)
  /-- A type universe. -/
  | univ (l : Nat)
  /-- Type from a code. -/
  | el (a : Expr) : Expr
  /-- Code from a type. -/
  | code (A : Expr) : Expr
  deriving Inhabited, Repr, Lean.ToExpr

@[simp]
theorem Expr.sizeOf_pos (e : Expr) : 0 < sizeOf e := by
  induction e <;> { dsimp; omega }

/-- A convergent rewriting system for the HoTT0 σ-calculus. -/
-- The attribute has to be initialized here for use in downstream modules.
register_simp_attr autosubst
