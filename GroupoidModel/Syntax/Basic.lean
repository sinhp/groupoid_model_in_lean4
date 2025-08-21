import Lean.Meta.Tactic.Simp

universe u

variable (χ : Type u) in
/-- A HoTT0 expression with constants indexed by `χ`. -/
inductive Expr where
  /-- A closed term constant in the environment. -/
  | const (c : χ)
  /-- De Bruijn index. -/
  | bvar (i : Nat)
  /-- Dependent product. -/
  | pi (l l' : Nat) (A B : Expr)
  /-- Lambda with the specified argument type. -/
  | lam (l l' : Nat) (A b : Expr)
  /-- Application at the specified output type family `B`. -/
  | app (l l' : Nat) (B fn arg : Expr)
  /-- Dependent sum. -/
  | sigma (l l' : Nat) (A B : Expr)
  /-- Pair formation. -/
  | pair (l l' : Nat) (B t u : Expr)
  /-- First component of a pair. -/
  | fst (l l' : Nat) (A B p : Expr)
  /-- Second component of a pair. -/
  | snd (l l' : Nat) (A B p : Expr)
  /-- Identity type. -/
  -- TODO: capitalize all the types
  | Id (l : Nat) (A t u : Expr)
  /-- A reflexive identity. -/
  | refl (l : Nat) (t : Expr)
  /-- Eliminates an identity. -/
  | idRec (l l' : Nat) (t M r u h : Expr)
  /-- A type universe. -/
  | univ (l : Nat)
  /-- Type from a code. -/
  | el (a : Expr)
  /-- Code from a type. -/
  | code (A : Expr)
  deriving Inhabited, Repr, Lean.ToExpr

@[simp]
theorem Expr.sizeOf_pos {χ} (e : Expr χ) : 0 < sizeOf e := by
  induction e <;> { dsimp; omega }

/-- A convergent rewriting system for the HoTT0 σ-calculus. -/
-- The attribute has to be initialized here for use in downstream modules.
register_simp_attr autosubst
