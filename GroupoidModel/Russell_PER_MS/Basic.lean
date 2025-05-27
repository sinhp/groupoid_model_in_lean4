/-! Presentation with
- PER-style equality judgments; and
- Russell-style universes up to N; and
- judgments stratified by universe.
-/

/-- A Hott₀ expression. -/
inductive Expr where
  /-- De Bruijn index. -/
  | bvar (i : Nat)
  /-- Dependent product. -/
  | pi (l l' : Nat) (A B : Expr)
  /-- Dependent sum. -/
  | sigma (l l' : Nat) (A B : Expr)
  /-- Lambda. -/
  | lam (l l' : Nat) (ty body : Expr)
  /-- Application at the specified output type. -/
  | app (l l' : Nat) (B fn arg : Expr)
  /-- Pair formation. -/
  | pair (l l' : Nat) (B t u : Expr)
  /-- First component. -/
  | fst (l l' : Nat) (A B p : Expr)
  /-- Second component. -/
  | snd (l l' : Nat) (A B p : Expr)
  /-- (Russell) type universe. -/
  | univ (l : Nat)
  /-- Type from a code. -/
  | el (a : Expr) : Expr
  /-- Code from a type. -/
  | code (A : Expr) : Expr
  deriving Repr

@[simp]
theorem Expr.sizeOf_pos (e : Expr) : 0 < sizeOf e := by
  induction e <;> { dsimp; omega }
