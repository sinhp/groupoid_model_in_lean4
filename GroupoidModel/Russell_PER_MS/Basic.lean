/-! Presentation with
- PER-style equality judgments; and
- Russell-style universes up to N; and
- judgments stratified by universe.
-/

set_option autoImplicit false -- no, bad.

/-- A Hott₀ expression. -/
inductive Expr where
  /-- De Bruijn index. -/
  | bvar (i : Nat)
  /-- Dependent product. -/
  | pi (l l' : Nat) (A B : Expr)
  /-- Lambda. -/
  | lam (l l' : Nat) (ty body : Expr)
  /-- Application at the specified output type. -/
  | app (l l' : Nat) (B fn arg : Expr)
  /-- (Russell) type universe. -/
  | univ (l : Nat)
  /-- Type from a code. -/
  | el (a : Expr) : Expr
  /-- Code from a type. -/
  | code (A : Expr) : Expr
  deriving Repr
