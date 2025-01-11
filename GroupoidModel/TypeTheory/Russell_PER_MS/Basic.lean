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
  | pi (A B : Expr)
  /-- Lambda. -/
  | lam (ty body : Expr)
  /-- Application at the specified output type. -/
  | app (B fn arg : Expr)
  /-- (Russell) type universe. -/
  | univ (n : Nat)
  deriving Repr
