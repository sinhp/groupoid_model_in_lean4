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
  | univ (l : Nat)
  /-- Type from a code. -/
  | el (a : Expr) : Expr
  /-- Code from a type. -/
  | code (A : Expr) : Expr
  deriving Repr

@[reducible]
def Expr.size : Expr → Nat
  | bvar _ => 1
  | pi A B => A.size + B.size + 1
  | lam A e => A.size + e.size + 1
  | app B fn arg => B.size + fn.size + arg.size + 1
  | univ _ => 1
  | el a => a.size + 1
  | code A => A.size + 1

@[simp]
theorem Expr.size_pos (e : Expr) : 0 < e.size := by
  induction e <;> { dsimp [size]; omega }

@[simp]
theorem Expr.size_lt_pi_size (A B : Expr) : A.size < (pi A B).size := by
  dsimp [size]; omega

@[simp]
theorem Expr.size_lt_app_size (B fn arg : Expr) : B.size < (app B fn arg).size := by
  dsimp [size]; omega

/-- `inferLvl Γ e` is such that
- if `Γ ⊢[l] e : A`, then `l = inferLvl Γ e`; and
- if `Γ ⊢[l] e` then `l = inferLvl Γ e`. -/
def Expr.inferLvl : List Expr → Expr → Nat
  | [],      bvar _       => 1337
  | A :: As, bvar 0       => inferLvl As A
  | _ :: As, bvar (i + 1) => inferLvl As (bvar i)
  | Γ,       pi A B       => max (inferLvl Γ A) (inferLvl (A :: Γ) B)
  | Γ,       lam A e      => max (inferLvl Γ A) (inferLvl (A :: Γ) e)
  | Γ,       app B _ _    => inferLvl Γ B
  | _,       univ l       => l + 1
  | Γ,       el a         => inferLvl Γ a - 1
  | Γ,       code a       => inferLvl Γ a + 1
termination_by Γ e => (e :: Γ).map Expr.size |>.sum
