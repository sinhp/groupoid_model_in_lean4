import GroupoidModel.TypeTheory.Russell_PER_MS.Basic

/-! In this section we compute the action of substitutions.

Write `↑ⁿ` for the `n`-fold weakening substitution `{n+i/i}`.
Write `σ:k` for `σ.vₖ₋₁.….v₁.v₀`.

The substitution `↑ⁿ⁺ᵏ:k`,
i.e., `{0/0,…,k-1/k-1, k+n/k,k+1+n/k+1,…}`,
arises by starting with `↑ⁿ` and traversing under `k` binders:
for example, `(ΠA. B)[↑¹] ≡ ΠA[↑¹]. B[↑².v₀] ≡ ΠA[↑¹]. B[↑¹⁺¹:1]`.

The substitution `↑ᵏ.e[↑ᵏ]:k`,
i.e., `{0/0,…,k-1/k-1, e[↑ᵏ]/k, k/k+1,k+2/k+3,…}`,
arises by starting with `id.e` and traversing under `k` binders:
for example `(ΠA. B)[id.e] ≡ ΠA[id.e]. B[↑.e[↑].v₀] ≡ ΠA[id.e]. B[↑¹.e[↑¹]:1]`.

The substitution `id.e` is used in `β`-reduction:
`(λa) b ↝ a[id.b]`. -/

/-- Substitute `↑ⁿ⁺ᵏ:k` in the de Bruijn index `i`. -/
def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

variable (n : Nat) in
/-- Substitute `↑ⁿ⁺ᵏ:k` in an expression. -/
def Expr.liftN : Expr → (k : Nat := 0) → Expr
  | .bvar i, k => .bvar (liftVar n i k)
  | .pi ty body, k => .pi (ty.liftN k) (body.liftN (k+1))
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k+1))
  | .app B fn arg, k => .app (B.liftN (k+1)) (fn.liftN k) (arg.liftN k)
  | .univ n, _ => .univ n

/-- Substitute `↑¹` in an expression. -/
abbrev Expr.lift := Expr.liftN 1

/-- Substitute `↑ᵏ.e[↑ᵏ]:k` in the de Bruijn index `i`. -/
def instVar (i : Nat) (e : Expr) (k := 0) : Expr :=
  if i < k then .bvar i else if i = k then .liftN k e else .bvar (i - 1)

/-- Substitute `↑ᵏ.e[↑ᵏ]:k` in an expression. -/
def Expr.inst : Expr → Expr → (k :_:= 0) → Expr
  | .bvar i, e, k => instVar i e k
  | .pi ty body, e, k => .pi (ty.inst e k) (body.inst e (k+1))
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst e (k+1))
  | .app B fn arg, e, k => .app (B.inst e (k+1)) (fn.inst e k) (arg.inst e k)
  | .univ n, _, _ => .univ n
