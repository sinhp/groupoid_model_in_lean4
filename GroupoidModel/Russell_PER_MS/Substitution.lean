import GroupoidModel.Russell_PER_MS.Basic

/-! In this module we compute the action of substitutions. -/

/-! ## Lifting/weakening

Write `↑ⁿ` for the `n`-fold weakening substitution `{n+i/i}`.
Write `σ:k` for `σ.vₖ₋₁.….v₁.v₀`.

The *thinning* substitution `↑ⁿ⁺ᵏ:k`,
i.e., `{0/0,…,k-1/k-1, k+n/k,k+1+n/k+1,…}`,
arises by starting with `↑ⁿ` and traversing under `k` binders:
for example, `(ΠA. B)[↑¹] ≡ ΠA[↑¹]. B[↑².v₀] ≡ ΠA[↑¹]. B[↑¹⁺¹:1]`.
Applying `↑ⁿ⁺ᵏ:k` moves an expression into a context
with `n` new binders inserted at index `k`:
`Γ.Bₙ.….B₁.Aₖ₋₁[↑ⁿ].….A₀[⋯] ⊢ ↑ⁿ⁺ᵏ:k : Γ.Aₖ₋₁.….A₀`.
(With `k = 0`, the codomain is just `Γ`.) -/

/-- Substitute `↑ⁿ⁺ᵏ:k` in the de Bruijn index `i`. -/
def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

variable (n : Nat) in
/-- Substitute `↑ⁿ⁺ᵏ:k` in an expression. -/
def Expr.liftN : Expr → (k : Nat := 0) → Expr
  | .bvar i,            k => .bvar (liftVar n i k)
  | .pi l l' A B,       k => .pi l l' (A.liftN k) (B.liftN (k+1))
  | .lam l l' A t,      k => .lam l l' (A.liftN k) (t.liftN (k+1))
  | .app l l' B fn arg, k => .app l l' (B.liftN (k+1)) (fn.liftN k) (arg.liftN k)
  | .univ l,            _ => .univ l
  | .el a,              k => .el (a.liftN k)
  | .code A,            k => .code (A.liftN k)

/-- Substitute `↑¹` in an expression. -/
abbrev Expr.lift := Expr.liftN 1

/-! ## Instantiation

The substitution `↑ᵏ.e[↑ᵏ]:k`,
i.e., `{0/0,…,k-1/k-1, e[↑ᵏ]/k, k/k+1,k+2/k+3,…}`,
arises by starting with `id.e` and traversing under `k` binders:
for example `(ΠA. B)[id.e] ≡ ΠA[id.e]. B[↑.e[↑].v₀] ≡ ΠA[id.e]. B[↑¹.e[↑¹]:1]`.
Applying `↑ᵏ.e[↑ᵏ]:k` moves an expression `t` into a context
with the `k`th binder removed:
`Γ.Aₖ₋₁[id.e].….A₀[⋯] ⊢ ↑ᵏ.e[↑ᵏ]:k : Γ.B.Aₖ₋₁.….A₀`.

The substitution `id.e` is used in `β`-reduction:
`(λa) b ↝ a[id.b]`. -/

/-- Substitute `↑ᵏ.e[↑ᵏ]:k` in the de Bruijn index `i`. -/
def instVar (i : Nat) (e : Expr) (k := 0) : Expr :=
  if i < k then .bvar i else if i = k then .liftN k e else .bvar (i - 1)

/-- Substitute `↑ᵏ.e[↑ᵏ]:k` in an expression. -/
def Expr.inst : Expr → Expr → (k :_:= 0) → Expr
  | .bvar i,            e, k => instVar i e k
  | .pi l l' A B,       e, k => .pi l l' (A.inst e k) (B.inst e (k+1))
  | .lam l l' A t,      e, k => .lam l l' (A.inst e k) (t.inst e (k+1))
  | .app l l' B fn arg, e, k => .app l l' (B.inst e (k+1)) (fn.inst e k) (arg.inst e k)
  | .univ l,            _, _ => .univ l
  | .el a,              e, k => .el (a.inst e k)
  | .code A,            e, k => .code (A.inst e k)

/-! ## Lemmas -/

@[simp]
theorem liftVar_zero (i k) : liftVar 0 i k = i := by
  simp [liftVar]

@[simp]
theorem liftVar_zero' (n i) : liftVar n i 0 = n + i := by
  simp [liftVar]

@[simp]
theorem Expr.lift_zero (t : Expr) (k) : t.liftN 0 k = t := by
  induction t generalizing k <;> simp [liftN, *]

