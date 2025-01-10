/-! Presentation with
- Russell-style universes up to N; and
- PER-style equal-expressions judgment; and
- explicit substitutions; and
- judgments stratified by universe.
-/

set_option autoImplicit false -- no, bad.

section RawSyntax

mutual
/-- A HoTT₀ substitution. -/
inductive Subst where
  /-- Identity substitution. -/
  | id
  /-- Weakening `↑`. -/
  -- TODO: For computation we may want to represent `n`-fold weakening directly.
  | wk (A : Expr)
  /-- `comp σ τ` is in-order composition `σ;τ`. -/
  | comp (σ τ : Subst)
  /-- Extension `σ.t` by a term. -/
  | ext (σ : Subst) (t : Expr)
  deriving Repr

/-- A HoTT₀ expression. -/
inductive Expr where
  /-- De Bruijn index. -/
  | bvar (i : Nat)
  /-- Dependent product. -/
  | pi (A B : Expr)
  /-- Lambda. -/
  | lam (ty body : Expr)
  /-- Application at an output type. -/
  | app (B fn arg : Expr)
  /-- (Russell) type universe. -/
  | univ (n : Nat)
  /-- Explicit substitution. -/
  | sb (t : Expr) (σ : Subst)
  deriving Repr
end

end RawSyntax

/-! In this section we specify typing judgments of the type theory
as `Prop`-valued relations. -/
section Typing
section Notation -- TODO make notation local

declare_syntax_cat judgment
syntax:25 term:51 " ⊢[" term:51 "] " judgment:50 : term
syntax:25 term:51 " ⊢ₛ " judgment:50 : term

syntax:50 term:51 " : " term:51 : judgment
syntax:50 term:51 " ≡ " term:51 " : " term:51 : judgment

set_option hygiene false in
macro_rules
  | `($Γ ⊢[$l:term] $t:term : $A:term) => `($Γ ⊢[$l] $t:term ≡ $t : $A)
  | `($Γ ⊢[$l:term] $t:term ≡ $u:term : $A:term) => `(EqExpr $Γ $l $t $u $A)
  | `($Δ ⊢ₛ $σ:term ≡ $τ:term : $Γ:term) => `(EqSubst $Δ $σ $τ $Γ)
  | `($Δ ⊢ₛ $σ:term : $Γ:term) => `($Δ ⊢ₛ $σ:term ≡ $σ : $Γ)

end Notation

/-- `Lookup Γ i A` implies that `Γ ⊢ .bvar i : A`. -/
inductive Lookup : List Expr → Nat → Expr → Prop where
  | zero {Γ A} : Lookup (A::Γ) 0 (A.sb (.wk A))
  | succ {Γ i A B} : Lookup Γ i A → Lookup (B::Γ) (i+1) (A.sb (.wk B))

/-- The maximum `l` for which `Γ ⊢[l+1] A : .univ l` makes sense.
When set to `0`, types cannot be quantified over at all,
and there is no type-level computation. -/
def univMax := 37

/-! ## Typing rules

Convention on order of implicit parameters:
contexts, substitutions, types, terms, de Bruijn indices, universe levels.

`presupp` indicates presuppositions.
We don't add all of them,
just the ones needed to make inversion easy. -/

mutual

inductive EqSubst : List Expr → Subst → Subst → List Expr → Prop
  -- Congruences / constructors
  | cong_id {Γ} :
    Γ ⊢ₛ .id : Γ

  | cong_wk {Γ A l} :
    Γ ⊢[l+1] A : .univ l →
    A :: Γ ⊢ₛ .wk A : Γ

  | cong_comp {Θ Δ Γ ρ ρ' σ σ'} :
    Θ ⊢ₛ ρ ≡ ρ' : Δ →
    Δ ⊢ₛ σ ≡ σ' : Γ →
    Θ ⊢ₛ .comp ρ σ ≡ .comp ρ' σ' : Γ

  | cong_ext {Δ Γ σ σ' A t t' l} :
    Δ ⊢ₛ σ ≡ σ' : Γ →
    Δ ⊢[l] t ≡ t' : A.sb σ →
    Δ ⊢ₛ .ext σ t ≡ .ext σ' t' : A :: Γ

  | cong_ext_univMax {Δ Γ σ σ' A t t'} :
    Δ ⊢ₛ σ ≡ σ' : Γ →
    Δ ⊢[univMax+1] t ≡ t' : .univ univMax →
    Δ ⊢ₛ .ext σ t ≡ .ext σ' t' : A :: Γ

  -- σ-reductions
  | comp_ext_wk {Δ Γ σ A t l} :
    Δ ⊢ₛ σ : Γ →
    Δ ⊢[l] t : A.sb σ →
    Δ ⊢ₛ .comp (.ext σ t) (.wk A) ≡ σ : Γ

  | comp_ext_wk_univMax {Δ Γ σ A t} :
    Δ ⊢ₛ σ : Γ →
    Δ ⊢[univMax+1] t : .univ univMax →
    Δ ⊢ₛ .comp (.ext σ t) (.wk A) ≡ σ : Γ

  | comp_ext {Θ Δ Γ ρ σ A t l} :
    Θ ⊢ₛ ρ : Δ →
    Δ ⊢ₛ σ : Γ →
    Δ ⊢[l] t : .sb A σ →
    Δ ⊢ₛ .comp ρ (.ext σ t) ≡ .ext (.comp ρ σ) (t.sb ρ) : Γ

  -- Category laws
  | comp_id {Δ Γ σ} :
    Δ ⊢ₛ σ : Γ →
    Δ ⊢ₛ .comp σ .id ≡ σ : Γ

  | id_comp {Δ Γ σ} :
    Δ ⊢ₛ σ : Γ →
    Δ ⊢ₛ .comp .id σ ≡ σ : Γ

  | comp_assoc {H Θ Δ Γ ρ σ τ} :
    H ⊢ₛ ρ : Θ →
    Θ ⊢ₛ σ : Δ →
    Δ ⊢ₛ τ : Γ →
    H ⊢ₛ .comp (.comp ρ σ) τ ≡ .comp ρ (.comp σ τ) : Γ

  -- Symmetric-transitive closure
  | symm {Δ Γ σ σ'} :
    Δ ⊢ₛ σ ≡ σ' : Γ →
    Δ ⊢ₛ σ' ≡ σ : Γ

  | trans {Δ Γ σ σ' σ''} :
    Δ ⊢ₛ σ ≡ σ' : Γ →
    Δ ⊢ₛ σ' ≡ σ'' : Γ →
    Δ ⊢ₛ σ ≡ σ'' : Γ

inductive EqExpr : List Expr → Nat → Expr → Expr → Expr → Prop
  -- Congruences / constructors
  | cong_bvar {Γ A i l} :
    Γ ⊢[l+1] A : .univ l →
    Lookup Γ i A →
    Γ ⊢[l] .bvar i : A

  | cong_pi {Γ A A' B B' l l'} :
    Γ ⊢[l+1] A ≡ A' : .univ l →
    A :: Γ ⊢[l'+1] B ≡ B' : .univ l' →
    Γ ⊢[max l l' + 1] .pi A B ≡ .pi A' B' : .univ (max l l')

  | cong_lam {Γ A A' B t t' l l'} :
    Γ ⊢[l+1] A ≡ A' : .univ l →
    A :: Γ ⊢[l'] t ≡ t' : B →
    Γ ⊢[max l l'] .lam A t ≡ .lam A' t' : .pi A B

  | cong_app {Γ A B B' f f' a a' l l'} :
    A :: Γ ⊢[l' + 1] B ≡ B' : .univ l' →
    Γ ⊢[max l l'] f ≡ f' : .pi A B →
    Γ ⊢[l] a ≡ a' : A →
    Γ ⊢[l'] .app B f a ≡ .app B' f' a' : B.sb (Subst.id.ext a)

  | cong_sb {Δ Γ σ σ' A t t' l} :
    Γ ⊢[l] t ≡ t' : A →
    Δ ⊢ₛ σ ≡ σ' : Γ →
    Δ ⊢[l] t.sb σ ≡ t'.sb σ' : A.sb σ

  -- Reductions
  | app_lam {Γ A B t u l l'} :
    A :: Γ ⊢[l'+1] B : .univ l' → -- presupp
    A :: Γ ⊢[l'] t : B →
    Γ ⊢[l] u : A →
    Γ ⊢[l'] .app B (.lam A t) u ≡ t.sb (Subst.id.ext u) : B.sb (Subst.id.ext u)

  -- Expansions
  | eta {Γ A B t l} :
    Γ ⊢[l] t : .pi A B →
    Γ ⊢[l] t ≡ .lam A (.app B (t.sb <| .wk A) (.bvar 0)) : .pi A B

  -- σ-reductions
  | bvar_id {Γ A i l} :
    Γ ⊢[l] .bvar i : A →
    Γ ⊢[l] .sb (.bvar i) .id ≡ .bvar i : A

  | bvar_wk {Γ A B i l l'} :
    Γ ⊢[l+1] A : .univ l → -- presupp
    Γ ⊢[l'+1] B : .univ l' → -- presupp
    Γ ⊢[l] .bvar i : A →
    B :: Γ ⊢[l] .sb (.bvar i) (.wk B) ≡ .bvar (i + 1) : A.sb (.wk B)

  | pi_sb {Δ Γ σ A B l l'} :
    Δ ⊢ₛ σ : Γ →
    Γ ⊢[l+1] A : .univ l →
    A :: Γ ⊢[l'+1] B : .univ l' →
    Δ ⊢[max l l' + 1] .sb (.pi A B) σ ≡
                      .pi (A.sb σ) (B.sb $ (Subst.comp $ .wk $ A.sb σ) σ |>.ext (.bvar 0)) :
                      .univ (max l l')

  | lam_sb {Δ Γ σ A B t l l'} :
    Δ ⊢ₛ σ : Γ →
    Γ ⊢[l+1] A : .univ l → -- presupp
    A :: Γ ⊢[l'+1] B : .univ l' → -- presupp
    A :: Γ ⊢[l'] t : B →
    Δ ⊢[max l l'] .sb (.lam A t) σ ≡ .lam (A.sb σ) (t.sb $ (Subst.comp $ .wk $ A.sb σ) σ |>.ext (.bvar 0)) :
      .pi (A.sb σ) (B.sb $ (Subst.comp $ .wk $ A.sb σ) σ |>.ext (.bvar 0))

  | app_sb {Δ Γ σ A B f a l l'} :
    Δ ⊢ₛ σ : Γ →
    A :: Γ ⊢[l'+1] B : .univ l' → -- presupp
    Γ ⊢[max l l'] f : .pi A B →
    Γ ⊢[l] a : A →
    Δ ⊢[l'] .sb (.app B f a) σ ≡ .app (.sb B σ) (.sb f σ) (.sb a σ) : B.sb (σ.ext (.sb a σ))

  | univ_sb {Δ Γ σ l} :
    Δ ⊢ₛ σ : Γ →
    l < univMax →
    Δ ⊢[l+2] .sb (.univ l) σ ≡ .univ l : .univ (l + 1)

  | sb_sb {Θ Δ Γ ρ σ A t l} :
    Θ ⊢ₛ ρ : Δ →
    Δ ⊢ₛ σ : Γ →
    Γ ⊢[l] t : A →
    Θ ⊢[l] .sb (.sb t σ) ρ ≡ .sb t (.comp ρ σ) : .sb A (.comp ρ σ)

  -- Conversion (source of all evil)
  | conv {Γ A A' t t' l} :
    Γ ⊢[l+1] A ≡ A' : .univ l →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t ≡ t' : A'

  /-- Absolutely scuffed rule:
  at the univMax of the universe hierarchy there is no equational theory
  (so e.g. `Γ ⊢ .sb (.univ univMax) .id ≢ .univ univMax`),
  but we nevertheless want to conclude `Γ ⊢ A : .univ univMax`
  from `Γ ⊢ A : .sb (.univ univMax) .id`. -/
  | conv_univMax {Γ A A' U} :
    Γ ⊢[univMax+1] A ≡ A' : U →
    Γ ⊢[univMax+1] A ≡ A' : .univ univMax

  -- Symmetric-transitive closure
  | symm {Γ A t t' l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t : A

  | trans {Γ A t t' t'' l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t'' : A →
    Γ ⊢[l] t ≡ t'' : A

end

/-! Pretty-printers. -/

section PrettyPrinting
open Lean PrettyPrinter

@[app_unexpander EqExpr]
def EqExpr.unexpand : Unexpander
  | `($_ $Γ $l $t $t' $A) =>
    if t == t' then
      `($Γ ⊢[$l] $t:term : $A)
    else
      `($Γ ⊢[$l] $t:term ≡ $t' : $A)
  | _ => throw ()

@[app_unexpander EqSubst]
def EqSubst.unexpand : Unexpander
  | `($_ $Δ $σ $σ' $Γ) =>
    if σ == σ' then
      `($Δ ⊢ₛ $σ:term : $Γ)
    else
      `($Δ ⊢ₛ $σ:term ≡ $σ' : $Γ)
  | _ => throw ()

end PrettyPrinting
