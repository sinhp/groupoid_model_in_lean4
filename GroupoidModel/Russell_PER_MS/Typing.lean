import GroupoidModel.Russell_PER_MS.Substitution

/-! In this file we specify typing judgments of the type theory
as `Prop`-valued relations. -/

section Notation -- TODO make notation local

declare_syntax_cat judgment
syntax:25 term:51 " ⊢[" term:51 "] " judgment:50 : term

syntax:50 term:51 : judgment
syntax:50 term:51 " ≡ " term:51 : judgment
syntax:50 term:51 " : " term:51 : judgment
syntax:50 term:51 " ≡ " term:51 " : " term:51 : judgment

set_option hygiene false in
macro_rules
  | `($Γ ⊢[$l:term] $t:term : $A:term) => `($Γ ⊢[$l] $t:term ≡ $t : $A)
  | `($Γ ⊢[$l:term] $A:term ≡ $B:term) => `(EqTp $Γ $l $A $B)
  | `($Γ ⊢[$l:term] $A:term) => `($Γ ⊢[$l] $A:term ≡ $A)
  | `($Γ ⊢[$l:term] $t:term ≡ $u:term : $A:term) => `(EqTm $Γ $l $t $u $A)

end Notation

/-- A typing context consisting of expressions and their universe levels. -/
abbrev Ctx := List (Expr × Nat)

/-- `Lookup Γ i A l` means that `(A, l)` is stored at index `i` in `Γ`.
This implies `Γ ⊢[l] .bvar i : A`. -/
inductive Lookup : Ctx → Nat → Expr → Nat → Prop where
  | zero (Γ A l) : Lookup ((A,l) :: Γ) 0 A.lift l
  | succ {Γ A i l} : Lookup Γ i A l → Lookup ((A,l) :: Γ) (i+1) A.lift l

/-- The maximum `l` for which `Γ ⊢[l] 𝒥` makes sense.
When set to `0`, types cannot be quantified over at all. -/
def univMax := 37

/- `presupp` indicates presuppositions.
We don't add literally all of them,
just the ones needed that make inversion easy. -/

/- Convention on order of implicit parameters:
contexts, types, de Bruijn indices, universe levels. -/

mutual
inductive EqTp : Ctx → Nat → Expr → Expr → Prop
  -- Congruences / constructors
  | cong_pi {Γ A A' B B' l l'} :
    Γ ⊢[l] A ≡ A'→
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A' B'

  | cong_univ (Γ l) :
    l < univMax →
    Γ ⊢[l+1] .univ l

  | cong_el {Γ A A' l} :
    Γ ⊢[l+1] A ≡ A' : .univ l →
    Γ ⊢[l] .el A ≡ .el A'

  -- Substitution
  | inst_tp {Γ A B B' t u l l'} :
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[l] t ≡ u : A →
    Γ ⊢[l'] B.inst t ≡ B.inst u

  -- lift

  -- Symmetric-transitive closure
  | symm_tp {Γ A A' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] A' ≡ A

  | trans_tp {Γ A A' A'' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] A' ≡ A'' →
    Γ ⊢[l] A ≡ A''

inductive EqTm : Ctx → Nat → Expr → Expr → Expr → Prop
  -- Congruences / constructors
  | cong_bvar {Γ A i l} :
    Γ ⊢[l] A →
    Lookup Γ i A l →
    Γ ⊢[l] .bvar i : A

  | cong_lam {Γ A A' B t t' l l'} :
    Γ ⊢[l] A ≡ A' →
    (A,l) :: Γ ⊢[l'] t ≡ t' : B →
    Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A' t' : .pi l l' A B

  | cong_app {Γ A B B' f f' a a' l l'} :
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] f ≡ f' : .pi l l' A B →
    Γ ⊢[l] a ≡ a' : A →
    Γ ⊢[l'] .app l l' B f a ≡ .app l l' B' f' a' : B.inst a

  | cong_code {Γ A A' l} :
    l < univMax →
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l+1] .code A ≡ .code A' : .univ l

  -- Reductions
  | app_lam {Γ A B t u l l'} :
    (A,l) :: Γ ⊢[l'] t : B →
    Γ ⊢[l] u : A →
    Γ ⊢[l'] .app l l' B (.lam l l' A t) u ≡ t.inst u : B.inst u

  -- Expansions
  | eta {Γ A B f l l'} :
    Γ ⊢[max l l'] f : .pi l l' A B →
    Γ ⊢[max l l'] f ≡ .lam l l' A (.app l l' (B.liftN 1 1) f.lift (.bvar 0)) : .pi l l' A B

  -- Conversion
  | conv {Γ A A' t t' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t ≡ t' : A'

  -- Substitution
  | inst_tm {Γ A B a b t u l l'} :
    (A,l) :: Γ ⊢[l'] a ≡ b : B →
    Γ ⊢[l] t ≡ u : A →
    Γ ⊢[l'] a.inst t ≡ b.inst u : B.inst t

  -- lift

  -- Symmetric-transitive closure
  | symm_tm {Γ A t t' l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t : A

  | trans_tm {Γ A t t' t'' l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t'' : A →
    Γ ⊢[l] t ≡ t'' : A
end

/-! Pretty-printers. -/

section PrettyPrinting
open Lean PrettyPrinter

@[app_unexpander EqTp]
def EqTp.unexpand : Unexpander
  | `($_ $Γ $l $A $A') =>
    if A == A' then
      `($Γ ⊢[$l] $A:term)
    else
      `($Γ ⊢[$l] $A:term ≡ $A')
  | _ => throw ()

@[app_unexpander EqTm]
def EqTm.unexpand : Unexpander
  | `($_ $Γ $l $t $t' $A) =>
    if t == t' then
      `($Γ ⊢[$l] $t:term : $A)
    else
      `($Γ ⊢[$l] $t:term ≡ $t' : $A)
  | _ => throw ()

end PrettyPrinting
