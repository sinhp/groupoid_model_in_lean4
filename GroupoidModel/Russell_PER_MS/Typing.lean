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

/-- `Lookup Γ i A` implies that `Γ ⊢ .bvar i : A`. -/
inductive Lookup : List Expr → Nat → Expr → Prop where
  | zero {Γ A} : Lookup (A::Γ) 0 A.lift
  | succ {Γ i A} : Lookup Γ i A → Lookup (A::Γ) (i+1) A.lift

/-- The maximum `l` for which `Γ ⊢[l] 𝒥` makes sense.
When set to `0`, types cannot be quantified over at all. -/
def univMax := 37

/- `presupp` indicates presuppositions.
We don't add literally all of them,
just the ones needed that make inversion easy. -/

/- Convention on order of implicit parameters:
contexts, types, de Bruijn indices, universe levels. -/

mutual
inductive EqTp : List Expr → Nat → Expr → Expr → Prop
  -- Congruences / constructors
  | cong_pi {Γ A A' B B' l l'} :
    Γ ⊢[l] A ≡ A'→
    A :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .pi A B ≡ .pi A' B'

  | cong_univ (Γ l) :
    l < univMax →
    Γ ⊢[l+1] .univ l

  | cong_el {Γ A A' l} :
    Γ ⊢[l+1] A ≡ A' : .univ l →
    -- NOTE: the `el` is silent here.
    -- If needed, we can add it as a term former to the syntax,
    -- and continue interpreting it as before.
    Γ ⊢[l] A ≡ A'

  -- Substitution
  | inst {Γ A B B' t u l l'} :
    A :: Γ ⊢[l] B ≡ B' →
    Γ ⊢[l'] t ≡ u : A →
    Γ ⊢[l] B.inst t ≡ B.inst u

  -- lift

  -- Symmetric-transitive closure
  | symm {Γ A A' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] A' ≡ A

  | trans {Γ A A' A'' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] A' ≡ A'' →
    Γ ⊢[l] A ≡ A''

inductive EqTm : List Expr → Nat → Expr → Expr → Expr → Prop
  -- Congruences / constructors
  | cong_bvar {Γ A i l} :
    Γ ⊢[l] A →
    Lookup Γ i A →
    Γ ⊢[l] .bvar i : A

  | cong_lam {Γ A A' B t t' l l'} :
    Γ ⊢[l] A ≡ A' →
    A :: Γ ⊢[l'] t ≡ t' : B →
    Γ ⊢[max l l'] .lam A t ≡ .lam A' t' : .pi A B

  | cong_app {Γ A B B' f f' a a' l l'} :
    A :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] f ≡ f' : .pi A B →
    Γ ⊢[l] a ≡ a' : A →
    Γ ⊢[l'] .app B f a ≡ .app B' f' a' : B.inst a

  | cong_code {Γ A A' l} :
    l < univMax →
    Γ ⊢[l] A ≡ A' →
    -- NOTE: See note on `cong_el`.
    Γ ⊢[l+1] A ≡ A' : .univ l

  -- Substitution
  | inst {Γ A B t u a b l l'} :
    A :: Γ ⊢[l] t ≡ u : B →
    Γ ⊢[l'] a ≡ b : A →
    Γ ⊢[l] t.inst a ≡ u.inst b : B.inst a

  -- lift

  -- Reductions
  | app_lam {Γ A B t u l l'} :
    A :: Γ ⊢[l'] t : B →
    Γ ⊢[l] u : A →
    Γ ⊢[l'] .app B (.lam A t) u ≡ t.inst u : B.inst u

  -- Expansions
  | eta {Γ A B t l} :
    Γ ⊢[l] t : .pi A B →
    Γ ⊢[l] t ≡ .lam A (.app B t.lift (.bvar 0)) : .pi A B

  -- Conversion
  | conv {Γ A A' t t' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t ≡ t' : A'

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
