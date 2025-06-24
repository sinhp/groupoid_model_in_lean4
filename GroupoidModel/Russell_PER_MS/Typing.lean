import GroupoidModel.Russell_PER_MS.Autosubst

/-! ## Typing rules

In this file we specify typing judgments of the type theory
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
  | `($Γ ⊢[$l:term] $t:term : $A:term) => `(WfTm $Γ $l $t $A)
  | `($Γ ⊢[$l:term] $A:term ≡ $B:term) => `(EqTp $Γ $l $A $B)
  | `($Γ ⊢[$l:term] $A:term) => `(WfTp $Γ $l $A)
  | `($Γ ⊢[$l:term] $t:term ≡ $u:term : $A:term) => `(EqTm $Γ $l $t $u $A)

end Notation

/-- A typing context consisting of type expressions and their universe levels. -/
abbrev Ctx := List (Expr × Nat)

/-- The maximum `l` for which `Γ ⊢[l] 𝒥` makes sense.
When set to `0`, types cannot be quantified over at all. -/
-- TODO: this should be a parameter,
-- but adding an `optParam` to all judgments is super noisy.
-- If only we had parameterized modules..
def univMax : Nat := 3

/-- `Lookup Γ i A l` means that `A = A'[↑ⁱ⁺¹]`
where `(A', l)` is stored at index `i` in `Γ`.
Together with `⊢ Γ`, this implies `Γ ⊢[l] .bvar i : A`. -/
inductive Lookup : Ctx → Nat → Expr → Nat → Prop where
  | zero (Γ A l) : Lookup ((A,l) :: Γ) 0 (A.subst Expr.wk) l
  | succ {Γ A i l} (B l') : Lookup Γ i A l → Lookup ((B,l') :: Γ) (i+1) (A.subst Expr.wk) l

mutual

/-- All types in the given context are well-formed. -/
inductive WfCtx : Ctx → Prop
  | nil : WfCtx []
  | snoc {Γ A l} :
    WfCtx Γ →
    Γ ⊢[l] A →
    WfCtx ((A,l) :: Γ)

/-- The type is well-formed at the specified universe level.

Many of the inference rules have redundant premises ("presuppositions");
these rules are postfixed with a prime (').
This makes it easier to push syntactic metatheory through.
After proving inversion lemmas,
we define more efficient rules with fewer premises,
named the same but without the prime.
This is not just for usability:
it also means the Lean kernel is checking smaller derivation trees.

Convention on order of implicit parameters:
contexts, types, terms, de Bruijn indices, universe levels. -/
inductive WfTp : Ctx → Nat → Expr → Prop
  -- Type formers
  | pi' {Γ A B l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] .pi l l' A B

  | sigma' {Γ A B l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] .sigma l l' A B

  | univ {Γ l} :
    WfCtx Γ →
    l < univMax →
    Γ ⊢[l+1] .univ l

  | el {Γ A l} :
    Γ ⊢[l+1] A : .univ l →
    Γ ⊢[l] .el A

/-- The two types are equal at the specified universe level. -/
inductive EqTp : Ctx → Nat → Expr → Expr → Prop
  -- Congruences
  | cong_pi' {Γ A A' B B' l l'} :
    Γ ⊢[l] A →
    Γ ⊢[l] A' →
    Γ ⊢[l] A ≡ A' →
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A' B'

  | cong_sigma' {Γ A A' B B' l l'} :
    Γ ⊢[l] A →
    Γ ⊢[l] A' →
    Γ ⊢[l] A ≡ A'→
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] .sigma l l' A B ≡ .sigma l l' A' B'

  | cong_el {Γ A A' l} :
    Γ ⊢[l+1] A ≡ A' : .univ l →
    Γ ⊢[l] .el A ≡ .el A'

  -- Reflexive-symmetric-transitive closure
  | refl_tp {Γ A l} :
    Γ ⊢[l] A →
    Γ ⊢[l] A ≡ A

  | symm_tp {Γ A A' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] A' ≡ A

  | trans_tp {Γ A A' A'' l} :
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] A' ≡ A'' →
    Γ ⊢[l] A ≡ A''

/-- The term has the specified type at the specified universe level. -/
inductive WfTm : Ctx → Nat → Expr → Expr → Prop
  -- Term formers
  | bvar {Γ A i l} :
    WfCtx Γ →
    Lookup Γ i A l →
    Γ ⊢[l] .bvar i : A

  | lam' {Γ A B t l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] t : B →
    Γ ⊢[max l l'] .lam l l' A t : .pi l l' A B

  | app' {Γ A B f a l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] f : .pi l l' A B →
    Γ ⊢[l] a : A →
    Γ ⊢[l'] .app l l' A B f a : B.subst a.toSb

  | pair' {Γ A B t u l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[max l l'] .pair l l' B t u : .sigma l l' A B

  | fst' {Γ A B p l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l] .fst l l' A B p : A

  | snd' {Γ A B p l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[l'] .snd l l' A B p : B.subst (Expr.fst l l' A B p).toSb

  | code {Γ A l} :
    l < univMax →
    Γ ⊢[l] A →
    Γ ⊢[l+1] .code A : .univ l

  -- Conversion
  | conv {Γ A A' t l} :
    Γ ⊢[l] t : A →
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] t : A'

/-- The two terms are equal at the specified type and universe level. -/
inductive EqTm : Ctx → Nat → Expr → Expr → Expr → Prop
  -- Congruences
  | cong_lam' {Γ A A' B t t' l l'} :
    Γ ⊢[l] A →
    Γ ⊢[l] A' →
    Γ ⊢[l] A ≡ A' →
    (A,l) :: Γ ⊢[l'] t ≡ t' : B →
    Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A' t' : .pi l l' A B

  | cong_app' {Γ A A' B B' f f' a a' l l'} :
    Γ ⊢[l] A →
    Γ ⊢[l] A ≡ A' →
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] f ≡ f' : .pi l l' A B →
    Γ ⊢[l] a ≡ a' : A →
    Γ ⊢[l'] .app l l' A B f a ≡ .app l l' A' B' f' a' : B.subst a.toSb

  | cong_pair' {Γ A B B' t t' u u' l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l'] u ≡ u' : B.subst t.toSb →
    Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B' t' u' : .sigma l l' A B

  | cong_fst' {Γ A A' B B' p p' l l'} :
    Γ ⊢[l] A →
    Γ ⊢[l] A ≡ A' →
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A' B' p' : A

  | cong_snd' {Γ A A' B B' p p' l l'} :
    Γ ⊢[l] A →
    Γ ⊢[l] A ≡ A' →
    (A,l) :: Γ ⊢[l'] B ≡ B' →
    Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A' B' p' : B.subst (Expr.fst l l' A B p).toSb

  | cong_code {Γ A A' l} :
    l < univMax →
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l+1] .code A ≡ .code A' : .univ l

  -- Reductions
  | app_lam' {Γ A B t u l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    (A,l) :: Γ ⊢[l'] t : B →
    Γ ⊢[l] u : A →
    Γ ⊢[l'] .app l l' A B (.lam l l' A t) u ≡ t.subst u.toSb : B.subst u.toSb

  | fst_pair' {Γ} {A B t u : Expr} {l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[l] .fst l l' A B (.pair l l' B t u) ≡ t : A

  | snd_pair' {Γ} {A B t u : Expr} {l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[l] t : A →
    Γ ⊢[l'] u : B.subst t.toSb →
    Γ ⊢[l'] .snd l l' A B (.pair l l' B t u) ≡ u : B.subst t.toSb

  -- Expansions
  | lam_app' {Γ A B f l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] f : .pi l l' A B →
    Γ ⊢[max l l'] f ≡ .lam l l' A (.app l l' (A.subst Expr.wk) (B.subst (Expr.up Expr.wk)) (f.subst Expr.wk) (.bvar 0)) : .pi l l' A B

  | pair_fst_snd' {Γ A B p l l'} :
    Γ ⊢[l] A →
    (A,l) :: Γ ⊢[l'] B →
    Γ ⊢[max l l'] p : .sigma l l' A B →
    Γ ⊢[max l l'] p ≡ .pair l l' B (.fst l l' A B p) (.snd l l' A B p) : .sigma l l' A B

  -- Conversion
  | conv_eq {Γ A A' t t' l} :
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] A ≡ A' →
    Γ ⊢[l] t ≡ t' : A'

  -- Reflexive-symmetric-transitive closure
  | refl_tm {Γ A t l} :
    Γ ⊢[l] t : A →
    Γ ⊢[l] t ≡ t : A

  | symm_tm' {Γ A t t' l} :
    Γ ⊢[l] A →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t : A

  | trans_tm' {Γ A t t' t'' l} :
    Γ ⊢[l] A →
    Γ ⊢[l] t ≡ t' : A →
    Γ ⊢[l] t' ≡ t'' : A →
    Γ ⊢[l] t ≡ t'' : A
end

/-! ## Pretty-printers -/

section PrettyPrinting
open Lean PrettyPrinter

@[app_unexpander WfTp]
def WfTp.unexpand : Unexpander
  | `($_ $Γ $l $A) => `($Γ ⊢[$l] $A:term)
  | _ => throw ()

@[app_unexpander EqTp]
def EqTp.unexpand : Unexpander
  | `($_ $Γ $l $A $A') => `($Γ ⊢[$l] $A:term ≡ $A')
  | _ => throw ()

@[app_unexpander WfTm]
def WfTm.unexpand : Unexpander
  | `($_ $Γ $l $t $A) => `($Γ ⊢[$l] $t:term : $A)
  | _ => throw ()

@[app_unexpander EqTm]
def EqTm.unexpand : Unexpander
  | `($_ $Γ $l $t $t' $A) => `($Γ ⊢[$l] $t:term ≡ $t' : $A)
  | _ => throw ()

end PrettyPrinting
