-- Authors: C.B. Aberlé, Wojciech Nawrocki

/- Bidirectional presentation suggested by Corinthia. -/

import GroupoidModel.NaturalModel
import GroupoidModel.TypeTheory.Tarski_SemanticBiDir.Interpretation

mutual
inductive TyExpr where
  | univ
  | el (A : Expr)
  | pi (A B : TyExpr)
  | wk (A : TyExpr) -- HACK: explicit substitutions, but just for weakening
  deriving Repr

inductive Expr where
  /-- A de Bruijn index. -/
  | bvar (n : Nat)
  | app (f a : Expr)
  -- NOTE: no domain type annotation because we only _check_ lambdas.
  -- To synthesize, use `.coe (.lam t) (.pi A B)`.
  -- AFAICT, this unfortunately makes it impossible
  -- to check the domain but synthesize the codomain.
  -- Fortunately we don't care about usability:
  -- expressions are elaborated (with higher-order unification) by Lean,
  -- and typechecking just has to ensure well-typedness in HoTT₀.
  | lam (val : Expr)
  | spi (a b : Expr)
  | coe (t : Expr) (A : TyExpr)
  deriving Repr
end

namespace Notation
declare_syntax_cat judgment
scoped syntax term " ⊢ " judgment : term

scoped syntax term:51 " ↝ " term:26 : judgment
scoped syntax term:51 " ∋ " term " ↝ " term:26 : judgment
scoped syntax term:51 " ∈ " term " ↝ " term:26 : judgment

set_option hygiene false in
macro_rules
  | `($Γ ⊢ $T:term ↝ $sT:term) => `(InterpType $Γ $T $sT)
  | `($Γ ⊢ $t:term ∈ $sT:term ↝ $st:term) => `(SynthType $Γ $t $sT $st)
  | `($Γ ⊢ $sT:term ∋ $t:term ↝ $st:term) => `(ChkType $Γ $sT $t $st)
end Notation
open Notation

open CategoryTheory NaturalModel Limits

universe u
variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx] [M : NaturalModel Ctx]

/-! Typechecking + interpretation relations.
EQ? marks where the typechecker would have to prove an equality to instantiate a premise.
DATA? marks where the typechecker would have to invent some data to instantiate a premise

Also note that we solve premises in the order they appear.

Btw, initially we wrote down
```lean
inductive SynthType : (Γ : CCtx Ctx) → Expr → (y(Γ) ⟶ M.Ty) → (y(Γ) ⟶ M.Tm) → Type u
inductive ChkType : (Γ : Ctx) → (y(Γ) ⟶ M.Ty) → Expr → (y(Γ) ⟶ M.Tm) → Type u
```
I think this can also work, but it's convenient to use `CCtx.typed`
whose APIs already deal with the various semantic typing obligations. -/
mutual
/-- Type interpretation `Γ ⊢ A ↝ sA`
Inputs: `Γ, A`
Outputs: `sA` -/
inductive InterpType : (Γ : CCtx Ctx) → TyExpr → Γ.ty → Type u
  -- Built-in weakening but not any other substitutions ¯\_(ツ)_/¯
  | wk {Γ A sA sB} :
    Γ ⊢ A ↝ sA →
    /- Subtlety:
    the typechecker _can_ decompose the input context into `Γ.cons sB`
    because the input is a semantic context _stack_ `CCtx Ctx`.
    It wouldn't work with just a `Ctx`. -/
    Γ.cons sB ⊢ .wk A ↝ Γ.wk sB sA
  | univ {Γ} : Γ ⊢ .univ ↝ wU
  | pi {Γ} {A B} {sA sB} :
    Γ ⊢ A ↝ sA →
    Γ.cons sA ⊢ B ↝ sB →
    Γ ⊢ .pi A B ↝ (Γ.mkPi sA sB)
  | el {Γ} {a} {sa} :
    Γ ⊢ wU ∋ a ↝ sa →
    Γ ⊢ .el a ↝ Γ.mkEl sa

/-- Type synthesis `Γ ⊢ t ∈ sA ↝ st`.
Elimination rules are synthesized.

Inputs: `Γ, t`
Outputs: `sA, st` -/
inductive SynthType : (Γ : CCtx Ctx) → Expr → (sA : Γ.ty) → Γ.typed sA → Type u
  | var {Γ : CCtx Ctx} {sA} :
    Γ.cons sA ⊢ .bvar 0 ∈ (Γ.wk sA sA) ↝ (Γ.var₀ sA)
  | app {Γ} {f a} {sF sA} {sB : (Γ.cons sA).ty} {sf sa} :
    Γ ⊢ f ∈ sF ↝ sf →
    /- DATA?(sA, sB) ; EQ?
    In a complete algorithm,
    we might want to check `sF = Γ.mkPi ?A ?B` here,
    with `?A` and `?B` being metavariables that need unification.
    .. but we cannot decide semantic equality,
    so it seems that synthesis needs to also give us a _syntactic_ type `F`
    for which we'd check `Γ ⊢ F ≡ .pi ?A ?B`. -/
    (eq_pi : sF = Γ.mkPi sA sB) →
    Γ ⊢ sA ∋ a ↝ sa →
    Γ ⊢ .app f a ∈ (Γ.inst sA sB sa) ↝ (Γ.mkApp sA sB (eq_pi ▸ sf) sa)
  | coe {Γ} {A} {t} {sA} {st} :
    Γ ⊢ A ↝ sA →
    Γ ⊢ sA ∋ t ↝ st →
    Γ ⊢ .coe t A ∈ sA ↝ st

/-- Type checking `Γ ⊢ sA ∋ t ↝ st`
Introduction rules are checked.

Inputs: `Γ, sA, t`
Outputs: `st` -/
inductive ChkType : (Γ : CCtx Ctx) → (sA : Γ.ty) → Expr → Γ.typed sA → Type u
  | lam {Γ} {t} {sA sB} {st} :
    Γ.cons sA ⊢ sB ∋ t ↝ st →
    Γ ⊢ (Γ.mkPi sA sB) ∋ .lam t ↝ (Γ.mkLam sA sB st)
  | synth {Γ} {t} {sA sA'} {st} :
    Γ ⊢ t ∈ sA' ↝ st →
    (eq : sA' = sA) → -- EQ?
    Γ ⊢ sA ∋ t ↝ st.cast eq
end

@[app_unexpander InterpType] def interpTypeUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $T $sT) => `($Γ ⊢ $T:term ↝ $sT)
  | _ => throw ()

@[app_unexpander SynthType] def synthTypeUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $t $sT $st) => `($Γ ⊢ $t:term ∈ $sT ↝ $st)
  | _ => throw ()

@[app_unexpander ChkType] def chkTypeUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $sT $t $st) => `($Γ ⊢ $sT:term ∋ $t ↝ $st)
  | _ => throw ()

noncomputable section

set_option quotPrecheck false in
notation "⋄" => CCtx.nil (M := M)

/-! Example typing derivations written out in painful detail
to simulate a typechecking metaprogram. -/

/- Thought:
for completeness of typechecking,
all the equality subgoals ought to apply a sound conversion procedure
rather than `rfl`/`simp`/something that happens to work,
but for that we'd need to synthesize syntactic types.
Equality of semantic types isn't decidable. -/
example
    (sN : ⋄.ty)
    (z : Expr) (sz : ⋄.typed sN)
    (z_synth : ⋄ ⊢ z ∈ sN ↝ sz)
    (f : Expr) (sf : ⋄.typed (⋄.mkPi sN (⋄.wk sN sN)))
    (f_synth : ⋄ ⊢ f ∈ (⋄.mkPi sN (⋄.wk sN sN)) ↝ sf) :
    Σ sa, ⋄ ⊢ sN ∋ .app f z ↝ sa :=
  ⟨_,
    .synth
      (.app
        f_synth
        (eq_pi := rfl)
        (.synth
          z_synth
          (eq := rfl)))
      (eq := by simp)⟩

-- A dumb lemma we are forced to use because of the indexed inductive.
theorem tri_tri {Γ : CCtx Ctx} (A B : Γ.ty) (eq : A = B) (eq' : B = A)
    (a : Γ.typed A) :
    (eq ▸ eq' ▸ a) = a :=
  by cases eq; cases eq'; rfl

example
    (N : TyExpr) (sN : ⋄.ty)
    (N_interp : ⋄ ⊢ N ↝ sN)
    (cN : Expr) (scN : ⋄.typed wU)
    /- With the present rules,
    `(cN_interp : ⋄ ⊢ .el cN ↝ sN)` seems not strong enough
    because we don't have a syntactic defeq judgment,
    so cannot conclude
    ```
    Γ ⊢ .el cT ↝ sT  Γ ⊢ T ≡ .el cT  Γ ⊢ T ↝ sT
    ---------------------------------------------
    Γ ⊢ T ↝ sa
    ``` -/
    (cN_synth : ⋄ ⊢ cN ∈ wU ↝ scN)
    (mkEl_scN : ⋄.mkEl scN = sN)
    (z : Expr) (sz : ⋄.typed sN)
    (z_synth : ⋄ ⊢ z ∈ sN ↝ sz)
    (f : Expr) (sf : ⋄.typed (⋄.mkPi sN (⋄.wk sN sN)))
    (f_synth : ⋄ ⊢ f ∈ (⋄.mkPi sN (⋄.wk sN sN)) ↝ sf) :
    let f' := .coe f $ .pi (.el $ .app (.coe (.lam $ .bvar 0) (.pi .univ $ .wk .univ)) cN) (.wk N)
    Σ sa, ⋄ ⊢ sN ∋ .app f' z ↝ sa :=
  ⟨_,
    .synth
      (.app
        (.coe
          (.pi
            (.el
              (.synth
                (.app
                  (.coe
                    (.pi
                      .univ
                      (.wk
                        .univ))
                    (.lam
                      (.synth
                        .var
                        (eq := rfl))))
                  (eq_pi := rfl)
                  (.synth
                    cN_synth
                    (eq := rfl)))
                (eq := by simp)))
            (.wk
              N_interp))
          -- Subtlety: the expected type here is already substantial,
          -- yet the example is trivial.
          -- I worry that checking these indices of the relation
          -- would generate 𝒪(a lot) work for the Lean kernel.
          -- Update: in fact, I think that having to generate these terms at all
          -- is a serious performance issue for any kind of certifying typechecker-interpreter.
          -- Given a certified interpreter,
          -- a typechecker-non-interpreter can simply produce `ofTerm (.app f' z) (⋯ : ⋄ ⊢ _ : N)`.
          (.synth
            f_synth
            (eq := by
              rw [CCtx.mkApp_mkLam]
              dsimp
              rw [CCtx.inst'_var₀]
              dsimp
              rw [mkEl_scN])))
        -- Have to invent `sA`/`sB` here.
        -- Assuming normalization of the Pi'd types so that `sA`/`sB` come out nice.
        (sA := sN)
        (sB := ⋄.wk sN sN)
        (eq_pi := by
          -- TODO: We just proved this above. Duplication why?
          rw [CCtx.mkApp_mkLam]
          dsimp
          rw [CCtx.inst'_var₀]
          dsimp
          rw [mkEl_scN])
        (.synth
          z_synth
          (eq := rfl)))
      (eq := by simp)⟩
