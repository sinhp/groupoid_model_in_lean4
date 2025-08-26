import Mathlib.Tactic.Convert
import GroupoidModel.Syntax.Basic

/-! Implementation of simultaneous substitutions
following Schäfer/Tebbi/Smolka in
*Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution*. -/

namespace Expr

/-- Append an element to a substitution or a renaming.
```
Δ ⊢ σ : Γ  Γ ⊢ A  Δ ⊢ t : A[σ]
------------------------------
Δ ⊢ σ.t : Γ.A
``` -/
def snoc.{u} {X : Sort u} (σ : Nat → X) (x : X) : Nat → X
  | 0   => x
  | n+1 => σ n

@[simp]
theorem snoc_zero {X} (σ : Nat → X) (x : X) : snoc σ x 0 = x := rfl

@[simp]
theorem snoc_succ {X} (σ : Nat → X) (x : X) (n) : snoc σ x (n + 1) = σ n := rfl

/-! ## Renaming -/

variable {χ : Type*}

/-- Lift a renaming under a binder. See `up`. -/
def upr (ξ : Nat → Nat) : Nat → Nat :=
  snoc (fun i => ξ i + 1) 0

-- TODO: add uprN

@[simp]
theorem upr_id : upr id = id := by
  ext ⟨⟩ <;> dsimp [upr, snoc]

/-- Rename the de Bruijn indices in an expression. -/
def rename (ξ : Nat → Nat) : Expr χ → Expr χ
  | .ax c => .ax c
  | .bvar i => .bvar (ξ i)
  | .pi l l' A B => .pi l l' (A.rename ξ) (B.rename (upr ξ))
  | .sigma l l' A B => .sigma l l' (A.rename ξ) (B.rename (upr ξ))
  | .lam l l' A t => .lam l l' (A.rename ξ) (t.rename (upr ξ))
  | .app l l' B fn arg => .app l l' (B.rename (upr ξ)) (fn.rename ξ) (arg.rename ξ)
  | .pair l l' B t u => .pair l l' (B.rename (upr ξ)) (t.rename ξ) (u.rename ξ)
  | .fst l l' A B p => .fst l l' (A.rename ξ) (B.rename (upr ξ)) (p.rename ξ)
  | .snd l l' A B p => .snd l l' (A.rename ξ) (B.rename (upr ξ)) (p.rename ξ)
  | .Id l A t u => .Id l (A.rename ξ) (t.rename ξ) (u.rename ξ)
  | .refl l t => .refl l (t.rename ξ)
  | .idRec l l' t C r u h =>
    .idRec l l' (t.rename ξ) (C.rename (upr <| upr ξ)) (r.rename ξ) (u.rename ξ) (h.rename ξ)
  | .univ l => .univ l
  | .el a => .el (a.rename ξ)
  | .code A => .code (A.rename ξ)

/-! ## Substitution -/

/-- Lift a substitution under a binder.
```
Δ ⊢ σ : Γ  Γ ⊢ A
------------------------
Δ.A[σ] ⊢ (↑≫σ).v₀ : Γ.A
```

Warning: don't unfold this definition! Use `up_eq_snoc` instead. -/
@[irreducible]
def up (σ : Nat → Expr χ) : Nat → Expr χ :=
  snoc (rename Nat.succ ∘ σ) (.bvar 0)

-- TODO: upN

@[simp]
theorem up_bvar (χ) : up (χ := χ) Expr.bvar = Expr.bvar := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, rename])

/-- Apply a substitution to an expression. -/
def subst (σ : Nat → Expr χ) : Expr χ → Expr χ
  | .ax c => .ax c
  | .bvar i => σ i
  | .pi l l' A B => .pi l l' (A.subst σ) (B.subst (up σ))
  | .sigma l l' A B => .sigma l l' (A.subst σ) (B.subst (up σ))
  | .lam l l' A t => .lam l l' (A.subst σ) (t.subst (up σ))
  | .app l l' B fn arg => .app l l' (B.subst (up σ)) (fn.subst σ) (arg.subst σ)
  | .pair l l' B t u => .pair l l' (B.subst (up σ)) (t.subst σ) (u.subst σ)
  | .fst l l' A B p => .fst l l' (A.subst σ) (B.subst (up σ)) (p.subst σ)
  | .snd l l' A B p => .snd l l' (A.subst σ) (B.subst (up σ)) (p.subst σ)
  | .Id l A t u => .Id l (A.subst σ) (t.subst σ) (u.subst σ)
  | .refl l t => .refl l (t.subst σ)
  | .idRec l l' t C r u h =>
    .idRec l l' (t.subst σ) (C.subst <| up <| up σ) (r.subst σ) (u.subst σ) (h.subst σ)
  | .univ l => .univ l
  | .el a => .el (a.subst σ)
  | .code A => .code (A.subst σ)

@[simp]
theorem subst_bvar (χ) : subst (χ := χ) Expr.bvar = id := by
  ext t; dsimp; induction t <;> grind [subst, up_bvar]

@[simp]
theorem subst_snoc_zero (σ : Nat → Expr χ) (t : Expr χ) : subst (snoc σ t) (.bvar 0) = t := by
  dsimp [subst, snoc]

/-- Turn a renaming into a substitution. -/
def ofRen (χ) (ξ : Nat → Nat) : Nat → Expr χ :=
  fun i => Expr.bvar (ξ i)

@[simp]
theorem ofRen_id (χ) : ofRen χ id = Expr.bvar := rfl

theorem ofRen_upr (χ ξ) : ofRen χ (upr ξ) = up (ofRen χ ξ) := by
  ext ⟨⟩ <;> simp [ofRen, upr, up, snoc, rename]

theorem rename_eq_subst_ofRen (χ) (ξ : Nat → Nat) : rename ξ = subst (ofRen χ ξ) := by
  ext t
  induction t generalizing ξ <;> dsimp [rename, subst]
  case bvar => simp [ofRen]
  all_goals grind [ofRen_upr]

/-- Compose two substitutions.
```
Θ ⊢ σ : Δ  Δ ⊢ τ : Γ
--------------------
Θ ⊢ σ≫τ : Γ
``` -/
def comp (σ τ : Nat → Expr χ) : Nat → Expr χ :=
  subst σ ∘ τ

@[simp]
theorem bvar_comp (σ : Nat → Expr χ) : comp Expr.bvar σ = σ := by
  ext i; simp [comp]

@[simp]
theorem comp_bvar (σ : Nat → Expr χ) : comp σ Expr.bvar = σ := by
  ext i; simp [comp, subst]

theorem up_comp_ren_sb (ξ : Nat → Nat) (σ : Nat → Expr χ) :
    up (σ ∘ ξ) = up σ ∘ upr ξ := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, upr])

theorem rename_subst (σ ξ) (t : Expr χ) : (t.rename ξ).subst σ = t.subst (σ ∘ ξ) := by
  induction t generalizing σ ξ
  all_goals grind [rename, subst, up_comp_ren_sb]

theorem up_comp_sb_ren (σ : Nat → Expr χ) (ξ : Nat → Nat) :
    up (rename ξ ∘ σ) = rename (upr ξ) ∘ up σ := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, rename, upr])
  conv => lhs; rw [rename_eq_subst_ofRen, rename_subst]
  conv => rhs; rw [rename_eq_subst_ofRen, rename_subst]
  rfl

theorem subst_rename (ξ σ) (t : Expr χ) :
    (t.subst σ).rename ξ = t.subst (rename ξ ∘ σ) := by
  induction t generalizing ξ σ
  all_goals grind [subst, rename, up_comp_sb_ren]

theorem up_comp (σ τ : Nat → Expr χ) :
    up (comp σ τ) = comp (up σ) (up τ) := by
  ext ⟨⟩ <;> simp [up, comp, snoc]
  simp [subst_rename, rename_subst]; congr

theorem subst_subst (σ τ : Nat → Expr χ) (t : Expr χ) :
    (t.subst τ).subst σ = t.subst (comp σ τ) := by
  induction t generalizing σ τ
  case bvar => dsimp [subst, comp]
  all_goals grind [subst, up_comp]

theorem comp_assoc (σ τ ρ : Nat → Expr χ) : comp σ (comp τ ρ) = comp (comp σ τ) ρ := by
  ext i
  conv => rhs; enter [0]; unfold comp
  dsimp; rw [← subst_subst]; dsimp [comp]

theorem comp_snoc (σ τ : Nat → Expr χ) (t : Expr χ) :
    comp σ (snoc τ t) = snoc (comp σ τ) (t.subst σ) := by
  ext ⟨⟩ <;> dsimp [comp, snoc]

/-- The weakening substitution.
```
Γ ⊢ A
------------
Γ.A ⊢ ↑ : Γ
``` -/
def wk : Nat → Expr χ :=
  ofRen χ Nat.succ

@[simp]
theorem ofRen_succ (χ) : ofRen χ Nat.succ = wk := rfl

theorem up_eq_snoc (σ : Nat → Expr χ) : up σ = snoc (comp wk σ) (.bvar 0) := by
  ext i; unfold up comp; congr 1; ext j
  rw [rename_eq_subst_ofRen]; congr 1

@[simp]
theorem snoc_comp_wk (σ : Nat → Expr χ) (t) : comp (snoc σ t) wk = σ := by
  ext ⟨⟩ <;> dsimp [comp, snoc, wk, ofRen, subst, -ofRen_succ]

@[simp]
theorem snoc_wk_zero (χ) : snoc wk (Expr.bvar (χ := χ) 0) = Expr.bvar := by
  ext ⟨⟩ <;> dsimp [snoc, wk, ofRen, -ofRen_succ]

theorem snoc_comp_wk_succ (σ : Nat → Expr χ) (n) :
    snoc (comp wk σ) (bvar (n + 1)) = comp wk (snoc σ (bvar n)) := by
  ext ⟨⟩ <;> dsimp [comp, snoc, wk, -ofRen_succ, subst, ofRen]

/-- A substitution that instantiates one binder.
```
Γ ⊢ t : A
--------------
Γ ⊢ id.t : Γ.A
``` -/
def toSb (t : Expr χ) : Nat → Expr χ :=
  snoc Expr.bvar t

/-! ## Decision procedure -/

theorem snoc_comp_wk_zero_subst (σ : Nat → Expr χ) :
    snoc (comp σ Expr.wk) ((Expr.bvar 0).subst σ) = σ := by
  ext ⟨⟩ <;> dsimp [snoc, comp, subst, wk, ofRen, -ofRen_succ]

theorem ofRen_comp (χ) (ξ₁ ξ₂ : Nat → Nat) :
    ofRen χ (ξ₁ ∘ ξ₂) = comp (ofRen χ ξ₁) (ofRen χ ξ₂) :=
  rfl

@[simp]
theorem wk_app (χ) (n) : wk (χ := χ) n = .bvar (n + 1) := by
  rw [wk, ofRen]


-- Rules from Fig. 1 in the paper.
attribute [autosubst low]
  subst
attribute [autosubst]
  subst_snoc_zero
  snoc_comp_wk
  subst_bvar
  snoc_comp_wk_zero_subst
  comp_bvar
  bvar_comp
  comp_assoc
  comp_snoc
  subst_subst
  snoc_wk_zero

-- Rules that are not in the paper,
-- but allow us to prove more stuff.
attribute [autosubst]
  snoc_zero
  snoc_succ
  snoc_comp_wk_succ
  wk_app

-- Rules to unfold abbreviations.
attribute [autosubst high]
  up_eq_snoc
  toSb

-- More rules to deal with renamings. These are ad-hoc, not from paper.
attribute [autosubst low]
  rename
attribute [autosubst]
  rename_eq_subst_ofRen
  ofRen_id
  ofRen_comp
  ofRen_succ
  ofRen_upr

-- Cleanup rules.
attribute [autosubst]
  id_eq

/-- Decides equality of substitutions applied to expressions. -/
macro "autosubst" : tactic => `(tactic| simp only [autosubst])

/-- Use a term modulo `autosubst` conversion. -/
macro "autosubst% " t:term : term => `(by convert ($t) using 1 <;> autosubst)

/-! Lemmas that come up in a few proofs -/

theorem subst_toSb_subst (B a : Expr χ) σ :
    (B.subst a.toSb).subst σ = (B.subst (Expr.up σ)).subst (a.subst σ).toSb := by
  autosubst

theorem subst_snoc_toSb_subst (B a b : Expr χ) σ :
    (B.subst <| Expr.snoc a.toSb b).subst σ =
      (B.subst <| Expr.up <| Expr.up σ).subst (Expr.snoc (a.subst σ).toSb (b.subst σ)) := by
  autosubst

/-! ## Closed expressions -/

/-- The expression uses only indices up to `k`. -/
def isClosed (k : Nat := 0) : Expr χ → Bool
  | .ax _ | .univ _ => true
  | .bvar i => i < k
  | .refl _ t | .el t | .code t => t.isClosed k
  | .pi _ _ t b | .sigma _ _ t b | .lam _ _ t b =>
    t.isClosed k && b.isClosed (k + 1)
  | .app _ _ b t u | .pair _ _ b t u | .fst _ _ t b u | .snd _ _ t b u =>
    b.isClosed (k + 1) && t.isClosed k && u.isClosed k
  | .Id _ A t u => A.isClosed k && t.isClosed k && u.isClosed k
  | .idRec _ _ t M r u h =>
    t.isClosed k && M.isClosed (k + 2) && r.isClosed k && u.isClosed k && h.isClosed k

/-- The substitution acts via identity on indices strictly below `k`. -/
def SbIsBvar (σ : Nat → Expr χ) (k : Nat) :=
  ∀ ⦃i⦄, i < k → σ i = .bvar i

theorem SbIsBvar.up {σ : Nat → Expr χ} {k} : SbIsBvar σ k → SbIsBvar (Expr.up σ) (k + 1) := by
  rintro σk ⟨⟩ lt
  . simp [Expr.up_eq_snoc]
  . have := σk (Nat.succ_lt_succ_iff.mp lt)
    simp [Expr.up_eq_snoc, Expr.comp, this, Expr.subst]

theorem SbIsBvar.zero (σ : Nat → Expr χ) : SbIsBvar σ 0 := nofun

theorem subst_of_isClosed' {e : Expr χ} {k} {σ : Nat → Expr χ} :
    e.isClosed k → SbIsBvar σ k → e.subst σ = e := by
  intro h hσ
  induction e generalizing k σ
  case bvar =>
    simp only [isClosed, decide_eq_true_eq] at h
    simp [subst, hσ h]
  all_goals grind [subst, isClosed, → SbIsBvar.up]

theorem subst_of_isClosed {e : Expr χ} (σ : Nat → Expr χ) : e.isClosed → e.subst σ = e :=
  fun h => e.subst_of_isClosed' h (.zero _)

end Expr
