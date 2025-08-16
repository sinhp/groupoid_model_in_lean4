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

/-- Lift a renaming under a binder. See `up`. -/
def upr (ξ : Nat → Nat) : Nat → Nat :=
  snoc (fun i => ξ i + 1) 0

-- TODO: add uprN

@[simp]
theorem upr_id : upr id = id := by
  ext ⟨⟩ <;> dsimp [upr, snoc]

variable {S} (bvar : S → Nat → Expr) (up : S → S) in
/-- Apply a substitution to an expression. -/
def subst' (σ : S) : Expr → Expr
  | .bvar i => bvar σ i
  | .pi l l' A B => .pi l l' (A.subst' σ) (B.subst' (up σ))
  | .sigma l l' A B => .sigma l l' (A.subst' σ) (B.subst' (up σ))
  | .lam l l' A t => .lam l l' (A.subst' σ) (t.subst' (up σ))
  | .app l l' B fn arg => .app l l' (B.subst' (up σ)) (fn.subst' σ) (arg.subst' σ)
  | .pair l l' B t u => .pair l l' (B.subst' (up σ)) (t.subst' σ) (u.subst' σ)
  | .fst l l' A B p => .fst l l' (A.subst' σ) (B.subst' (up σ)) (p.subst' σ)
  | .snd l l' A B p => .snd l l' (A.subst' σ) (B.subst' (up σ)) (p.subst' σ)
  | .Id l A t u => .Id l (A.subst' σ) (t.subst' σ) (u.subst' σ)
  | .refl l t => .refl l (t.subst' σ)
  | .idRec l l' t C r u h =>
    .idRec l l' (t.subst' σ) (C.subst' (up <| up σ)) (r.subst' σ) (u.subst' σ) (h.subst' σ)
  | .univ l => .univ l
  | .el a => .el (a.subst' σ)
  | .code A => .code (A.subst' σ)

/-- Rename the de Bruijn indices in an expression. -/
def rename (ξ : Nat → Nat) : Expr → Expr := subst' (.bvar ∘ ·) upr ξ

/-! ## Substitution -/

/-- Lift a substitution under a binder.
```
Δ ⊢ σ : Γ  Γ ⊢ A
------------------------
Δ.A[σ] ⊢ (↑≫σ).v₀ : Γ.A
```

Warning: don't unfold this definition! Use `up_eq_snoc` instead. -/
@[irreducible]
def up (σ : Nat → Expr) : Nat → Expr :=
  snoc (fun i => (σ i).rename Nat.succ) (.bvar 0)

-- TODO: upN

@[simp]
theorem up_bvar : up Expr.bvar = Expr.bvar := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, rename, subst'])

/-- Apply a substitution to an expression. -/
def subst (σ : Nat → Expr) : Expr → Expr := subst' id up σ

theorem subst'_bvar {S bvar up} {σ : S} (hup : up σ = σ) (hb : bvar σ = .bvar) :
    subst' bvar up σ = id := by
  have := funext_iff.1 hb
  ext t; dsimp; induction t <;> grind [subst']

@[simp]
theorem subst_bvar : subst Expr.bvar = id := subst'_bvar up_bvar rfl

@[simp]
theorem subst_snoc_zero (σ : Nat → Expr) (t : Expr) : subst (snoc σ t) (.bvar 0) = t := by
  dsimp [subst, subst', snoc]

/-- Turn a renaming into a substitution. -/
def ofRen (ξ : Nat → Nat) : Nat → Expr :=
  fun i => Expr.bvar (ξ i)

@[simp]
theorem ofRen_id : ofRen id = Expr.bvar := rfl

theorem ofRen_upr (ξ) : ofRen (upr ξ) = up (ofRen ξ) := by
  ext ⟨⟩ <;> simp [ofRen, upr, up, snoc, rename, subst']

theorem subst'_map {S T bvar up up'} {σ : S} (f : S → T) (hup : ∀ ξ, up (f ξ) = f (up' ξ)) :
    subst' bvar up (f σ) = subst' (bvar ∘ f) up' σ := by
  ext t
  induction t generalizing σ <;> dsimp [subst'] <;> grind [ofRen_upr]

theorem rename_eq_subst_ofRen (ξ : Nat → Nat) : rename ξ = subst (ofRen ξ) :=
  .symm <| subst'_map _ fun _ => (ofRen_upr _).symm

/-- Compose two substitutions.
```
Θ ⊢ σ : Δ  Δ ⊢ τ : Γ
--------------------
Θ ⊢ σ≫τ : Γ
``` -/
def comp (σ τ : Nat → Expr) : Nat → Expr :=
  fun i => (τ i).subst σ

@[simp]
theorem bvar_comp (σ) : comp Expr.bvar σ = σ := by
  ext i; simp [comp]

@[simp]
theorem comp_bvar (σ) : comp σ Expr.bvar = σ := by
  ext i; simp [comp, subst, subst']

theorem up_comp_ren_sb (ξ : Nat → Nat) (σ : Nat → Expr) :
    up (σ ∘ ξ) = up σ ∘ upr ξ := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, upr])

theorem subst'_subst' {S₁ S₂ S₃ bvar₁ up₁ bvar₂ up₂ bvar₃ up₃}
    (hup : ∀ ξ σ τ, (∀ i, bvar₃ τ i = (bvar₁ σ i).subst' bvar₂ up₂ ξ) →
      ∀ i, bvar₃ (up₃ τ) i = (bvar₁ (up₁ σ) i).subst' bvar₂ up₂ (up₂ ξ))
    (ξ : S₂) (σ : S₁) (τ : S₃) (t : Expr)
    (H1 : ∀ i, bvar₃ τ i = (bvar₁ σ i).subst' bvar₂ up₂ ξ) :
    (t.subst' bvar₁ up₁ σ).subst' bvar₂ up₂ ξ = t.subst' bvar₃ up₃ τ := by
  induction t generalizing ξ σ τ <;> dsimp [subst'] <;> grind

theorem subst_subst' {S' bvar' up'}
    (hup : ∀ ξ σ, up (fun i => (σ i).subst' bvar' up' ξ) =
      fun i => (up σ i).subst' bvar' up' (up' ξ))
    (ξ : S') (σ) (t : Expr) :
    (t.subst σ).subst' bvar' up' ξ = t.subst fun i => (σ i).subst' bvar' up' ξ := by
  refine subst'_subst' (fun _ _ _ H => ?_) _ _ _ _ (funext_iff.1 rfl)
  cases funext_iff.2 H
  exact funext_iff.1 (hup ..)

theorem rename_subst' {S v' up'}
    (hup : ∀ ξ σ, up' (fun i => σ (ξ i)) = fun i => up' σ (upr ξ i))
    (σ : Nat → S) (ξ) (t : Expr) :
    (t.rename ξ).subst' (v' ∘ ·) up' σ = t.subst' (v' ∘ ·) up' (fun i => σ (ξ i)) := by
  dsimp [rename, subst]
  induction t generalizing σ ξ <;> dsimp [subst']
  all_goals
    specialize hup ξ σ
    simp [*]

theorem rename_subst (σ ξ) (t : Expr) : (t.rename ξ).subst σ = t.subst (σ ∘ ξ) := by
  apply rename_subst' (v' := id); apply up_comp_ren_sb

theorem up_comp_sb_ren (σ : Nat → Expr) (ξ : Nat → Nat) :
    up (rename ξ ∘ σ) = rename (upr ξ) ∘ up σ := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, rename, subst', upr])
  simp [← rename.eq_1]
  conv => lhs; rw [rename_eq_subst_ofRen, rename_subst]
  conv => rhs; rw [rename_eq_subst_ofRen, rename_subst]
  rfl

section
variable
  {S} {up' : S → S} {v' : S → Nat → Expr}
  (up0 : ∀ {ξ}, v' (up' ξ) 0 = bvar 0)
  (upS : ∀ {ξ n}, v' (up' ξ) (n + 1) = rename Nat.succ (v' ξ n))
include up0 upS

theorem up_comp_sb'_ren
    (σ) (ξ : S) :
    up (fun i ↦ v' ξ (σ i)) = fun i => v' (up' ξ) (upr σ i) := by
  ext ⟨⟩ <;> simp [up, snoc, rename, upr, *]

theorem subst'_rename (ξ : S) (σ) (t : Expr) :
    (t.rename σ).subst' v' up' ξ = t.subst fun i => v' ξ (σ i) := by
  dsimp [rename, subst]
  have := up_comp_sb'_ren up0 upS
  induction t generalizing ξ σ <;> dsimp [subst'] <;> simp [*]

theorem up_comp_sb' (ξ : S) (σ : Nat → Expr) :
    up (fun i => (σ i).subst' v' up' ξ) = fun i => (up σ i).subst' v' up' (up' ξ) := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, rename, subst', upr])
  · symm; apply up0
  · simp [← rename.eq_1]
    rw [subst'_rename up0 upS]
    apply subst'_subst'
    · intro ξ σ _ H i
      cases funext H
      refine (funext_iff.1 (up_comp_sb_ren _ _) _).trans ?_
      congr; cases i <;> simp [up, *]
    · simp [upS, rename]

theorem subst_subst'₂ (ξ : S) (σ) (t : Expr) :
    (t.subst σ).subst' v' up' ξ = t.subst (fun i => (σ i).subst' v' up' ξ) := by
  apply subst'_subst'
  · intros _ _ _ H i
    cases funext H
    dsimp
    rw [up_comp_sb' up0 upS]
  · intro; rfl

omit up0 upS
theorem subst_rename (ξ σ) (t : Expr) :
    (t.subst σ).rename ξ = t.subst (rename ξ ∘ σ) :=
  subst_subst'₂ rfl rfl ..

theorem up_comp (σ τ : Nat → Expr) :
    up (comp σ τ) = comp (up σ) (up τ) := by
  ext i; unfold up comp snoc; cases i
  · rfl
  · grind [rename_subst, subst_rename]

include up0 upS in
theorem subst'_subst (ξ : S) (σ) (t : Expr) :
    (t.subst' v' up' ξ).subst σ = t.subst (fun i => (v' ξ i).subst σ) := by
  apply subst'_subst'
  · intros _ _ _ H i
    cases funext H
    dsimp
    refine (congrFun (up_comp ..) _).trans ?_
    simp [comp, subst]; congr
    cases i <;> simp [up, up0, upS]
  · intro; rfl
end

include up0 upS in
theorem subst'_subst (ξ : S) (σ) (t : Expr) :
    (t.subst' v' up' ξ).subst σ = t.subst (fun i => (v' ξ i).subst σ) := by
  apply subst'_subst'
  · intros _ _ _ H i
    cases funext H
    dsimp
    refine (congrFun (up_comp ..) _).trans ?_
    simp [comp, subst]; congr
    cases i <;> simp [up, up0, upS]
  · intro; rfl
end

theorem subst_subst (σ τ : Nat → Expr) (t : Expr) :
    (t.subst τ).subst σ = t.subst (comp σ τ) := by
  apply subst_subst'; apply up_comp

theorem comp_assoc (σ τ ρ) : comp σ (comp τ ρ) = comp (comp σ τ) ρ := by
  ext i
  conv => rhs; enter [0]; unfold comp
  rw [← subst_subst]; dsimp [comp]

theorem comp_snoc (σ τ : Nat → Expr) (t : Expr) :
    comp σ (snoc τ t) = snoc (comp σ τ) (t.subst σ) := by
  ext ⟨⟩ <;> dsimp [comp, snoc]

/-- The weakening substitution.
```
Γ ⊢ A
------------
Γ.A ⊢ ↑ : Γ
``` -/
def wk : Nat → Expr :=
  ofRen Nat.succ

@[simp]
theorem ofRen_succ : ofRen Nat.succ = wk := rfl

theorem up_eq_snoc (σ : Nat → Expr) : up σ = snoc (comp wk σ) (.bvar 0) := by
  ext i; unfold up comp; congr 1; ext j
  rw [rename_eq_subst_ofRen]; congr 1

@[simp]
theorem snoc_comp_wk (σ : Nat → Expr) (t) : comp (snoc σ t) wk = σ := by
  ext ⟨⟩ <;> dsimp [comp, snoc, wk, ofRen, subst, subst', -ofRen_succ]

@[simp]
theorem snoc_wk_zero : snoc wk (Expr.bvar 0) = Expr.bvar := by
  ext ⟨⟩ <;> dsimp [snoc, wk, ofRen, -ofRen_succ]

@[simp]
theorem wk_app (i) : wk i = Expr.bvar i.succ := rfl

theorem snoc_comp_wk_succ (σ n) : snoc (comp wk σ) (bvar (n + 1)) = comp wk (snoc σ (bvar n)) := by
  ext i; cases i <;> dsimp [comp, snoc, wk, -ofRen_succ, subst, ofRen]

/-- A substitution that instantiates one binder.
```
Γ ⊢ t : A
--------------
Γ ⊢ id.t : Γ.A
``` -/
def toSb (t : Expr) : Nat → Expr :=
  snoc Expr.bvar t

/-! ## Decision procedure -/

theorem snoc_comp_wk_zero_subst (σ) : snoc (comp σ Expr.wk) ((Expr.bvar 0).subst σ) = σ := by
  ext ⟨⟩ <;> dsimp [snoc, comp, subst, subst', wk, ofRen, -ofRen_succ]

theorem ofRen_comp (ξ₁ ξ₂ : Nat → Nat) : ofRen (ξ₁ ∘ ξ₂) = comp (ofRen ξ₁) (ofRen ξ₂) := rfl

theorem wk_app (n) : wk n = .bvar (n + 1) := by
  rw [wk, ofRen]


-- Rules from Fig. 1 in the paper.
@[autosubst low] theorem subst_bvar' {σ i} :
  subst σ (.bvar i) = σ i := rfl
@[autosubst low] theorem subst_pi {σ l l' A B} :
  subst σ (.pi l l' A B) = .pi l l' (A.subst σ) (B.subst (up σ)) := rfl
@[autosubst low] theorem subst_sigma {σ l l' A B} :
  subst σ (.sigma l l' A B) = .sigma l l' (A.subst σ) (B.subst (up σ)) := rfl
@[autosubst low] theorem subst_lam {σ l l' A B} :
  subst σ (.lam l l' A B) = .lam l l' (A.subst σ) (B.subst (up σ)) := rfl
@[autosubst low] theorem subst_app {σ l l' B} {fn arg} :
  subst σ (.app l l' B fn arg) = .app l l' (B.subst (up σ)) (fn.subst σ) (arg.subst σ) := rfl
@[autosubst low] theorem subst_pair {σ l l' B t u} :
  subst σ (.pair l l' B t u) = .pair l l' (B.subst (up σ)) (t.subst σ) (u.subst σ) := rfl
@[autosubst low] theorem subst_fst {σ l l' A B p} :
  subst σ (.fst l l' A B p) = .fst l l' (A.subst σ) (B.subst (up σ)) (p.subst σ) := rfl
@[autosubst low] theorem subst_snd {σ l l' A B p} :
  subst σ (.snd l l' A B p) = .snd l l' (A.subst σ) (B.subst (up σ)) (p.subst σ) := rfl
@[autosubst low] theorem subst_univ {σ l} :
  subst σ (.univ l) = .univ l := rfl
@[autosubst low] theorem subst_el {σ a} :
  subst σ (.el a) = .el (a.subst σ) := rfl
@[autosubst low] theorem subst_code {σ A} :
  subst σ (.code A) = .code (A.subst σ) := rfl
attribute [autosubst low]
  subst'
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

theorem subst_toSb_subst (B a : Expr) σ :
    (B.subst a.toSb).subst σ = (B.subst (Expr.up σ)).subst (a.subst σ).toSb := by
  autosubst

theorem subst_snoc_toSb_subst (B a b : Expr) σ :
    (B.subst <| Expr.snoc a.toSb b).subst σ =
      (B.subst <| Expr.up <| Expr.up σ).subst (Expr.snoc (a.subst σ).toSb (b.subst σ)) := by
  autosubst

end Expr
