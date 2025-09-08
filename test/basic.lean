import GroupoidModel.Syntax.Frontend.Commands

/-! Test basic typechecker functionality. -/

/-! ## Declaring theories -/

declare_theory mltt

declare_theory anothertt

/-! ## Universes -/

mltt def tp_univ : Type 1 := Type 0

/-! ## Functions -/

mltt def tp_pi_nondep : Type 1 := Type 0 → Type 0

mltt def tm_lam_nondep : Type 0 → Type 0 := fun x => x

mltt def tp_pi : Type 1 := (A : Type 0) → A → A

mltt def tm_lam : (A : Type 0) → A → A := fun _ a => a

mltt def tm_app : (A : Type 0) → A → (A → A) → A := fun _ a f => f a

/-! ## Products -/

mltt def tp_sigma : Type 1 :=
  (A : Type) × A

mltt def tp_sigma_partial : (A : Type) → (B : A → Type) → Type :=
  @Sigma

mltt def tm_pair_nondep : (_ : Type 1) × Type 1 :=
  ⟨Type 0, Type 0⟩

-- Noncomputable due to Lean issue https://github.com/leanprover/lean4/issues/9692
mltt noncomputable def tm_pair : (A : Type 2) × A :=
  ⟨Type 1, Type 0⟩

mltt def tm_fst : Type 2 :=
  { fst := Type 1, snd := Type 0 : (A : Type 2) × A }.fst

mltt def tm_snd : Type 1 :=
  { fst := Type 1, snd := Type 0 : (A : Type 2) × A }.snd

/-! ## Identity types -/

mltt def tp_id : Type 2 :=
  @Identity (Type 1) Type Type

mltt def tm_refl : @Identity (Type 1) Type Type :=
  @Identity.refl (Type 1) Type

mltt noncomputable def tm_idRec (A B : Type) (eq : @Identity Type A B) (a : A) : B :=
  @Identity.rec Type A (fun T _ => T) a B eq

/-! ## Definitional equalities -/

mltt def defeq_el_code {A : Type} (a : A) : A :=
  (fun (α : Type) (x : α) => x) ((fun (α : Type 1) (x : α) => x) Type A) a

/-! ## Using previous definitions -/

mltt def tm_refl' : tp_id := tm_refl

/-! ## Adding axioms -/

mltt axiom B : Type

mltt axiom b : B

mltt axiom C : B → Type

mltt axiom c : C b

/-! ## Using axioms -/

mltt def Cb : Type := C b

mltt noncomputable def c' : Cb := c

/-! ## Using `sorry` -/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
mltt def foo : Type := sorry
