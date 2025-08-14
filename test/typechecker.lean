import GroupoidModel.Syntax.Typechecker.Frontend

/- Tests to ensure the HoTT0 typechecker works. -/

/-! ## Universes -/

hott def tp_univ : Type 1 := Type 0

/-! ## Functions -/

hott def tp_pi_nondep : Type 1 := Type 0 → Type 0

hott def tm_lam_nondep : Type 0 → Type 0 := fun x => x

hott def tp_pi : Type 1 := (A : Type 0) → A → A

hott def tm_lam : (A : Type 0) → A → A := fun _ a => a

hott def tm_app : (A : Type 0) → A → (A → A) → A := fun _ a f => f a

/-! ## Products -/

hott def tp_sigma : Type 1 :=
  (A : Type) × A

hott def tp_sigma_partial : (A : Type) → (B : A → Type) → Type :=
  @Sigma

hott def tm_pair_nondep : (_ : Type 1) × Type 1 :=
  ⟨Type 0, Type 0⟩

-- Noncomputable due to Lean issue https://github.com/leanprover/lean4/issues/9692
hott noncomputable def tm_pair : (A : Type 2) × A :=
  ⟨Type 1, Type 0⟩

hott def tm_fst : Type 2 :=
  { fst := Type 1, snd := Type 0 : (A : Type 2) × A }.fst

hott def tm_snd : Type 1 :=
  { fst := Type 1, snd := Type 0 : (A : Type 2) × A }.snd

/-! ## Identity types -/

hott def tp_id : Type 2 :=
  @HoTT0.Id (Type 1) Type Type

-- TODO
hott def tm_refl : @HoTT0.Id (Type 1) Type Type :=
  @HoTT0.Id.refl (Type 1) Type

-- TODO: idRec

/-! ## Definitional equalities -/

hott def defeq_el_code {A : Type} (a : A) : A :=
  (fun (α : Type) (x : α) => x) ((fun (α : Type 1) (x : α) => x) Type A) a
