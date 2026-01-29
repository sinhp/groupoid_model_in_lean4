import HoTTLean.Frontend.Reflect

/-! Test basic typechecker functionality. -/

/-! ## Universes -/

@[reflect]
def tp_univ : Type 1 := Type 0

/-! ## Functions -/

@[reflect]
def tp_pi_nondep : Type 1 := Type 0 → Type 0

def tm_lam_nondep : Type 0 → Type 0 := fun x => x

def tp_pi : Type 1 := (A : Type 0) → A → A

def tm_lam : (A : Type 0) → A → A := fun _ a => a

def tm_app : (A : Type 0) → A → (A → A) → A := fun _ a f => f a

/-! ## Products -/

@[reflect]
def tp_sigma : Type 1 :=
  (A : Type) × A

@[reflect]
def tp_sigma_partial : (A : Type) → (B : A → Type) → Type :=
  @Sigma

@[reflect]
def tm_pair_nondep : (_ : Type 1) × Type 1 :=
  ⟨Type 0, Type 0⟩

-- Noncomputable due to Lean issue https://github.com/leanprover/lean4/issues/9692
-- FIXME: needs at least 4 universes.
-- mltt noncomputable def tm_pair : (A : Type 2) × A :=
--   ⟨Type 1, Type 0⟩

@[reflect]
def tm_fst : Type 2 :=
  { fst := Type 1, snd := Type 0 : (A : Type 2) × A }.fst

@[reflect]
def tm_snd : Type 1 :=
  { fst := Type 1, snd := Type 0 : (A : Type 2) × A }.snd

/-! ## Identity types -/

@[reflect]
def tp_id : Type 2 :=
  @Identity (Type 1) Type Type

@[reflect]
def tm_refl : @Identity (Type 1) Type Type :=
  @Identity.refl (Type 1) Type

@[reflect]
noncomputable def tm_idRec (A B : Type) (eq : @Identity Type A B) (a : A) : B :=
  @Identity.rec Type A (fun T _ => T) a B eq

/-! ## Definitional equalities -/

@[reflect]
def defeq_el_code {A : Type} (a : A) : A :=
  (fun (α : Type) (x : α) => x) ((fun (α : Type 1) (x : α) => x) Type A) a

/-! ## Using previous definitions -/

@[reflect]
def tm_refl' : tp_id := tm_refl

/-! ## Adding axioms -/

@[reflect]
axiom B : Type

@[reflect]
axiom b : B

@[reflect]
axiom C : B → Type

@[reflect]
axiom c : C b

/-! ## Using axioms -/

@[reflect]
def Cb : Type := C b

@[reflect]
noncomputable def c' : Cb := c

/-! ## Using `sorry` -/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
@[reflect]
def foo : Type := sorry
