import HoTTLean.Frontend.Commands

/-! Axioms of HoTT0 and basic constructions. -/

noncomputable section

declare_theory hott0

namespace HoTT0

/-! ## Sections and equivalences -/

hott0 def isSection₀₀ {A B : Type} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isSection₁₀ {A : Type 1} {B : Type} (f : A → B) (g : B → A) : Type 1 :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isSection₀₁ {A : Type} {B : Type 1} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isEquiv₀₀ {A B : Type} (f : A → B) : Type :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₀₀ f g),
        isSection₀₀ h f

hott0 def isEquiv₁₀ {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₁₀ f g),
        isSection₀₁ h f

/-! ## Function extensionality -/

hott0 def happly₀₀ {A : Type} {B : A → Type} {f g : (a : A) → B a} :
    Identity f g → (a : A) → Identity (f a) (g a) :=
  fun h _ => h.rec .rfl₀

hott0
  /-- HoTT book, Axiom 2.9.3. -/
  axiom isEquiv₀₀_happly₀₀ {A : Type} {B : A → Type} (f g : (a : A) → B a) :
    isEquiv₀₀ (@happly₀₀ _ _ f g)

hott0 def funext₀₀ {A : Type} {B : A → Type} {f g : (a : A) → B a} :
    (∀ a : A, Identity (f a) (g a)) → Identity f g :=
  -- TODO: frontend rejects auxiliary match-defintion
  -- let ⟨F, _⟩ := isEquiv₀₀_happly₀₀ f g
  fun h => (isEquiv₀₀_happly₀₀ f g).fst h

/-! ## H-level -/

hott0
  /-- The type `A` is (-1)-truncated. -/
  def isProp₀ (A : Type) : Type :=
    ∀ (a a' : A), Identity a a'

hott0
  /-- The type `A` is 0-truncated. -/
  def isSet₀ (A : Type) : Type :=
    ∀ (a b : A), isProp₀ (Identity a b)

hott0
  /-- The type `A` is 1-truncated. -/
  def isGrpd₀ (A : Type) : Type :=
    ∀ (a b : A), isSet₀ (Identity a b)

/-! ## Set univalence -/

hott0 def transport₀ {A B : Type} (h : Identity A B) (a : A) : B :=
  h.rec a

hott0 def isEquiv₀₀_transport₀ {A B : Type} (h : Identity A B) : isEquiv₀₀ (transport₀ h) :=
  h.rec ⟨fun a => a, fun a => a, fun _ => .rfl₀, fun _ => .rfl₀⟩

hott0 def Identity.toEquiv₀₀ {A B : Type} : Identity A B → Σ (f : A → B), isEquiv₀₀ f :=
  fun h => ⟨transport₀ h, isEquiv₀₀_transport₀ h⟩

hott0
  /-- The univalence axiom for sets. See HoTT book, Axiom 2.10.3. -/
  axiom setUv₀₀ {A B : Type} (A_set : isSet₀ A) (B_set : isSet₀ B) :
    isEquiv₁₀ (@Identity.toEquiv₀₀ A B)

/-! ## Groupoids -/

hott0
  /-- Every type is a groupoid. -/
  axiom isGrpd₀_all (A : Type) : isGrpd₀ A

hott0 def grpdIsEquiv₀₀ {A B : Type} (f : A → B) : Type :=
  Σ (g : B → A),
    Σ (_ : isSection₀₀ f g),
      isSection₀₀ g f

hott0 def ofGrpdIsEquiv₀₀ {A B : Type} {f : A → B} :
    grpdIsEquiv₀₀ f → isEquiv₀₀ f :=
  fun e => ⟨e.1, e.1, e.2.1, e.2.2⟩

hott0 def grpdIsEquiv₀₀_ofGrpdIsEquiv₀₀ {A B : Type} (f : A → B) :
    grpdIsEquiv₀₀ (ofGrpdIsEquiv₀₀ (f := f)) :=
  sorry

hott0 def isEquiv₀₀_ofGrpdIsEquiv₀₀ {A B : Type} (f : A → B) :
    isEquiv₀₀ (ofGrpdIsEquiv₀₀ (f := f)) :=
  -- TODO: frontend timeout
  -- ofGrpdIsEquiv₀₀ (grpdIsEquiv₀₀_ofGrpdIsEquiv₀₀ f)
  sorry
