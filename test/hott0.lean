import HoTTLean.Frontend.Reflect

noncomputable section

namespace HoTT0

@[reflect]
def isSection₀₀ {A B : Type} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

@[reflect]
def isEquiv₀₀ {A B : Type} (f : A → B) : Type :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₀₀ f g),
        isSection₀₀ h f

@[reflect]
def happly {A : Type} {B : A → Type} {f g : (a : A) → B a} :
    Identity f g → (a : A) → Identity (f a) (g a) :=
  fun h _ => h.rec .rfl₀

/-- HoTT book, Axiom 2.9.3. -/
@[reflect]
axiom funext₀₀ {A : Type} {B : A → Type} (f g : (a : A) → B a) :
  isEquiv₀₀ (@happly _ _ f g)

@[reflect]
def isSection₁₀ {A : Type 1} {B : Type} (f : A → B) (g : B → A) : Type 1 :=
  ∀ (a : A), Identity (g (f a)) a

@[reflect]
def isSection₀₁ {A : Type} {B : Type 1} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

@[reflect]
def isEquiv₁₀ {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₁₀ f g),
        isSection₀₁ h f

@[reflect]
def isEquiv₁₀_grpd {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (_ : isSection₁₀ f g),
      isSection₀₁ g f

@[reflect]
def transport₀ {A B : Type} (h : Identity A B) (a : A) : B :=
  h.rec a

@[reflect]
def isEquiv₀₀_transport₀ {A B : Type} (h : Identity A B) : isEquiv₀₀ (transport₀ h) :=
  h.rec ⟨fun a => a, fun a => a, fun _ => .rfl₀, fun _ => .rfl₀⟩

@[reflect]
def Identity.toEquiv₀₀ {A B : Type} : Identity A B → Σ (f : A → B), isEquiv₀₀ f :=
  fun h => ⟨transport₀ h, isEquiv₀₀_transport₀ h⟩

hott0
  /-- The type `A` is (-1)-truncated. -/
  def isProp₀ (A : Type) : Type :=
    ∀ (a a' : A), Identity a a'

hott0
  /-- The type `A` is 0-truncated. -/
  def isSet₀ (A : Type) : Type :=
    ∀ (a b : A), isProp₀ (Identity a b)

/-- The univalence axiom for sets. See HoTT book, Axiom 2.10.3. -/
@[reflect]
axiom setUv₀₀ {A B : Type} (A_set : isSet₀ A) (B_set : isSet₀ B) :
  isEquiv₁₀ (@Identity.toEquiv₀₀ A B)
