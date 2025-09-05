import GroupoidModel.Syntax.Frontend.Commands

noncomputable section

declare_theory hott0

namespace HoTT0

hott0 axiom funext₀₀ {A B : Type} (f g : A → B)
  (ext : ∀ (x : A), Identity (f x) (g x)) : Identity f g

hott0 def isInv₀₀ {A B : Type} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isEquiv₀₀ {A B : Type} (f : A → B) : Type :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isInv₀₀ f g),
        isInv₀₀ h f

hott0 def isInv₁₀ {A : Type 1} {B : Type} (f : A → B) (g : B → A) : Type 1 :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isInv₀₁ {A : Type} {B : Type 1} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isEquiv₁₀ {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isInv₁₀ f g),
        isInv₀₁ h f

hott0 def transport₀ {A B : Type} (h : Identity A B) (a : A) : B :=
  h.rec a

hott0 def isEquiv₀₀_transport₀ {A B : Type} (h : Identity A B) : isEquiv₀₀ (transport₀ h) :=
  h.rec ⟨fun a => a, fun a => a, fun _ => .rfl₀, fun _ => .rfl₀⟩

hott0 def Identity.toEquiv₀₀ {A B : Type} : Identity A B → Σ (f : A → B), isEquiv₀₀ f :=
  fun h => ⟨transport₀ h, isEquiv₀₀_transport₀ h⟩

hott0 def isProp₀ (A : Type) : Type :=
  ∀ (a a' : A) (h h' : Identity a a'), Identity h h'

hott0 def isSet₀ (A : Type) : Type :=
  ∀ (a b : A), isProp₀ (Identity a b)

hott0
  /-- The univalence axiom for sets. -/
  axiom setUv₀₀ {A B : Type} (ha : isSet₀ A) (hb : isSet₀ B) :
    isEquiv₁₀ (@Identity.toEquiv₀₀ A B)
