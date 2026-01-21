import HoTTLean.Frontend.Commands

noncomputable section

declare_theory hott0

namespace HoTT0

hott0 def isSection₀₀ {A B : Type} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isEquiv₀₀ {A B : Type} (f : A → B) : Type :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₀₀ f g),
        isSection₀₀ h f

hott0 def happly {A : Type} {B : A → Type} {f g : (a : A) → B a} :
    Identity f g → (a : A) → Identity (f a) (g a) :=
  fun h _ => h.rec .rfl₀

hott0
  /-- HoTT book, Axiom 2.9.3. -/
  axiom funext₀₀ {A : Type} {B : A → Type} (f g : (a : A) → B a) :
    isEquiv₀₀ (@happly _ _ f g)

hott0 def isSection₁₀ {A : Type 1} {B : Type} (f : A → B) (g : B → A) : Type 1 :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isSection₀₁ {A : Type} {B : Type 1} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isEquiv₁₀ {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₁₀ f g),
        isSection₀₁ h f

hott0 def isEquiv₁₀_grpd {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (_ : isSection₁₀ f g),
      isSection₀₁ g f

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
  /-- The univalence axiom for sets. See HoTT book, Axiom 2.10.3. -/
  axiom setUv₀₀ {A B : Type} (A_set : isSet₀ A) (B_set : isSet₀ B) :
    isEquiv₁₀ (@Identity.toEquiv₀₀ A B)

-- Beginning Magma Definition
hott0 def magma :=  Σ (A : Type), A → (A → A)

-- Projection helpers
hott0 def magma.carrier (M : magma) : Type := M.1
hott0 def magma.op (M : magma) : M.carrier → M.carrier → M.carrier := M.2



-- Retrying how to solve the pull request for issue
-- Prove that equivalent magmas consisting of set-data (meaning magmas
-- (A,A×A→A) s.t. the underlying type A is a set) are equal using set-univalence in test/hott0.lean.
-- A magma homomorphism preserves the operation
hott0 def magma_hom (M N : magma) : Type :=
  Σ (f : M.carrier → N.carrier),
    ∀ (x y : M.carrier), Identity (f (M.op x y)) (N.op (f x) (f y))

-- A magma equivalence is an equivalence that preserves structure
hott0 def magma_equiv (M N : magma) : Type :=
  Σ (f : M.carrier → N.carrier),
    Σ (e : isEquiv₀₀ f),
      ∀ (x y : M.carrier), Identity (f (M.op x y)) (N.op (f x) (f y))

hott0 def Sigma.eta {A : Type} {B : A → Type} (w : Σ (a : A), B a) :
    Identity w ⟨w.1, w.2⟩ :=
  .rfl₀
