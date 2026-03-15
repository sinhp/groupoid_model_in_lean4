import HoTTLean.Frontend.Commands

set_option profiler true

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

--Adding Is Contractible over here
hott0 def isContr₀ (A : Type) : Type := Σ (a : A), (∀ (b : A), Identity a b)

hott0
  /-- The type `A` is (-1)-truncated. -/
  def isProp₀ (A : Type) : Type :=
    ∀ (a a' : A), Identity a a'

hott0
  /-- The type `A` is 0-truncated. -/
  def isSet₀ (A : Type) : Type :=
    ∀ (a b : A), isProp₀ (Identity a b)

hott0
  /-- The univalence axiom for sets. See HoTT book, Axiom 2.10.3. -/
  axiom setUv₀₀ {A B : Type} (A_set : isSet₀ A) (B_set : isSet₀ B) :
    isEquiv₁₀ (@Identity.toEquiv₀₀ A B)


-- Consider having type aliases for long subgoals
-- ap on one type
hott0 def ap {A B : Type} (f : A → B) {a a' : A} (p : Identity a a') : Identity (f a) (f a') :=
  p.rec (Identity.rfl₀)

-- ap on two types
hott0 def ap₂ {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (p : Identity a a') (q : Identity b b') : Identity (f a b) (f a' b') :=
  p.rec (ap (f a) q)

--=======================================
--Sigma Type Stuff

-- Sigma type Eta expansion
hott0 def Sigma.eta {A : Type} {B : A → Type} (w : Σ (a : A), B a) :
    Identity w ⟨w.1, w.2⟩ := Identity.rfl₀


-- Sigma eq for Type
hott0 def Sigma.eq {A : Type} {B : A → Type} {w w' : Σ (a : A), B a}
    (p : Identity w.1 w'.1)
    (q : Identity (p.rec w.2) w'.2)
    : Identity w w' :=
  @Identity.rec
    A
    w.1
    (fun x p' => ∀ (b' : B x), Identity (p'.rec w.2) b' → Identity w ⟨x, b'⟩)
    (fun b' q' =>
      @Identity.rec
        (B w.1)
        w.2
        (fun b'' q'' => Identity w ⟨w.1, b''⟩)
        Identity.rfl₀
        b'
        q')
    w'.1
    p
    w'.2
    q

-- Sigma eq for Type 1
hott0 def Sigma.eq₁ {A : Type 1} {B : A → Type} {w w' : Σ (a : A), B a}
    (p : Identity w.1 w'.1)
    (q : Identity (p.rec w.2) w'.2)
    : Identity w w' :=
  @Identity.rec
    A
    w.1
    (fun x p' => ∀ (b' : B x), Identity (p'.rec w.2) b' → Identity w ⟨x, b'⟩)
    (fun b' q' =>
      @Identity.rec
        (B w.1)
        w.2
        (fun b'' q'' => Identity w ⟨w.1, b''⟩)
        Identity.rfl₁
        b'
        q')
    w'.1
    p
    w'.2
    q

-- function extensionality
hott0 def funext₀ {A : Type} {B : A → Type} {f g : (a : A) → B a}
    (h : ∀ (a : A), Identity (f a) (g a)) : Identity f g :=
  (funext₀₀ f g).1 h

--=====================================
-- Transport on Π-Types

hott0
  /-- Transport on binary operations -/
  axiom transport_op {A B : Type}
      (A_set : isSet₀ A) (B_set : isSet₀ B)
      (f : A → B) (e : isEquiv₀₀ f)
      (op : A → A → A) (b₁ b₂ : B) :
    Identity
      (@Identity.rec Type A (fun X _ => X → X → X) op B ((setUv₀₀ A_set B_set).1 ⟨f, e⟩) b₁ b₂)
      (f (op (e.1 b₁) (e.1 b₂)))


---============================================
-- Beginning Magma Definition
hott0 def magma :=  Σ (A : Type), A → (A → A)

-- Projection helpers
-- The set
hott0 def magma.carrier (M : magma) : Type := M.1
 -- The Operation
hott0 def magma.op (M : magma) : M.carrier → M.carrier → M.carrier := M.2

-- Prove that equivalent magmas consisting of set-data (meaning magmas
-- (A,A×A→A) s.t. the underlying type A is a set) are equal using set-univalence in test/hott0.lean.
-- A magma homomorphism preserves the operation
-- hott0 def magma_hom (M N : magma) : Type :=
--   Σ (f : M.carrier → N.carrier),
--     ∀ (x y : M.carrier), Identity (f (M.op x y)) (N.op (f x) (f y))

-- A magma equivalence is an equivalence that preserves structure

/-

Proof Idea
------------
Two magmas are given thus
M = (A, m) where A is a set and m : A → A → A
N = (B, n) where B is a set and n : B → B → B

We have an equivalence of types e : A ≃ B
with forward map f : A → B and inverse map g : B → A

We have e : isEquiv₀₀ f which gives us:
1. g : B → A (inverse)
2. h : B → A (another inverse)
3. α : isSection₁₀ f g = a (section)
4. β : isSection₀₁ h f = a (retraction))

f_hom: ∀ (x y : A), Identity (f (m x y)) (n (f x) (f y)) (homomorphism property)

Then we prove M = N, which is (A, m) = (B, n)


Step 1: Get the carriers equal using set-univalence
 we can convert the equivalence e into a path p : Identity A B
 This uses the inverse of the univalence equivalence for sets
 p = (setUv₀₀ A_set B_set).1 ⟨f, e⟩

Step 2: Transport the operation m along p to get an operation on B
 tranport^{X ↦ X → X → X}(p,m) : B → B → B

Step 3: Show that the transported operation is equal to n pointwise
  For all x,y : B, we have a path
  Identity (transported_op M N M_set N_set e x y) (N.op x y)

  transported_op m x y
    = f(m(g(x), g(y)))    -- by transport_op
    = n(f(g(x)), f(g(y))) -- by f_hom
    = n(x,y)              -- by α (section : f(g(y)) = y) applied twice

Step 4: Use function extensionality to get the operations equal
  funext₀ on the pointwise equalities to get
  Identity (transported_op M N M_set N_set e) (N.op)

Step 5: Combine the equalities of the carriers and operations to get
  Identity M N

-/

hott0 def magma_equiv (M N : magma) : Type :=
  Σ (f : M.carrier → N.carrier),
    Σ (e : isEquiv₀₀ f),
      ∀ (x y : M.carrier), Identity (f (M.op x y)) (N.op (f x) (f y))

hott0
  axiom equiv_retraction {A B : Type}
      (A_set : isSet₀ A) (B_set : isSet₀ B)
      (f : A → B) (e : isEquiv₀₀ f) (b : B) :
    Identity (f (e.1 b)) b

set_option maxHeartbeats 500000000

-- Seems to be a problem, maybe try specifying which path to take
hott0 def magma_carrier_eq
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : Identity M.carrier N.carrier :=
  (setUv₀₀ M_set N_set).1 ⟨e.1, e.2.1⟩

-- Strategy Show any two operations on M, or N are the same under univalence
-- Try a simpler intermediate definition for timeouts
hott0 def transported_op
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : N.carrier → N.carrier → N.carrier :=
  @Identity.rec Type M.carrier (fun X _ => X → X → X)
    M.op N.carrier ((setUv₀₀ M_set N_set).1 ⟨e.1, e.2.1⟩)


-- Univalence axiom doesn't specify, but asserts existence of a path.
-- Left sorry's in, just in case things people want to run it without waiting so long
set_option diagnostics true

hott0 def subexpr
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    (x y : N.carrier)
    :=
    -- sorry
    ((e.2.2 (e.2.1.1 x) (e.2.1.1 y)).trans₀
      (ap₂ N.op
        (equiv_retraction M_set N_set e.1 e.2.1 x)
        (equiv_retraction M_set N_set e.1 e.2.1 y)))


-- VEERRY Sloow, give it 1h 15 mins on a MacBook Air with Apple M4, 16GB RAM
-- With nothing else but VSCode Open
hott0 def magma_op_eq_pointwise
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    (x y : N.carrier)
    : Identity (transported_op M N M_set N_set e x y) (N.op x y) :=
      -- sorry
  (transport_op M_set N_set e.1 e.2.1 M.op x y).trans₀
    (subexpr M N M_set N_set e x y)

-- Apply function extensionality twice
hott0 def magma_op_eq
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : Identity (transported_op M N M_set N_set e) N.op :=
  funext₀ (fun x => funext₀ (fun y =>
    magma_op_eq_pointwise M N M_set N_set e x y))

-- Combine everything with Sigma.eq
hott0 def magma_eq_of_equiv
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : Identity M N :=
  Sigma.eq₁
    (magma_carrier_eq M N M_set N_set e)
    (magma_op_eq M N M_set N_set e)
