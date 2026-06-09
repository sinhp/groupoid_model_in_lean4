import test.hott0

/-! ## Structure identity principle for magmas

Proves that equivalent magmas with set-underlying data are equal,
using set-univalence (`setUv₀₀`) from `test/hott0.lean`.

Closes <https://github.com/sinhp/HoTTLean/issues/165>.

NOTE: the proofs in this file are very slow.
`magma_op_eq_pointwise` has been reported to take ~1h 15min on an M4 MacBook Air.
Do not include this file in the default test target. -/

noncomputable section

namespace HoTT0

-- Transport on binary operations.
-- TODO: should be derivable from set-univalence + funext, currently postulated.
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
-- (A,A×A→A) s.t. the underlying type A is a set) are equal using set-univalence.
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
