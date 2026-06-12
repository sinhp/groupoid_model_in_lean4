import test.hott0

/-! ## Structure identity principle for pointed (set-)types

A warm-up before the magma SIP: shows that the same recipe — set-univalence
plus `Sigma.eq₁` — identifies pointed sets that are connected by a
point-preserving equivalence. Should typecheck quickly. -/

noncomputable section

namespace HoTT0

hott0
  /-- A pointed type: a carrier with a chosen point.
  Set-ness of the carrier is *not* bundled here; it is supplied as a
  hypothesis to the SIP theorem (matching how `magma` treats `isSet₀`). -/
  def pointedType : Type 1 := Σ (A : Type), A

hott0 def pointedType.carrier (M : pointedType) : Type := M.1
hott0 def pointedType.point (M : pointedType) : M.carrier := M.2

hott0 def pointedType_equiv (M N : pointedType) : Type :=
  Σ (f : M.carrier → N.carrier),
    Σ (_ : isEquiv₀₀ f),
      Identity (f M.point) N.point

hott0
  /-- Transport of a point along a univalence-induced path equals
  applying the equivalence. -/
  axiom transport_point {A B : Type}
      (A_set : isSet₀ A) (B_set : isSet₀ B)
      (f : A → B) (e : isEquiv₀₀ f)
      (a : A) :
    Identity
      (@Identity.rec Type A (fun X _ => X) a B ((setUv₀₀ A_set B_set).1 ⟨f, e⟩))
      (f a)

-- The following proofs need more heartbeats than the default 200000
-- to push the certifying typechecker through `setUv₀₀`/`Identity.rec`
-- unfoldings.
set_option maxHeartbeats 4000000

-- Profiling: bisecting which def is slow.
set_option profiler true
-- set_option trace.profiler true  -- adds large overhead; turn on only when needed

hott0 def pointedType_carrier_eq
    (M N : pointedType)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : pointedType_equiv M N)
    : Identity M.carrier N.carrier :=
  (setUv₀₀ M_set N_set).1 ⟨e.1, e.2.1⟩

-- hott0 def transported_point
--     (M N : pointedType)
--     (M_set : isSet₀ M.carrier)
--     (N_set : isSet₀ N.carrier)
--     (e : pointedType_equiv M N)
--     : N.carrier :=
--   @Identity.rec Type M.carrier (fun X _ => X)
--     M.point N.carrier (pointedType_carrier_eq M N M_set N_set e)

-- hott0 def pointedType_point_eq
--     (M N : pointedType)
--     (M_set : isSet₀ M.carrier)
--     (N_set : isSet₀ N.carrier)
--     (e : pointedType_equiv M N)
--     : Identity (transported_point M N M_set N_set e) N.point :=
--   (transport_point M_set N_set e.1 e.2.1 M.point).trans₀ e.2.2

-- TEMPORARILY commented out for profiling — re-enable once the
-- preceding defs are understood.
-- hott0
--   /-- One direction of the structure identity principle for pointed sets:
--   a point-preserving equivalence of pointed sets yields an identification.
--   The full SIP would assert that this map is itself an equivalence. -/
--   def pointedType_eq_of_equiv
--       (M N : pointedType)
--       (M_set : isSet₀ M.carrier)
--       (N_set : isSet₀ N.carrier)
--       (e : pointedType_equiv M N)
--       : Identity M N :=
--     Sigma.eq₁
--       (pointedType_carrier_eq M N M_set N_set e)
--       (pointedType_point_eq M N M_set N_set e)

hott0 def pointedType_carrier_eq'
    (M N : pointedType)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : pointedType_equiv M N)
    : Identity M.carrier N.carrier :=
  pointedType_carrier_eq M N M_set N_set e

open SynthLean open Expr Neut Val
#print pointedType_carrier_eq'

hott0 axiom foo : Type
hott0 def foo' (x : foo) := x
#print foo
#print foo'
