import HoTTLeanTest.basic

/-! Test importing a theory.

Note: this is no longer as test-worthy since we deprecated theory-environments,
and `@[reflect]` just uses the ordinary Lean environment. -/

@[reflect]
noncomputable def tm_refl'' : tp_id := tm_refl'

@[reflect]
def B'' : Type := B
