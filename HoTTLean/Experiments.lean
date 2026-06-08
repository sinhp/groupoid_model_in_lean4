import HoTTLean.Frontend.Commands

namespace HoTTLean.Experiments

declare_theory ab

ab axiom add (X : Type) : X → X → X

ab axiom zero (X : Type) : X

-- I would like this to be stated as an equality `(add X a (add X b c)) = (add X (add X a b) c)`
-- but that gives an error
ab axiom assoc {X : Type} (a b c : X) : Identity (add X a (add X b c)) (add X (add X a b) c)

-- I would also like this to be stated with `=`
ab axiom comm' {X : Type} (a b : X) : Identity (add X a b) (add X b a)

-- I would also like this to be stated with `=`
ab axiom add_zero {X : Type} (a : X) : Identity (add X a (zero X)) a

-- Now I want to state and prove the following theorem internally:
-- `ab theorem zero_add {X : Type} (a : X) : Identity (add X (zero X) a) a := ...`

-- And then I want to prove that any `X : Type` with `[AddCommGroup X]` is a model for the theory
-- `ab` by proving that it satisfies all the axioms.

-- Next, I want to prove that `zero_add` holds for any `X : Type` with `[AddCommGroup X]`
-- by using the `ab` theorem `zero_add` (not relying on an existing mathlib proof).

end HoTTLean.Experiments
