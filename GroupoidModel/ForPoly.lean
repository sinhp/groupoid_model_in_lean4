import Poly.UvPolynomial
import Poly.LCCC.Presheaf
import Poly.LCCC.Basic

open CategoryTheory Limits

noncomputable section

namespace UvPoly

variable {𝒞} [Category 𝒞] [HasTerminal 𝒞] [HasPullbacks 𝒞]

-- TODO: rm this and just use `equiv` directly
/-- Universal property of the polynomial functor. -/
def _root_.UvPoly.equiv' {E B : 𝒞} (P : UvPoly E B) (Γ X : 𝒞) :
    (Γ ⟶ P.functor.obj X) ≃ Σ b : Γ ⟶ B, pullback P.p b ⟶ X :=
  (UvPoly.equiv P Γ X).trans <|
  Equiv.sigmaCongrRight fun _ =>
  ((yoneda.obj X).mapIso (pullbackSymmetry ..).op).toEquiv

end UvPoly

variable {𝒞 : Type*} [SmallCategory 𝒞] [HasTerminal 𝒞]

instance : LCC (Psh 𝒞) :=
  @LCCC.mkOfOverCC _ _ _ ⟨CategoryOfElements.presheafOverCCC⟩

instance {X Y : Psh 𝒞} (f : X ⟶ Y) : CartesianExponentiable f where
  functor := LCC.pushforward f
  adj := LCC.adj _
