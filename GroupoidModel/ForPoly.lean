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

-- TODO: add this to Poly
def _root_.UvPoly.comp {𝒞} [Category 𝒞] [HasFiniteWidePullbacks 𝒞] [HasTerminal 𝒞]
    {E B D C : 𝒞} (P1 : UvPoly E B) (P2 : UvPoly D C) : UvPoly (P2.functor.obj E) (P1.functor.obj C) :=
   let f : E ⟶ B := P1.p
   let g : D ⟶ C := P2.p
   {
     p := sorry
     exp := sorry
   }

end UvPoly

variable {𝒞 : Type*} [SmallCategory 𝒞] [HasTerminal 𝒞]

instance : LCC (Psh 𝒞) :=
  @LCCC.mkOfOverCC _ _ _ ⟨CategoryOfElements.presheafOverCCC⟩

instance {X Y : Psh 𝒞} (f : X ⟶ Y) : CartesianExponentiable f where
  functor := LCC.pushforward f
  adj := LCC.adj _
