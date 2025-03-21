import Poly.UvPoly
import Poly.LCCC.Presheaf
import Poly.LCCC.Basic
import GroupoidModel.ForMathlib

open CategoryTheory Limits

noncomputable section

namespace UvPoly

variable {𝒞} [Category 𝒞] [HasTerminal 𝒞] [HasPullbacks 𝒞]

variable {E B : 𝒞} (P : UvPoly E B) (A : 𝒞)

-- TODO (JH) make issue
theorem pair_proj {Γ} (b : Γ ⟶ B) (e : pullback b P.p ⟶ A) :
    P.pairPoly b e ≫ P.proj _ = b := by
  sorry

def genPb.snd : P.genPb A ⟶ E :=
  pullback.snd (f := P.proj A) (g := P.p)

variable {A}
theorem genPb.condition :
    genPb.snd P A ≫ P.p = genPb.fst P A ≫ P.proj A := by
  simp [genPb.fst,genPb.snd,pullback.condition]

def compDomEquiv {Γ E B D A : 𝒞} {P : UvPoly E B} {Q : UvPoly D A} :
    (Γ ⟶ compDom P Q)
    ≃ (AB : Γ ⟶ P.functor.obj A) × (α : Γ ⟶ E) × (β : Γ ⟶ D)
    ×' (h : AB ≫ P.proj A = α ≫ P.p)
    ×' (β ≫ Q.p = pullback.lift AB α h ≫ genPb.u₂ P A) :=
  calc
  _ ≃ (β : Γ ⟶ D) × (αB : Γ ⟶ genPb P A)
  ×' (β ≫ Q.p = αB ≫ genPb.u₂ P A) := pullbackHomEquiv
  _ ≃ (β : Γ ⟶ D) × (αB : (AB : Γ ⟶ P.functor.obj A) × (α : Γ ⟶ E) ×' AB ≫ P.proj A = α ≫ P.p) ×'
      β ≫ Q.p = pullback.lift αB.1 αB.2.1 αB.2.2 ≫ genPb.u₂ P A :=
    Equiv.sigmaCongrRight (fun β =>
    calc
    _ ≃
    (αB : (AB : Γ ⟶ P.functor.obj A)
    × (α : Γ ⟶ E)
    ×' (AB ≫ P.proj A = α ≫ P.p))
    ×' (β ≫ Q.p = pullback.lift αB.1 αB.2.1 αB.2.2 ≫ genPb.u₂ P A) :=
      Equiv.psigmaCongrProp pullbackHomEquiv (fun αB => by
        apply Eq.congr_right
        congr 1
        apply pullback.hom_ext
        · simp [pullbackHomEquiv]
        · simp [pullbackHomEquiv]))
  _ ≃ _ := {
      -- TODO should be general tactic for this?
      toFun x := ⟨ x.2.1.1, x.2.1.2.1 , x.1 , x.2.1.2.2, x.2.2 ⟩
      invFun x := ⟨ x.2.2.1 , ⟨ x.1, x.2.1 , x.2.2.2.1 ⟩ , x.2.2.2.2 ⟩
      left_inv _ := rfl
      right_inv _ := rfl }

end UvPoly

variable {𝒞 : Type*} [SmallCategory 𝒞] [HasTerminal 𝒞]

instance : LCC (Psh 𝒞) :=
  @LCCC.mkOfOverCC _ _ _ ⟨CategoryOfElements.presheafOverCCC⟩

instance {X Y : Psh 𝒞} (f : X ⟶ Y) : CartesianExponentiable f where
  functor := LCC.pushforward f
  adj := LCC.adj _
