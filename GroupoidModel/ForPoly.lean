import Poly.UvPoly.Basic
import GroupoidModel.ForMathlib

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.UvPoly

variable {𝒞} [Category 𝒞] [HasTerminal 𝒞] [HasPullbacks 𝒞]

variable {E B : 𝒞} (P : UvPoly E B) (A : 𝒞)

def compDomEquiv {Γ E B D A : 𝒞} {P : UvPoly E B} {Q : UvPoly D A} :
    (Γ ⟶ compDom P Q) ≃
      (AB : Γ ⟶ P.functor.obj A) × (α : Γ ⟶ E) × (β : Γ ⟶ D) ×'
      (w : AB ≫ P.fstProj A = α ≫ P.p) ×'
      (β ≫ Q.p = pullback.lift AB α w ≫ (PartialProduct.fan P A).snd) :=
  calc
  _ ≃ (β : Γ ⟶ D) × (αB : Γ ⟶ pullback (PartialProduct.fan P A).fst P.p) ×'
      β ≫ Q.p = αB ≫ (PartialProduct.fan P A).snd :=
    pullbackHomEquiv
  _ ≃ (β : Γ ⟶ D) × (αB : (AB : Γ ⟶ P.functor.obj A) × (α : Γ ⟶ E) ×'
        AB ≫ P.fstProj A = α ≫ P.p) ×'
      β ≫ Q.p = pullback.lift αB.1 αB.2.1 αB.2.2 ≫ (PartialProduct.fan P A).snd :=
    Equiv.sigmaCongrRight (fun β => calc
      _ ≃ (αB : (AB : Γ ⟶ P.functor.obj A) × (α : Γ ⟶ E) ×' (AB ≫ P.fstProj A = α ≫ P.p)) ×'
          (β ≫ Q.p = pullback.lift αB.1 αB.2.1 αB.2.2 ≫ (PartialProduct.fan P A).snd) :=
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

@[simp] theorem compDomEquiv_symm_comp_p {Γ E B D A : 𝒞} {P : UvPoly E B}
    {Q : UvPoly D A} (AB : Γ ⟶ P.functor.obj A) (α : Γ ⟶ E)
    (β : Γ ⟶ D) (w : AB ≫ P.fstProj A = α ≫ P.p)
    (h : β ≫ Q.p = pullback.lift AB α w ≫ (PartialProduct.fan P A).snd) :
    compDomEquiv.symm ⟨AB,α,β,w,h⟩ ≫ (P.comp Q).p = AB := by
   simp [compDomEquiv, Equiv.psigmaCongrProp, Equiv.sigmaCongrRight_symm,
    Equiv.coe_fn_symm_mk, pullbackHomEquiv]

end CategoryTheory.UvPoly
