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


noncomputable section

namespace CategoryTheory.UvPoly
open Limits PartialProduct

universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasTerminal C] {E B : C}

namespace Equiv

variable (P : UvPoly E B) {Γ : C} (X Y : C) (f : X ⟶ Y)

def fst (pair : Γ ⟶ P @ X) :
    Γ ⟶ B :=
  fan P X |>.extend pair |>.fst

def snd (pair : Γ ⟶ P @ X) :
    pullback (fst P X pair) P.p ⟶ X :=
  fan P X |>.extend pair |>.snd

def mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    Γ ⟶ P @ X :=
  P.lift (Γ := Γ) (X := X) b x

@[simp]
lemma fst_mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    fst P X (mk P X b x) = b := by
  simp [fst, mk]

lemma snd_mk_heq (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    snd P X (mk P X b x) ≍ x := by
  simp [snd, mk, fst]
  sorry

lemma snd_mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    snd P X (mk P X b x) = eqToHom (by simp) ≫ x := by
  simp [fst, snd, mk]
  sorry

@[simp]
lemma eta (pair : Γ ⟶ P @ X) :
    mk P X (fst P X pair) (snd P X pair) = pair := by
  simp [fst, snd, mk]
  sorry

lemma fst_naturality_right (pair : Γ ⟶ P @ X) :
    fst P Y (pair ≫ P.functor.map f) = fst P X pair :=
  sorry

lemma snd_naturality_right (pair : Γ ⟶ P @ X) :
    snd P Y (pair ≫ P.functor.map f) =
    eqToHom (by rw [fst_naturality_right]) ≫ snd P X pair ≫ f :=
  sorry

lemma mk_naturality_right (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    mk P X b x ≫ P.functor.map f = mk P Y b (x ≫ f) :=
  sorry

open TwoSquare

section

variable {F : C} (P : UvPoly E B) (Q : UvPoly F B) (ρ : E ⟶ F) (h : P.p = ρ ≫ Q.p)

lemma fst_verticalNatTrans_app {Γ : C} (X : C) (pair : Γ ⟶ Q @ X) :
    Equiv.fst P X (pair ≫ (verticalNatTrans P Q ρ h).app X) = Equiv.fst Q X pair :=
    sorry

lemma snd_verticalNatTrans_app {Γ : C} (X : C) (pair : Γ ⟶ Q @ X) :
    Equiv.snd P X (pair ≫ (verticalNatTrans P Q ρ h).app X) =
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ρ)
      (by rw [fst_verticalNatTrans_app, pullback.condition, h, Category.assoc])) ≫
    Equiv.snd Q X pair :=
    sorry

lemma mk_comp_verticalNatTrans_app {Γ : C} (X : C) (b : Γ ⟶ B) (x : pullback b Q.p ⟶ X) :
    Equiv.mk Q X b x ≫ (verticalNatTrans P Q ρ h).app X = Equiv.mk P X b
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ρ)
    (by simp [pullback.condition, h]) ≫ x) :=
  sorry

end

end Equiv


end CategoryTheory.UvPoly
