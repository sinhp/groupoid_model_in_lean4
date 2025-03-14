import Poly.UvPoly
import Poly.LCCC.Presheaf
import Poly.LCCC.Basic
import GroupoidModel.ForMathlib

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

def genPb.snd {E B: 𝒞} (P : UvPoly E B) (X : 𝒞) : P.genPb X ⟶ E :=
  pullback.snd (f := P.proj X) (g := P.p)

theorem genPb.condition {E B A: 𝒞} (P : UvPoly E B) : genPb.snd P A ≫ P.p = genPb.fst P A ≫ P.proj A := by
  simp [genPb.fst,genPb.snd,pullback.condition]

def compDomUP {Γ E B D A : 𝒞} {P : UvPoly E B} {Q : UvPoly D A} : (Γ ⟶ compDom P Q) ≃ (β : Γ ⟶ D) × (αB : Γ ⟶ genPb P A) ×' (β ≫ Q.p = αB ≫ genPb.u₂ P A) where
  toFun f := ⟨f ≫ (pullback.fst Q.p (genPb.u₂ P A)), f ≫ (pullback.snd Q.p (genPb.u₂ P A)), by simp [pullback.condition (f := Q.p) (g := genPb.u₂ P A)]⟩
  invFun := by
    rintro ⟨β,αB,h⟩
    exact pullback.lift β αB h
  left_inv f := by
    refine pullback.hom_ext ?_ ?_
    . simp
    . simp
  right_inv := by
    rintro ⟨β,αB,h⟩
    simp

def pullbackUP {A B C: 𝒞} (Γ : 𝒞) (f : A ⟶ C) (g : B ⟶ C) : (Γ ⟶ pullback f g) ≃ (fst : Γ ⟶ A) × (snd : Γ ⟶ B) ×' (fst ≫ f = snd ≫ g) where
  toFun h := ⟨h ≫ pullback.fst f g, h ≫ pullback.snd f g, by simp[pullback.condition]⟩
  invFun := by
    rintro ⟨fst,snd,h⟩
    exact pullback.lift fst snd h
  left_inv f := by
    refine pullback.hom_ext ?_ ?_
    . simp[genPb.fst]
    . simp[genPb.snd]
  right_inv := by
    rintro ⟨fst,snd,h⟩
    simp[genPb.fst,genPb.snd]

def compDomUP' {Γ E B D A : 𝒞} {P : UvPoly E B} {Q : UvPoly D A} : (Γ ⟶ compDom P Q) ≃ (β : Γ ⟶ D) × (fst : Γ ⟶ P.functor.obj A) × (snd : Γ ⟶ E) ×' (h : fst ≫ P.proj A = snd ≫ P.p) ×' (β ≫ Q.p = pullback.lift fst snd h ≫ genPb.u₂ P A) where
  toFun f := ⟨f ≫ (pullback.fst Q.p (genPb.u₂ P A)), f ≫ (pullback.snd Q.p (genPb.u₂ P A)) ≫ genPb.fst P A, f ≫ (pullback.snd Q.p (genPb.u₂ P A)) ≫ genPb.snd P A, sorry⟩
  invFun := by
    rintro ⟨β,fst,snd,h,h'⟩
    exact pullback.lift β (pullback.lift fst snd h) h'
  left_inv f := by
    refine pullback.hom_ext ?_ ?_
    . simp
    . refine pullback.hom_ext ?_ ?_
      . simp[genPb.fst]
      . simp[genPb.snd]
  right_inv := by
    rintro ⟨β,fst,snd,h,h'⟩
    sorry

end UvPoly

variable {𝒞 : Type*} [SmallCategory 𝒞] [HasTerminal 𝒞]

instance : LCC (Psh 𝒞) :=
  @LCCC.mkOfOverCC _ _ _ ⟨CategoryOfElements.presheafOverCCC⟩

instance {X Y : Psh 𝒞} (f : X ⟶ Y) : CartesianExponentiable f where
  functor := LCC.pushforward f
  adj := LCC.adj _
