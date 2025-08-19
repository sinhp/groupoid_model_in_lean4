import Poly.UvPoly.Basic
import GroupoidModel.ForMathlib

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.UvPoly

variable {𝒞} [Category 𝒞] [HasTerminal 𝒞] [HasPullbacks 𝒞]

variable {E B : 𝒞} (P : UvPoly E B) (A : 𝒞)

def compDomEquiv {Γ E B D A : 𝒞} {P : UvPoly E B} {Q : UvPoly D A} :
    (Γ ⟶ compDom P Q) ≃
      (AB : Γ ⟶ P @ A) × (α : Γ ⟶ E) × (β : Γ ⟶ D) ×'
      (w : AB ≫ P.fstProj A = α ≫ P.p) ×'
      (β ≫ Q.p = pullback.lift AB α w ≫ (PartialProduct.fan P A).snd) :=
  calc
  _ ≃ (β : Γ ⟶ D) × (αB : Γ ⟶ pullback (PartialProduct.fan P A).fst P.p) ×'
      β ≫ Q.p = αB ≫ (PartialProduct.fan P A).snd :=
    pullbackHomEquiv
  _ ≃ (β : Γ ⟶ D) × (αB : (AB : Γ ⟶ P @ A) × (α : Γ ⟶ E) ×'
        AB ≫ P.fstProj A = α ≫ P.p) ×'
      β ≫ Q.p = pullback.lift αB.1 αB.2.1 αB.2.2 ≫ (PartialProduct.fan P A).snd :=
    Equiv.sigmaCongrRight (fun β => calc
      _ ≃ (αB : (AB : Γ ⟶ P @ A) × (α : Γ ⟶ E) ×' (AB ≫ P.fstProj A = α ≫ P.p)) ×'
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
    {Q : UvPoly D A} (AB : Γ ⟶ P @ A) (α : Γ ⟶ E)
    (β : Γ ⟶ D) (w : AB ≫ P.fstProj A = α ≫ P.p)
    (h : β ≫ Q.p = pullback.lift AB α w ≫ (PartialProduct.fan P A).snd) :
    compDomEquiv.symm ⟨AB, α, β, w, h⟩ ≫ (P.comp Q).p = AB := by
   simp [compDomEquiv, Equiv.psigmaCongrProp, Equiv.sigmaCongrRight_symm,
    Equiv.coe_fn_symm_mk, pullbackHomEquiv]

theorem ε_map {E B A E' B' A' : 𝒞} {P : UvPoly E B}
    {P' : UvPoly E' B'}
    (p : P.functor ⟶ P'.functor)
    (e : E ⟶ E')
    (b : B ⟶ B')
    (a : A ⟶ A')
    (ha : P.fstProj A ≫ b = p.app A ≫ P'.fstProj A)
    (hp : P.p ≫ b = e ≫ P'.p) :
    pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p (p.app A ≫ P'.functor.map a)
      e b (by simp [ha]) hp ≫ PartialProduct.ε P' A' =
    PartialProduct.ε P A ≫ prod.map e a := by
  simp [PartialProduct.ε]
  sorry

def compDomMap {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E')
    (d : D ⟶ D')
    (b : B ⟶ B')
    (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p)
    (hq : IsPullback Q.p d a Q'.p)
    (ha : P.fstProj A ≫ b = (P.cartesianNatTrans P' b e hp).app A ≫ P'.fstProj A) :
    compDom P Q ⟶ compDom P' Q' := by
  set p := P.cartesianNatTrans P' b e hp
  let ⟨fst, dependent, snd, h1, h2⟩ := compDomEquiv (𝟙 (P.compDom Q))
  have : (fst ≫ p.app A ≫ P'.functor.map a) ≫ P'.fstProj A' = (dependent ≫ e) ≫ P'.p := by
    simp [← ha]; rw [← Category.assoc, h1]; simp [hp.w]
  refine compDomEquiv.symm ⟨fst ≫ p.app A ≫ P'.functor.map a, dependent ≫ e, snd ≫ d, this, ?_⟩
  simp [← hq.w]; rw [← Category.assoc, h2]; simp
  simp [show pullback.lift (fst ≫ p.app A ≫ P'.functor.map a) (dependent ≫ e) this =
    pullback.lift fst dependent h1 ≫
      pullback.map _ _ _ _ (p.app A ≫ P'.functor.map a) _ _ (by simp [ha]) hp.w by
    apply pullback.hom_ext <;> simp]
  congr! 1
  rw [← Category.assoc, ← Category.assoc, ε_map (ha := ha)]
  simp

theorem compDomMap_isPullback {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E')
    (d : D ⟶ D')
    (b : B ⟶ B')
    (a : A ⟶ A')
    (p : P.functor ⟶ P'.functor)
    (hp : IsPullback P.p e b P'.p)
    (hq : IsPullback Q.p d a Q'.p)
    (ha : P.fstProj A ≫ b = (P.cartesianNatTrans P' b e hp).app A ≫ P'.fstProj A) :
    IsPullback
      (UvPoly.compDomMap e d b a hp hq ha)
      (P.comp Q).p (P'.comp Q').p
      (p.app A ≫ P'.functor.map a) := by
  set p := P.cartesianNatTrans P' b e hp
  apply IsPullback.paste_vert
    (h₂₁ := pullback.map _ _ _ _ (p.app A ≫ P'.functor.map a) _ _ (by simp [ha]) hp.w)
  · sorry
  · sorry

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

lemma mk_naturality_right (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    mk P X b x ≫ P.functor.map f = mk P Y b (x ≫ f) :=
  sorry

end Equiv

open TwoSquare

section

variable {F : C} (P : UvPoly E B) (Q : UvPoly F B) (ρ : E ⟶ F) (h : P.p = ρ ≫ Q.p)

lemma mk_comp_verticalNatTrans_app {Γ : C} (X : C) (b : Γ ⟶ B) (x : pullback b Q.p ⟶ X) :
    Equiv.mk Q X b x ≫ (verticalNatTrans P Q ρ h).app X = Equiv.mk P X b
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ρ)
    (by simp [pullback.condition, h]) ≫ x) :=
  sorry

end

open Over ExponentiableMorphism in
lemma cartesianNatTrans_fstProj {D F : C} (P : UvPoly E B) (Q : UvPoly F D)
    (δ : B ⟶ D) (φ : E ⟶ F) (pb : IsPullback P.p φ δ Q.p) (X : C) :
    (P.cartesianNatTrans Q δ φ pb).app X ≫ Q.fstProj X = P.fstProj X ≫ δ := by
  simp [cartesianNatTrans, fstProj]
  let SE := Over.star E
  let SF := Over.star F
  let pφ := Over.pullback φ
  let pδ := Over.pullback δ
  let Pp := pushforward P.p
  let Qp := pushforward Q.p
  let fB := Over.forget B
  let fD := Over.forget D
  let FF : SE ⟶ SF ⋙ pφ := (Over.starPullbackIsoStar φ).inv
  let GG : pφ ⋙ Pp ⟶ Qp ⋙ pδ :=
    (pushforwardPullbackIsoSquare pb.flip).inv
  let HH : pδ ⋙ fB ⟶ fD := pullbackForgetTwoSquare δ
  change (Pp.map (FF.app X)).left ≫ (GG.app (SF.obj X)).left ≫
      HH.app (Qp.obj (SF.obj X)) ≫ (Qp.obj (SF.obj X)).hom =
    (Pp.obj (SE.obj X)).hom ≫ δ
  sorry

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] [HasTerminal C] {E B : C}

instance preservesConnectedLimitsOfShape_of_hasLimitsOfShape {J : Type v₁} [SmallCategory J]
  [IsConnected J] [HasLimitsOfShape J C] (P : UvPoly E B) :
    PreservesLimitsOfShape J (P.functor) := by
  unfold UvPoly.functor
  infer_instance

instance preservesPullbacks (P : UvPoly E B)
    {Pb X Y Z : C} (fst : Pb ⟶ X) (snd : Pb ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h: IsPullback fst snd f g) :
    IsPullback (P.functor.map fst) (P.functor.map snd) (P.functor.map f) (P.functor.map g) :=
    P.functor.map_isPullback h


end CategoryTheory.UvPoly
