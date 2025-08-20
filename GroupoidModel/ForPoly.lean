import Poly.UvPoly.Basic
import GroupoidModel.ForMathlib

open CategoryTheory Limits

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

def snd' (pair : Γ ⟶ P @ X) {R f g} (H : IsPullback (P := R) f g (fst P X pair) P.p) : R ⟶ X :=
  H.isoPullback.hom ≫ snd P X pair

theorem snd_eq_snd' (pair : Γ ⟶ P @ X) :
    snd P X pair = snd' P X pair (.of_hasPullback ..) := by simp [snd']

def mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    Γ ⟶ P @ X :=
  P.lift (Γ := Γ) (X := X) b x

def mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X) : Γ ⟶ P @ X :=
  mk P X b (H.isoPullback.inv ≫ x)

theorem mk_eq_mk' (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    mk P X b x = mk' P X b (.of_hasPullback ..) x := by simp [mk']

@[simp]
lemma fst_mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    fst P X (mk P X b x) = b := by
  simp [fst, mk]

@[simp]
lemma fst_mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X) :
    fst P X (mk' P X b H x) = b := by
  simp [mk']

lemma fst_eq (pair : Γ ⟶ P @ X) : fst P X pair = pair ≫ P.fstProj X := by simp [fst]

@[simp]
lemma mk'_comp_fstProj (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X) :
    mk' P X b H x ≫ P.fstProj X = b := by
  simp [← fst_eq]

theorem fst_comp_left (pair : Γ ⟶ P @ X) {Δ} (f : Δ ⟶ Γ) :
    fst P X (f ≫ pair) = f ≫ fst P X pair := by simp [fst_eq]

theorem fst_comp_right (pair : Γ ⟶ P @ X) : fst P Y (pair ≫ P.functor.map f) = fst P X pair := by
  simp [fst_eq]

lemma snd'_eq (pair : Γ ⟶ P @ X) {R f g} (H : IsPullback (P := R) f g (fst P X pair) P.p) :
    snd' P X pair H = pullback.lift (f ≫ pair) g (by simpa using H.w) ≫ ε P X ≫ prod.snd := by
  simp [snd', snd]
  simp only [← Category.assoc]; congr! 2
  ext <;> simp
  · simp only [← Category.assoc]; congr! 1
    exact H.isoPullback_hom_fst
  · exact H.isoPullback_hom_snd

@[simp]
lemma snd'_mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X) :
    snd' P X (mk' P X b H x) (by rwa [fst_mk']) = x := by
  have : comparison (c := fan P X) (mk' P X b H x) ≫ _ =
      (pullback.congrHom (f₁ := mk' P X b H x ≫ _) ..).hom ≫ _ :=
    partialProd.lift_snd ⟨fan P X, isLimitFan P X⟩ b (H.isoPullback.inv ≫ x)
  have H' : IsPullback (P := R) f g (mk' P X b H x ≫ (fan P X).fst) P.p := by simpa
  convert congr(H'.isoPullback.hom ≫ $(this)) using 1
  · simp [partialProd.snd, partialProd.cone, snd'_eq]
    simp only [← Category.assoc]; congr! 2
    simp [comparison]; ext <;> simp
  · slice_rhs 1 0 => skip
    refine .symm <| .trans ?_ (Category.id_comp _); congr! 1
    rw [Iso.comp_inv_eq_id]; ext <;> simp

lemma snd_mk_heq (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    snd P X (mk P X b x) ≍ x := by
  have h := mk_eq_mk' P X b x
  set t := mk' P ..
  have : snd' P X t _ = x := snd'_mk' ..
  refine .trans ?_ this.heq
  rw [snd_eq_snd']; congr! 2 <;> simp

lemma snd_mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    snd P X (mk P X b x) = eqToHom (by simp) ≫ x := by
  apply eq_of_heq; rw [heq_eqToHom_comp_iff]; apply snd_mk_heq

theorem snd'_comp_right (pair : Γ ⟶ P @ X)
    {R f1 f2} (H : IsPullback (P := R) f1 f2 (fst P X pair) P.p) :
    snd' P Y (pair ≫ P.functor.map f) (by rwa [fst_comp_right]) =
    snd' P X pair H ≫ f := by
  simp [snd'_eq, ε]
  have := congr($((ExponentiableMorphism.ev P.p).naturality ((Over.star E).map f)).left ≫ prod.snd)
  dsimp at this; simp at this
  rw [← this]; clear this
  simp only [← Category.assoc]; congr! 2
  ext <;> simp
  · slice_rhs 2 3 => apply pullback.lift_fst
    slice_rhs 1 2 => apply pullback.lift_fst
    simp; rfl
  · slice_rhs 2 3 => apply pullback.lift_snd
    symm; apply pullback.lift_snd

theorem snd_comp_right (pair : Γ ⟶ P @ X) : snd P Y (pair ≫ P.functor.map f) =
    eqToHom congr(pullback $(fst_comp_right ..) _) ≫ snd P X pair ≫ f := by
  rw [snd_eq_snd', snd'_comp_right, snd', Category.assoc, ← eqToIso.hom]; congr! 2
  exact IsPullback.isoPullback_eq_eqToIso_left (fst_comp_right _ _ _ f pair) P.p

lemma hom_ext' {pair₁ pair₂ : Γ ⟶ P @ X}
    {R f g} (H : IsPullback (P := R) f g (fst P X pair₁) P.p)
    (h1 : fst P X pair₁ = fst P X pair₂)
    (h2 : snd' P X pair₁ H = snd' P X pair₂ (by rwa [h1] at H)) :
    pair₁ = pair₂ := by
  simp [fst_eq] at h1 H
  apply partialProd.hom_ext ⟨fan P X, isLimitFan P X⟩ h1
  refine (cancel_epi H.isoPullback.hom).1 ?_
  convert h2 using 1 <;> (
    simp [snd'_eq, comparison_pullback.map, partialProd.snd, partialProd.cone]
    simp only [← Category.assoc]; congr! 2
    ext <;> simp)
  · slice_lhs 2 3 => apply pullback.lift_fst
    slice_lhs 1 2 => apply H.isoPullback_hom_fst
    simp
  · slice_lhs 2 3 => apply pullback.lift_snd
    slice_lhs 1 2 => apply H.isoPullback_hom_snd
    simp

@[simp]
lemma eta' (pair : Γ ⟶ P @ X)
    {R f1 f2} (H : IsPullback (P := R) f1 f2 (fst P X pair) P.p) :
    mk' P X (fst P X pair) H (snd' P X pair H) = pair :=
  .symm <| hom_ext' P X H (by simp) (by simp)

@[simp]
lemma eta (pair : Γ ⟶ P @ X) :
    mk P X (fst P X pair) (snd P X pair) = pair := by
  simp [mk_eq_mk', snd_eq_snd']

lemma mk'_comp_right (b : Γ ⟶ B) {R f1 f2} (H : IsPullback (P := R) f1 f2 b P.p) (x : R ⟶ X) :
    mk' P X b H x ≫ P.functor.map f = mk' P Y b H (x ≫ f) := by
  refine .symm <| hom_ext' _ _ (by rwa [fst_mk']) (by simp [fst_comp_right]) ?_
  rw [snd'_comp_right (H := by rwa [fst_mk'])]; simp

lemma mk_comp_right (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    mk P X b x ≫ P.functor.map f = mk P Y b (x ≫ f) := by
  simp [mk_eq_mk', mk'_comp_right]

end Equiv

section

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

open ExponentiableMorphism in
theorem ε_map {E B A E' B' A' : 𝒞} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p)
    (ha : P.fstProj A ≫ b = (P.cartesianNatTrans P' b e hp).app A ≫ P'.fstProj A) :
    pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p
      ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a)
      e b (by simp [ha]) hp.w ≫ ε P' A' =
    ε P A ≫ prod.map e a := by
  ext
  · simp
    slice_rhs 1 2 => apply by simpa using ((ev P.p).app ((Over.star E).obj A)).w
    slice_lhs 2 3 => apply by simpa using ((ev P'.p).app ((Over.star E').obj A')).w
    apply pullback.lift_snd
  · have := ((Over.star E).whiskerLeft (ev P.p)).naturality a
    replace := congr($(this).left ≫ prod.snd)
    simp [ε, -Adjunction.counit_naturality] at this ⊢
    simp [cartesianNatTrans] at ha
    let Z := Functor.whiskerRight ((Over.star E).whiskerLeft (ev P.p)) (Over.forget E)
    have : Z.app A = sorry := sorry; simp [Z] at this
    have := (pushforwardPullbackIsoSquare hp.flip).inv
    have := (Over.starPullbackIsoStar e).inv
    have := (Over.pullbackForgetTwoSquare b).natTrans
    have := P.cartesianNatTrans P' b e hp; dsimp [functor] at this
    stop
    set p := P.cartesianNatTrans P' b e hp
    let z := P.functor.map a ≫ p.app A'
    let R := pullback (P.fstProj A) P.p
    let r1 : R ⟶ P @ A := pullback.fst (P.fstProj A) P.p
    let r2 : R ⟶ E := pullback.snd (P.fstProj A) P.p
    let R' := pullback (P'.fstProj A') P'.p
    have : Equiv.fst P' A' z = P.fstProj A ≫ b := by simp [Equiv.fst_eq, z, ha]
    have pb : IsPullback r1 (r2 ≫ e) (Equiv.fst P' A' z) P'.p := this ▸ .paste_vert (.of_hasPullback ..) hp
    have : Equiv.snd' P' A' z pb = ε P A ≫ prod.snd ≫ a := by
      rw [Equiv.snd'_eq]
      sorry
    have : Equiv.fst P A' (P.functor.map a) = P.fstProj A := by simp [Equiv.fst_eq]
    have pb : IsPullback (P := R) r1 r2 (Equiv.fst P A' (P.functor.map a)) P.p := by rw [this]; exact .of_hasPullback ..
    have := Equiv.snd'_eq P A' (P.functor.map a) pb
    have : ε P A ≫ ?_ = ?_ ≫ ε P' A' := sorry
    unfold ε at this
    have := (ev P.p).app ((Over.star E).obj A)
    dsimp at this
    have := pushforwardUncurry <|
      (pushforward P.p).map ((Over.star E).map a)
    have := ((pushforward P.p).obj
          ((Over.star E).obj A))
    have' := pushforwardUncurry (f := P.p)
      (𝟙
        ((pushforward P.p).obj
          ((Over.star E).obj A)))
    simp [PartialProduct.ε]
    sorry

def compDomMap {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E') (d : D ⟶ D') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) (hq : IsPullback Q.p d a Q'.p)
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
  rw [← Category.assoc, ← Category.assoc, ε_map (hp := hp) (ha := ha)]
  simp

theorem compDomMap_isPullback {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E') (d : D ⟶ D') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) (hq : IsPullback Q.p d a Q'.p)
    (ha : P.fstProj A ≫ b = (P.cartesianNatTrans P' b e hp).app A ≫ P'.fstProj A) :
    IsPullback
      (UvPoly.compDomMap e d b a hp hq ha)
      (P.comp Q).p (P'.comp Q').p
      ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a) := by
  set p := P.cartesianNatTrans P' b e hp
  apply IsPullback.paste_vert
    (h₂₁ := pullback.map _ _ _ _ (p.app A ≫ P'.functor.map a) _ _ (by simp [ha]) hp.w)
  · sorry
  · sorry

end

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
