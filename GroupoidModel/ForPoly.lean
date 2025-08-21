import Poly.UvPoly.Basic
import GroupoidModel.ForMathlib

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.UvPoly
open Limits PartialProduct

universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasTerminal C] {E B : C}

open ExponentiableMorphism in
theorem ev_naturality {E B E' B' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B')
    (hp : IsPullback P.p e b P'.p) :
    let pfwd := pushforward P.p
    let p'fwd := pushforward P'.p
    let pbk := Over.pullback P.p
    let ebk := Over.pullback e
    let bbk := Over.pullback b
    let p'bk := Over.pullback P'.p
    have β : ebk ⋙ pfwd ⟶ p'fwd ⋙ bbk := (pushforwardPullbackIsoSquare hp.flip).inv
    have bb : bbk ⋙ pbk ≅ p'bk ⋙ ebk :=
      (Over.pullbackComp P.p b).symm.trans (eqToIso congr(Over.pullback $(hp.w)))
        |>.trans (Over.pullbackComp e P'.p)
    (Functor.whiskerRight β pbk ≫
      Functor.whiskerLeft p'fwd bb.hom ≫
      Functor.whiskerRight (ev P'.p) ebk : ebk ⋙ pfwd ⋙ pbk ⟶ ebk) =
    Functor.whiskerLeft ebk (ev P.p) := by
  intro pfwd p'fwd pbk ebk bbk p'bk β bb
  sorry

theorem associator_eq_id {C D E E'} [Category C] [Category D] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : Functor.associator F G H = Iso.refl (F ⋙ G ⋙ H) := rfl

open Functor in
theorem whiskerRight_left' {C D E B} [Category C] [Category D] [Category E] [Category B]
    (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K = whiskerLeft F (whiskerRight α K) := by
  aesop_cat

open Functor in
theorem id_whiskerLeft' {C D} [Category C] [Category D] {G H : C ⥤ D} (α : G ⟶ H) :
    whiskerLeft (𝟭 C) α = α := by
  aesop_cat

open Functor in
theorem whiskerLeft_twice' {C D E B} [Category C] [Category D] [Category E] [Category B]
    (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) = whiskerLeft (F ⋙ G) α := by
  aesop_cat

open Functor in
theorem whiskerRight_twice' {C D E B} [Category C] [Category D] [Category E] [Category B]
    {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G = whiskerRight α (F ⋙ G) := by
  aesop_cat

open Over ExponentiableMorphism Functor in
@[simp]
lemma cartesianNatTrans_fstProj {B' E' : C} (P : UvPoly E B) (P' : UvPoly E' B')
    (b : B ⟶ B') (e : E ⟶ E') (pb : IsPullback P.p e b P'.p) (X : C) :
    (P.cartesianNatTrans P' b e pb).app X ≫ P'.fstProj X = P.fstProj X ≫ b := by
  let m := whiskerRight (Over.starPullbackIsoStar e).inv (pushforward P.p) ≫
    whiskerLeft (Over.star E') (pushforwardPullbackIsoSquare pb.flip).inv
  simp [cartesianNatTrans, pullbackForgetTwoSquare, Adjunction.id, Over.mapForget]
  rw [← Category.assoc]
  change (m.app X).left ≫ pullback.fst (P'.fstProj X) b ≫ P'.fstProj X = P.fstProj X ≫ b
  rw [pullback.condition, ← Category.assoc]; congr 1
  simpa using Over.w (m.app X)

open ExponentiableMorphism Functor in
set_option maxHeartbeats 300000 in
theorem ε_map_snd' {E B E' B' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (A : C) (hp : IsPullback P.p e b P'.p) :
    pullback.map (P.fstProj A) P.p (P'.fstProj A) P'.p
      ((P.cartesianNatTrans P' b e hp).app A) e b (by simp) hp.w
      ≫ ε P' A ≫ prod.snd =
    ε P A ≫ prod.snd := by
  have := ev_naturality e b hp; revert this; lift_lets
  let sE := Over.star E
  let sE' := Over.star E'
  let UE := Over.forget E
  let UE' := Over.forget E'
  let UB := Over.forget B
  let UB' := Over.forget B'
  intros pfwd p'fwd pbk ebk bbk p'bk β bb eq
  let α : sE ⟶ sE' ⋙ ebk := (Over.starPullbackIsoStar e).inv
  let eγ : ebk ⋙ UE ⟶ UE' := Over.pullbackForgetTriangle e
  let bγ : bbk ⋙ UB ⟶ UB' := Over.pullbackForgetTriangle b
  let pγ : pbk ⋙ UE ⟶ UB := Over.pullbackForgetTriangle P.p
  let p'γ : p'bk ⋙ UE' ⟶ UB' := Over.pullbackForgetTriangle P'.p
  let y1 := whiskerRight α pfwd ≫ whiskerLeft sE' β
  set p : sE ⋙ pfwd ⋙ UB ⟶ sE' ⋙ p'fwd ⋙ UB' :=
    P.cartesianNatTrans P' b e hp
  have p_eq : whiskerRight y1 UB ≫ whiskerLeft (sE' ⋙ p'fwd) bγ = p := by
    simp [y1, associator_eq_id, bγ, p, cartesianNatTrans, TwoSquare.vComp, TwoSquare.mk,
      TwoSquare.natTrans]
    conv_lhs => apply Category.id_comp
    slice_rhs 2 6 => apply Category.id_comp
    slice_rhs 4 5 => apply Category.comp_id
    slice_rhs 2 2 => rw [← whiskerRight_left']
    slice_rhs 3 3 => apply whiskerLeft_id
    slice_rhs 3 4 => apply Category.id_comp
    rfl
  let r :=
    whiskerRight (
      whiskerRight y1 pbk ≫
      whiskerLeft (sE' ⋙ p'fwd) bb.hom) UE ≫
    whiskerLeft (sE' ⋙ p'fwd ⋙ p'bk) eγ
  have : r.app A = pullback.map (P.fstProj A) P.p (P'.fstProj A) P'.p
      (p.app A) e b (by simp [p]) hp.w := by
    simp [r, UE, bb, eγ, sE', UE', pbk, p'bk, Over.pullbackComp, Over.pullbackForgetTriangle,
      Over.pullbackForgetTwoSquare, Over.pullback, Adjunction.id, Over.mapForget,
      TwoSquare.natTrans]
    slice_lhs 5 5 => exact (pullback_map_eq_eqToHom rfl hp.w).symm
    slice_lhs 10 10 => enter [2,2,2,2]; apply Category.comp_id
    ext <;> simp
    · conv_rhs => apply pullback.lift_fst
      slice_lhs 1 2 => apply pullback.lift_fst
      simp [← p_eq, UB, bγ, p'fwd, pfwd, Over.pullbackForgetTriangle,
        Over.pullbackForgetTwoSquare, Adjunction.id, TwoSquare.natTrans, Over.mapForget]
      congr 2
      symm; apply Category.id_comp
    · slice_lhs 1 2 => apply pullback.lift_snd
      symm; apply pullback.lift_snd
  let Z : sE ⋙ pfwd ⋙ pbk ⋙ UE ⟶ sE ⋙ UE :=
    whiskerRight (sE.whiskerLeft (ev P.p)) UE
  let Z' : sE' ⋙ p'fwd ⋙ p'bk ⋙ UE' ⟶ sE' ⋙ UE' :=
    whiskerRight (sE'.whiskerLeft (ev P'.p)) UE'
  rw [← this, ← show Z.app A = ε P A by rfl, ← show Z'.app A = ε P' A by rfl]
  have : Z ≫ whiskerRight α UE ≫ whiskerLeft sE' eγ = r ≫ Z' := by
    simp [Z, Z', r, y1, associator_eq_id]
    slice_rhs 1 1 => apply whiskerRight_id
    slice_rhs 1 2 => apply Category.id_comp
    slice_rhs 1 2 => apply Category.id_comp
    slice_rhs 1 2 => apply Category.comp_id
    slice_lhs 1 1 => apply whiskerRight_left'
    slice_lhs 1 2 => apply whiskerLeft_comp_whiskerRight (H := pfwd ⋙ pbk ⋙ UE)
    slice_lhs 2 2 =>
      conv => apply (whiskerLeft_twice' ..).symm
      arg 2; apply (whiskerRight_left' ..).symm
    simp [← eq, associator_eq_id]; congr! 1
    slice_lhs 1 1 => apply whiskerLeft_id
    slice_lhs 1 2 => apply Category.id_comp
    slice_rhs 1 1 => apply whiskerRight_left'
    slice_rhs 2 2 =>
      conv => arg 1; apply (whiskerLeft_twice' ..).symm
      apply whiskerRight_left'
    slice_lhs 3 3 => apply whiskerLeft_id
    slice_lhs 3 4 => apply Category.id_comp
    slice_rhs 3 3 => apply (whiskerLeft_twice' sE' (p'fwd ⋙ p'bk) _).symm
    slice_rhs 3 4 =>
      conv => arg 2; apply whiskerRight_left'
      rw [← whiskerLeft_comp, whiskerLeft_comp_whiskerRight, whiskerLeft_comp, id_whiskerLeft']
  have := congr($(this).app A)
  simp [UE, eγ, Over.pullbackForgetTriangle, Over.pullbackForgetTwoSquare,
    Adjunction.id, TwoSquare.natTrans, Over.mapForget] at this
  slice_lhs 1 2 => rw [← this]
  slice_lhs 2 3 => apply Category.comp_id
  simp [α, Over.starPullbackIsoStar]
  slice_lhs 5 6 => apply pullback.lift_fst
  simp [Over.mapForget]

open ExponentiableMorphism in
theorem ε_map_snd {E B A E' B' A' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) :
    pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p
      ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a)
      e b (by simp) hp.w ≫ ε P' A' ≫ prod.snd =
    (ε P A ≫ prod.snd) ≫ a := by
  have := ((Over.star E').whiskerLeft (ev P'.p)).naturality a
  replace := congr($(this).left ≫ prod.snd)
  simp [-Adjunction.counit_naturality] at this
  simp [← ε.eq_def] at this
  have H := congr($(ε_map_snd' e b A hp) ≫ a)
  conv at H => lhs; slice 2 4; apply this.symm
  simp at H ⊢; rw [← H]
  simp only [← Category.assoc]; congr 2; ext <;> simp
  · slice_rhs 2 3 => apply pullback.lift_fst
    slice_rhs 1 2 => apply pullback.lift_fst
    simp; rfl
  · slice_rhs 2 3 => apply pullback.lift_snd
    slice_rhs 1 2 => apply pullback.lift_snd

open ExponentiableMorphism in
theorem ε_map {E B A E' B' A' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) :
    pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p
      ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a) e b (by simp) hp.w ≫ ε P' A' =
    ε P A ≫ prod.map e a := by
  ext
  · simp
    slice_rhs 1 2 => apply by simpa using ((ev P.p).app ((Over.star E).obj A)).w
    slice_lhs 2 3 => apply by simpa using ((ev P'.p).app ((Over.star E').obj A')).w
    apply pullback.lift_snd
  · simpa using ε_map_snd e b a hp

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

lemma snd'_eq_snd' (pair : Γ ⟶ P @ X) {R f g} (H : IsPullback (P := R) f g (fst P X pair) P.p)
    {R' f' g'} (H' : IsPullback (P := R') f' g' (fst P X pair) P.p) :
    snd' P X pair H = (H.isoIsPullback _ _ H').hom ≫ snd' P X pair H' := by
  simp [snd'_eq, ← Category.assoc]
  congr 2
  ext <;> simp

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

theorem snd'_comp_left (pair : Γ ⟶ P @ X)
    {R f g} (H : IsPullback (P := R) f g (fst P X pair) P.p)
    {Δ} (σ : Δ ⟶ Γ)
    {R' f' g'} (H' : IsPullback (P := R') f' g' (σ ≫ fst P X pair) P.p) :
    snd' P X (σ ≫ pair) (by convert H'; rw [fst_comp_left]) =
    H.lift (f' ≫ σ) g' (by simp [H'.w]) ≫ snd' P X pair H := by
  simp only [snd'_eq, ← Category.assoc]
  congr 2
  ext
  · simp
  · simp

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

theorem mk'_eq_mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X)
    {R' f' g'} (H' : IsPullback (P := R') f' g' b P.p) :
    mk' P X b H x = mk' P X b (R := R') H' ((IsPullback.isoIsPullback _ _ H H').inv ≫ x) := by
  apply hom_ext' P X (R := R) (f := f) (g := g) (by convert H; simp)
  · rw [snd'_eq_snd' P X (mk' P X b H' ((IsPullback.isoIsPullback _ _ H H').inv ≫ x))
      (by convert H; simp) (by convert H'; simp)]
    simp [snd'_mk']
  · simp

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

theorem mk'_comp_left {Δ}
    (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X) (σ : Δ ⟶ Γ)
    {R' f' g'} (H' : IsPullback (P := R') f' g' (σ ≫ b) P.p) :
    σ ≫ UvPoly.Equiv.mk' P X b H x =
    UvPoly.Equiv.mk' P X (σ  ≫ b) H'
    (H.lift (f' ≫ σ) g' (by simp [H'.w]) ≫ x) := by
  apply hom_ext' P (R := R') (f := f') (g := g') (H := by convert H'; simp [fst_eq])
  · rw [snd'_comp_left (H := by convert H; rw [fst_mk']) (H' := by convert H'; rw [fst_mk'])]
    simp
  · simp [fst_comp_left]

theorem mk_comp_left {Δ} (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) (σ: Δ ⟶ Γ) :
    σ ≫ UvPoly.Equiv.mk P X b x =
    UvPoly.Equiv.mk P X (σ  ≫ b)
    (pullback.map _ _ _ _ σ (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ x) := by
  simp only [mk_eq_mk']
  rw [mk'_comp_left (H := IsPullback.of_hasPullback _ _) (H' := IsPullback.of_hasPullback _ _)]
  congr 2; ext <;> simp

lemma mk'_comp_cartesianNatTrans_app {E' B' Γ X : C} {P' : UvPoly E' B'}
    (y : Γ ⟶ B) (R f g) (H : IsPullback (P := R) f g y P.p)
    (x : R ⟶ X) (e : E ⟶ E') (b : B ⟶ B')
    (hp : IsPullback P.p e b P'.p) :
    Equiv.mk' P X y H x ≫ (P.cartesianNatTrans P' b e hp).app X =
    Equiv.mk' P' X (y ≫ b) (H.paste_vert hp) x := by
  have : fst P' X (Equiv.mk' P X y H x ≫ (P.cartesianNatTrans P' b e hp).app X) = y ≫ b := by
    rw [fst_eq, Category.assoc, cartesianNatTrans_fstProj, ← Category.assoc, mk'_comp_fstProj]
  refine hom_ext' _ _ (this ▸ H.paste_vert hp) (by simpa) ?_
  simp; rw [snd'_eq]
  have := snd'_mk' P X y H x
  rw [snd'_eq, ← ε_map_snd' _ _ X hp] at this
  refine .trans ?_ this
  simp only [← Category.assoc]; congr 2; ext <;> simp

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

-- -- TODO: rename
-- abbrev ev1 : pullback (P.fstProj A) P.p ⟶ A := ε P A ≫ prod.snd

-- theorem ev1_map {E B A E' B' A' : 𝒞} {P : UvPoly E B} {P' : UvPoly E' B'}
--     (e : E ⟶ E') (b : B ⟶ B') (a : A ⟶ A')
--     (hp : IsPullback P.p e b P'.p)
--     (ha : P.fstProj A ≫ b = (P.cartesianNatTrans P' b e hp).app A ≫ P'.fstProj A) :
--     pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p
--       ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a)
--       e b (by simp [ha]) hp.w ≫ ev1 P' A' =
--     ev1 P A ≫ a := by
--   set p := P.cartesianNatTrans P' b e hp
--   let z := P.functor.map a ≫ p.app A'
--   have isPullbackUpper : IsPullback (pullback.fst (P.fstProj A) P.p)
--       (pullback.snd (P.fstProj A) P.p ≫ e) (Equiv.fst P' A' z) P'.p := by
--     simp [Equiv.fst_eq, z, p.naturality, ← ha]
--     exact .paste_vert (.of_hasPullback (P.fstProj A) P.p) hp
--   have functor_map_eq_mk : P.functor.map a = Equiv.mk P A' (fstProj P A) (ev1 P A ≫ a) := by
--     rw [← Equiv.mk_comp_right]
--     refine .symm <| .trans ?_ (Category.id_comp _); congr 1
--     have pb : IsPullback (pullback.fst (P.fstProj A) P.p)
--         (pullback.snd (P.fstProj A) P.p) (Equiv.fst P A (𝟙 _)) P.p := by
--       simp [Equiv.fst_eq]; exact .of_hasPullback ..
--     rw [Equiv.mk_eq_mk']
--     convert Equiv.eta' P A (𝟙 _) pb
--     · simp [Equiv.fst_eq]
--     · simp [ev1, Equiv.snd'_eq]
--   calc pullback.map _ _ _ _ (p.app A ≫ P'.functor.map a) e b (by simp [ha]) hp.w ≫ ev1 P' A'
--   _ = UvPoly.Equiv.snd' P' A' z isPullbackUpper := by
--     simp only [Equiv.snd'_eq, ev1, ← Category.assoc]
--     congr 2
--     ext <;> simp [z]
--   _ = _ := by
--     dsimp [z]
--     rw! [functor_map_eq_mk, Equiv.mk_eq_mk', Equiv.mk'_comp_cartesianNatTrans_app, Equiv.snd'_mk']

def compDomMap {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E') (d : D ⟶ D') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) (hq : IsPullback Q.p d a Q'.p) :
    compDom P Q ⟶ compDom P' Q' := by
  set p := P.cartesianNatTrans P' b e hp
  let pa := p.app A ≫ P'.functor.map a
  let r := pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p pa e b (by simp [pa, p]) hp.w
  refine pullback.map _ _ _ _ d r a hq.w (ε_map_snd _ _ _ hp).symm

theorem compDomMap_isPullback {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E') (d : D ⟶ D') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) (hq : IsPullback Q.p d a Q'.p) :
    IsPullback
      (UvPoly.compDomMap e d b a hp hq)
      (P.comp Q).p (P'.comp Q').p
      ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a) := by
  set p := P.cartesianNatTrans P' b e hp
  apply IsPullback.paste_vert
    (h₂₁ := pullback.map _ _ _ _ (p.app A ≫ P'.functor.map a) _ _ (by simp [p]) hp.w)
  · refine hq.flip.back_face_of_comm_cube _ _ _ _ _ _ _ _ _ _ _ _ (by simp [compDomMap]) ?_ ?_
      (.of_hasPullback ..) (.of_hasPullback ..)
    · exact ⟨ε_map_snd _ _ a hp⟩
    · constructor; simp [compDomMap]; ext <;> simp [p]
  · exact hp.flip.back_face_of_comm_cube _ _ _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [p]) (by simp) (.flip (.of_hasPullback ..)) (.flip (.of_hasPullback ..))

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
