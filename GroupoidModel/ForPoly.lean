import Poly.UvPoly.Basic
import GroupoidModel.ForMathlib

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.UvPoly
open Limits PartialProduct

universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C]

theorem η_naturality {E B E' B' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (hp : CommSq P.p e b P'.p) :
    Functor.whiskerLeft (Over.pullback P.p) (Over.mapPullbackAdj e).unit ≫
    Functor.whiskerRight (Over.pullbackMapTwoSquare (sq := hp.flip)) (Over.pullback e) ≫
    Functor.whiskerLeft (Over.map b)
      ((Over.pullbackComp P.p b).symm.trans (eqToIso congr(Over.pullback $(hp.w)))
        |>.trans (Over.pullbackComp e P'.p)).inv =
    Functor.whiskerRight (Over.mapPullbackAdj b).unit (Over.pullback P.p) := by
  ext X
  simp [← pullback_map_eq_eqToHom rfl hp.w.symm, Over.pullbackComp]
  ext <;> simp [pullback.condition]

open ExponentiableMorphism in
theorem pushforwardPullbackIsoSquare_eq {C} [Category C] [HasPullbacks C] {X Y Z W : C}
    {h : X ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ W} {k : Y ⟶ W} (pb : IsPullback h f g k)
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    haveI := pullbackMapTwoSquare_of_isPullback_isIso pb
    pushforwardPullbackIsoSquare pb =
    conjugateIsoEquiv
      ((Over.mapPullbackAdj k).comp (adj g))
      ((adj f).comp (Over.mapPullbackAdj h))
      (asIso (Over.pullbackMapTwoSquare h f g k pb.toCommSq)) := by
  simp [pushforwardPullbackIsoSquare, Over.pushforwardPullbackTwoSquare]
  ext1; simp

def Over.pullbackIsoOfEq {X Y : C} {f g : X ⟶ Y} (h : f = g) : Over.pullback f ≅ Over.pullback g :=
  eqToIso congr(Over.pullback $h)

@[simp]
theorem Over.pullbackIsoOfEq_symm {X Y : C} {f g : X ⟶ Y} (h : f = g) :
    (Over.pullbackIsoOfEq h).symm = Over.pullbackIsoOfEq h.symm := by
  simp [Over.pullbackIsoOfEq]; rfl

@[simp]
theorem Over.pullbackIsoOfEq_hom_app_left {X Y : C} {Z} {f g : X ⟶ Y} (h : f = g) :
    ((Over.pullbackIsoOfEq h).hom.app Z).left =
    pullback.map Z.hom f Z.hom g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]) := by
  simp [pullback_map_eq_eqToHom rfl h, Over.pullbackIsoOfEq]

@[simp]
theorem Over.pullbackIsoOfEq_inv_app_left {X Y : C} {Z} {f g : X ⟶ Y} (h : f = g) :
    ((Over.pullbackIsoOfEq h).inv.app Z).left =
    pullback.map Z.hom g Z.hom f (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]) := by
  rw [← Iso.symm_hom]; simp

open ExponentiableMorphism Functor in
theorem ev_naturality {E B E' B' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (hp : CommSq P.p e b P'.p) :
    let pfwd := pushforward P.p
    let p'fwd := pushforward P'.p
    let pbk := Over.pullback P.p
    let ebk := Over.pullback e
    let bbk := Over.pullback b
    let p'bk := Over.pullback P'.p
    have β : p'fwd ⋙ bbk ⟶ ebk ⋙ pfwd := Over.pushforwardPullbackTwoSquare (sq := hp.flip)
    have bb : bbk ⋙ pbk ≅ p'bk ⋙ ebk :=
      (Over.pullbackComp P.p b).symm.trans (Over.pullbackIsoOfEq hp.w)
        |>.trans (Over.pullbackComp e P'.p)
    whiskerLeft p'fwd bb.hom ≫ whiskerRight (ev P'.p) ebk =
    whiskerRight β pbk ≫ whiskerLeft ebk (ev P.p) := by
  intro pfwd p'fwd pbk ebk bbk p'bk β bb
  let bmap := Over.map b
  let emap := Over.map e
  let α : pbk ⋙ emap ⟶ bmap ⋙ p'bk := Over.pullbackMapTwoSquare (sq := hp.flip)
  have :
    whiskerLeft pbk (Over.mapPullbackAdj e).unit ≫
    whiskerRight α ebk ≫ whiskerLeft bmap bb.inv =
    whiskerRight (Over.mapPullbackAdj b).unit pbk :=
    η_naturality e b hp
  rw [← isoWhiskerLeft_inv, ← Category.assoc, Iso.comp_inv_eq] at this
  simp [β, Over.pushforwardPullbackTwoSquare, ev]
  rw [show Over.pullbackMapTwoSquare .. = α by rfl]
  generalize Over.mapPullbackAdj e = adje, Over.mapPullbackAdj b = adjb at *
  ext X : 2; simp
  have := congr(
    $(whiskerLeft_comp_whiskerRight (H := pfwd ⋙ pbk)
      (whiskerLeft p'fwd (
          whiskerLeft bbk (whiskerLeft pbk adje.unit ≫ whiskerRight α ebk) ≫
          whiskerRight adjb.counit (p'bk ⋙ ebk)) ≫
        whiskerRight (adj P'.p).counit ebk)
      (adj P.p).counit).app X)
  simp [-Adjunction.counit_naturality] at this
  rw [Category.id_comp, Category.id_comp] at this
  rw [← this]; clear this
  rw [reassoc_of% (adj P.p).left_triangle_components]
  replace := congr(($this).app ((p'fwd ⋙ bbk).obj X)); dsimp at this
  rw [reassoc_of% this]; clear this
  have := adjb.counit
  have := congr($(whiskerLeft_comp_whiskerRight adjb.counit bb.hom).app (p'fwd.obj X))
  dsimp at this; rw [reassoc_of% this]; clear this
  rw [← map_comp_assoc, adjb.right_triangle_components, map_id]; simp

theorem associator_eq_id {C D E E'} [Category C] [Category D] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : Functor.associator F G H = Iso.refl (F ⋙ G ⋙ H) := rfl

open Functor in
theorem whiskerRight_left' {C D E B} [Category C] [Category D] [Category E] [Category B]
    (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K = whiskerLeft F (whiskerRight α K) := rfl

open Functor in
theorem id_whiskerRight' {C D} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G) :
    whiskerRight α (𝟭 _) = α := rfl

open Functor in
theorem id_whiskerLeft' {C D} [Category C] [Category D] {G H : C ⥤ D} (α : G ⟶ H) :
    whiskerLeft (𝟭 C) α = α := rfl

open Functor in
theorem whiskerLeft_twice' {C D E B} [Category C] [Category D] [Category E] [Category B]
    (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) = whiskerLeft (F ⋙ G) α := rfl

open Functor in
theorem whiskerRight_twice' {C D E B} [Category C] [Category D] [Category E] [Category B]
    {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G = whiskerRight α (F ⋙ G) := rfl

variable [HasTerminal C]

open Over ExponentiableMorphism Functor in
@[simp]
lemma cartesianNatTrans_fstProj {E B E' B' : C} (P : UvPoly E B) (P' : UvPoly E' B')
    (e : E ⟶ E') (b : B ⟶ B') (pb : IsPullback P.p e b P'.p) (X : C) :
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
theorem fan_snd_map' {E B E' B' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (A : C) (hp : IsPullback P.p e b P'.p) :
    pullback.map (P.fstProj A) P.p (P'.fstProj A) P'.p
      ((P.cartesianNatTrans P' b e hp).app A) e b (by simp) hp.w
      ≫ (fan P' A).snd =
    (fan P A).snd := by
  let sE  := Over.star E;  let UE  := Over.forget E;  let UB  := Over.forget B
  let sE' := Over.star E'; let UE' := Over.forget E'; let UB' := Over.forget B'
  have eq := ev_naturality e b hp.toCommSq
  extract_lets pfwd p'fwd pbk ebk bbk p'bk β' bb at eq
  let α : sE' ⋙ ebk ≅ sE := Over.starPullbackIsoStar e
  let β : p'fwd ⋙ bbk ≅ ebk ⋙ pfwd := pushforwardPullbackIsoSquare hp.flip
  rw [show β' = β.hom by rfl, ← isoWhiskerRight_hom, ← Iso.inv_comp_eq] at eq
  let eγ : ebk ⋙ UE ⟶ UE' := Over.pullbackForgetTriangle e
  let bγ : bbk ⋙ UB ⟶ UB' := Over.pullbackForgetTriangle b
  let pγ : pbk ⋙ UE ⟶ UB := Over.pullbackForgetTriangle P.p
  let p'γ : p'bk ⋙ UE' ⟶ UB' := Over.pullbackForgetTriangle P'.p
  let y1 := whiskerRight α.inv pfwd ≫ whiskerLeft sE' β.inv
  set p : sE ⋙ pfwd ⋙ UB ⟶ sE' ⋙ p'fwd ⋙ UB' := P.cartesianNatTrans P' b e hp
  have p_eq : whiskerRight y1 UB ≫ whiskerLeft (sE' ⋙ p'fwd) bγ = p := by
    simp [y1, associator_eq_id, bγ, p, cartesianNatTrans, TwoSquare.vComp, TwoSquare.mk,
      TwoSquare.natTrans]
    rw! [Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]; rfl
  let r := whiskerRight (whiskerRight y1 pbk ≫ whiskerLeft (sE' ⋙ p'fwd) bb.hom) UE ≫
    whiskerLeft (sE' ⋙ p'fwd ⋙ p'bk) eγ
  have : r.app A = pullback.map (P.fstProj A) P.p (P'.fstProj A) P'.p
      (p.app A) e b (by simp [p]) hp.w := by
    simp [r, UE, bb, eγ, sE', UE', pbk, p'bk, Over.pullbackComp, Over.pullbackForgetTriangle,
      Over.pullbackForgetTwoSquare, Over.pullback, Adjunction.id, Over.mapForget,
      TwoSquare.natTrans]
    slice_lhs 9 10 => apply Category.comp_id
    ext <;> simp
    · rw! [pullback.lift_fst, pullback.lift_fst_assoc]
      simp [← p_eq, UB, bγ, p'fwd, pfwd, Over.pullbackForgetTriangle,
        Over.pullbackForgetTwoSquare, Adjunction.id, TwoSquare.natTrans, Over.mapForget]
      rw! [Category.id_comp]; rfl
    · rw! [pullback.lift_snd, pullback.lift_snd_assoc]; rfl
  let Z  : sE  ⋙ pfwd  ⋙ pbk  ⋙ UE  ⟶ sE  ⋙ UE  := whiskerRight (sE.whiskerLeft  (ev P.p))  UE
  let Z' : sE' ⋙ p'fwd ⋙ p'bk ⋙ UE' ⟶ sE' ⋙ UE' := whiskerRight (sE'.whiskerLeft (ev P'.p)) UE'
  dsimp only [fan]
  rw [← this, ← show Z.app A = ε P A by rfl, ← show Z'.app A = ε P' A by rfl]
  have : Z ≫ whiskerRight α.inv UE ≫ whiskerLeft sE' eγ = r ≫ Z' := by
    simp [Z, Z', r, y1, associator_eq_id]
    rw! [Category.id_comp, Category.id_comp, Category.id_comp, whiskerRight_left',
      whiskerLeft_comp_whiskerRight_assoc (H := pfwd ⋙ pbk ⋙ UE),
      ← whiskerLeft_twice', ← whiskerRight_left']
    simp [← eq, associator_eq_id]; congr! 1
    rw! [Category.id_comp, Category.id_comp, whiskerRight_left', ← whiskerLeft_twice',
      whiskerRight_left', ← whiskerLeft_twice' sE' (p'fwd ⋙ p'bk), whiskerRight_left' _ (ev P'.p)]
    symm; rw [← whiskerLeft_comp, whiskerLeft_comp_whiskerRight]; rfl
  have := congr($(this).app A)
  simp [UE, eγ, Over.pullbackForgetTriangle, Over.pullbackForgetTwoSquare,
    Adjunction.id, TwoSquare.natTrans, Over.mapForget] at this
  rw! [← reassoc_of% this, Category.id_comp]
  simp [α, Over.starPullbackIsoStar]
  rw! [pullback.lift_fst_assoc]
  simp [Over.mapForget]

open ExponentiableMorphism in
theorem fan_snd_map {E B A E' B' A' : C} {P : UvPoly E B} {P' : UvPoly E' B'}
    (e : E ⟶ E') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) :
    pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p
      ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a)
      e b (by simp) hp.w ≫ (fan P' A').snd =
    (fan P A).snd ≫ a := by
  have := ((Over.star E').whiskerLeft (ev P'.p)).naturality a
  replace := congr($(this).left ≫ prod.snd)
  simp [-Adjunction.counit_naturality] at this
  simp only [← ε.eq_def] at this
  rw [← fan_snd, ← Category.assoc, ← fan_snd] at this
  have H := congr($(fan_snd_map' e b A hp) ≫ a)
  conv at H => lhs; slice 2 4; apply this.symm
  simp at H ⊢; rw [← H]
  simp only [← Category.assoc]; congr 2; ext <;> simp
  · rw! [pullback.lift_fst, pullback.lift_fst_assoc]; simp; rfl
  · rw! [pullback.lift_snd, pullback.lift_snd]

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
  · simpa [fan_snd] using fan_snd_map e b a hp

namespace Equiv

variable {E B : C} (P : UvPoly E B) {Γ : C} (X Y : C) (f : X ⟶ Y)

def fst (pair : Γ ⟶ P @ X) :
    Γ ⟶ B :=
  fan P X |>.extend pair |>.fst

lemma fst_eq (pair : Γ ⟶ P @ X) : fst P X pair = pair ≫ P.fstProj X := by simp [fst]

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

@[simp]
lemma mk'_comp_fstProj (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X) :
    mk' P X b H x ≫ P.fstProj X = b := by
  simp [← fst_eq]

theorem fst_comp_left (pair : Γ ⟶ P @ X) {Δ} (f : Δ ⟶ Γ) :
    fst P X (f ≫ pair) = f ≫ fst P X pair := by simp [fst_eq]

theorem fst_comp_right (pair : Γ ⟶ P @ X) : fst P Y (pair ≫ P.functor.map f) = fst P X pair := by
  simp [fst_eq]

lemma snd'_eq (pair : Γ ⟶ P @ X) {R f g} (H : IsPullback (P := R) f g (fst P X pair) P.p) :
    snd' P X pair H = pullback.lift (f ≫ pair) g (by simpa using H.w) ≫ (fan P X).snd := by
  simp [snd', snd]
  simp only [← Category.assoc]; congr! 2
  ext <;> simp
  · simp only [← Category.assoc]; congr! 1
    exact H.isoPullback_hom_fst
  · exact H.isoPullback_hom_snd

/-- Switch the selected pullback `R` used in `UvPoly.Equiv.snd'` with a different pullback `R'`. -/
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
  simp [snd'_eq, fan_snd, ε]
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
    eqToHom (by congr 1; apply fst_comp_right) ≫ snd P X pair ≫ f := by
  rw [snd_eq_snd', snd'_comp_right, snd', Category.assoc, ← eqToIso.hom]; congr! 2
  exact IsPullback.isoPullback_eq_eqToIso_left (fst_comp_right _ _ _ f pair) P.p

lemma ext' {pair₁ pair₂ : Γ ⟶ P @ X}
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

/-- Switch the selected pullback `R` used in `UvPoly.Equiv.mk'` with a different pullback `R'`. -/
theorem mk'_eq_mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X)
    {R' f' g'} (H' : IsPullback (P := R') f' g' b P.p) :
    mk' P X b H x = mk' P X b (R := R') H' ((IsPullback.isoIsPullback _ _ H H').inv ≫ x) := by
  apply ext' P X (R := R) (f := f) (g := g) (by convert H; simp)
  · rw [snd'_eq_snd' P X (mk' P X b H' ((IsPullback.isoIsPullback _ _ H H').inv ≫ x))
      (by convert H; simp) (by convert H'; simp)]
    simp [snd'_mk']
  · simp

@[simp]
lemma eta' (pair : Γ ⟶ P @ X)
    {R f1 f2} (H : IsPullback (P := R) f1 f2 (fst P X pair) P.p) :
    mk' P X (fst P X pair) H (snd' P X pair H) = pair :=
  .symm <| ext' P X H (by simp) (by simp)

@[simp]
lemma eta (pair : Γ ⟶ P @ X) :
    mk P X (fst P X pair) (snd P X pair) = pair := by
  simp [mk_eq_mk', snd_eq_snd']

lemma mk'_comp_right (b : Γ ⟶ B) {R f1 f2} (H : IsPullback (P := R) f1 f2 b P.p) (x : R ⟶ X) :
    mk' P X b H x ≫ P.functor.map f = mk' P Y b H (x ≫ f) := by
  refine .symm <| ext' _ _ (by rwa [fst_mk']) (by simp [fst_comp_right]) ?_
  rw [snd'_comp_right (H := by rwa [fst_mk'])]; simp

lemma mk_comp_right (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    mk P X b x ≫ P.functor.map f = mk P Y b (x ≫ f) := by
  simp [mk_eq_mk', mk'_comp_right]

theorem mk'_comp_left {Δ}
    (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p) (x : R ⟶ X) (σ : Δ ⟶ Γ)
    (σb) (eq : σ ≫ b = σb)
    {R' f' g'} (H' : IsPullback (P := R') f' g' σb P.p) :
    σ ≫ UvPoly.Equiv.mk' P X b H x = UvPoly.Equiv.mk' P X σb H'
    (H.lift (f' ≫ σ) g' (by simp [eq, H'.w]) ≫ x) := by
  apply ext' P (R := R') (f := f') (g := g') (H := by convert H'; simp [eq, fst_eq])
  · rw [snd'_comp_left (H := by convert H; rw [fst_mk']) (H' := by convert H'; rw [← eq, fst_mk'])]
    simp
  · simp [eq, fst_comp_left]

theorem mk_comp_left {Δ} (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) (σ: Δ ⟶ Γ) :
    σ ≫ UvPoly.Equiv.mk P X b x =
    UvPoly.Equiv.mk P X (σ ≫ b)
      (pullback.map _ _ _ _ σ (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ x) := by
  simp only [mk_eq_mk']
  rw [mk'_comp_left (H := .of_hasPullback _ _) (H' := .of_hasPullback _ _) (eq := rfl)]
  congr 2; ext <;> simp

lemma mk'_comp_cartesianNatTrans_app {E' B' Γ X : C} {P' : UvPoly E' B'}
    (y : Γ ⟶ B) (R f g) (H : IsPullback (P := R) f g y P.p)
    (x : R ⟶ X) (e : E ⟶ E') (b : B ⟶ B')
    (hp : IsPullback P.p e b P'.p) :
    Equiv.mk' P X y H x ≫ (P.cartesianNatTrans P' b e hp).app X =
    Equiv.mk' P' X (y ≫ b) (H.paste_vert hp) x := by
  have : fst P' X (Equiv.mk' P X y H x ≫ (P.cartesianNatTrans P' b e hp).app X) = y ≫ b := by
    rw [fst_eq, Category.assoc, cartesianNatTrans_fstProj, ← Category.assoc, mk'_comp_fstProj]
  refine ext' _ _ (this ▸ H.paste_vert hp) (by simpa) ?_
  simp; rw [snd'_eq]
  have := snd'_mk' P X y H x
  rw [snd'_eq, ← fan_snd_map' _ _ X hp] at this
  refine .trans ?_ this
  simp only [← Category.assoc]; congr 1; ext <;> simp

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

def compP {E B D A : C} (P : UvPoly E B) (Q : UvPoly D A) : compDom P Q ⟶ P @ A :=
  pullback.snd Q.p (fan P A).snd ≫ pullback.fst (fan P A).fst P.p

@[simp] theorem compDomEquiv_symm_compP {Γ E B D A : 𝒞} {P : UvPoly E B}
    {Q : UvPoly D A} (AB : Γ ⟶ P @ A) (α : Γ ⟶ E)
    (β : Γ ⟶ D) (w : AB ≫ P.fstProj A = α ≫ P.p)
    (h : β ≫ Q.p = pullback.lift AB α w ≫ (PartialProduct.fan P A).snd) :
    compDomEquiv.symm ⟨AB, α, β, w, h⟩ ≫ P.compP Q = AB := by
   simp [compDomEquiv, compP, Equiv.psigmaCongrProp, Equiv.sigmaCongrRight_symm,
    Equiv.coe_fn_symm_mk, pullbackHomEquiv]

def compDomMap {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E') (d : D ⟶ D') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) (hq : IsPullback Q.p d a Q'.p) :
    compDom P Q ⟶ compDom P' Q' := by
  set p := P.cartesianNatTrans P' b e hp
  let pa := p.app A ≫ P'.functor.map a
  let r := pullback.map (P.fstProj A) P.p (P'.fstProj A') P'.p pa e b (by simp [pa, p]) hp.w
  refine pullback.map _ _ _ _ d r a hq.w (fan_snd_map _ _ _ hp).symm

theorem compDomMap_isPullback {E B D A E' B' D' A' : 𝒞} {P : UvPoly E B} {Q : UvPoly D A}
    {P' : UvPoly E' B'} {Q' : UvPoly D' A'}
    (e : E ⟶ E') (d : D ⟶ D') (b : B ⟶ B') (a : A ⟶ A')
    (hp : IsPullback P.p e b P'.p) (hq : IsPullback Q.p d a Q'.p) :
    IsPullback
      (UvPoly.compDomMap e d b a hp hq)
      (P.compP Q) (P'.compP Q')
      ((P.cartesianNatTrans P' b e hp).app A ≫ P'.functor.map a) := by
  set p := P.cartesianNatTrans P' b e hp
  apply IsPullback.paste_vert
    (h₂₁ := pullback.map _ _ _ _ (p.app A ≫ P'.functor.map a) _ _ (by simp [p]) hp.w)
  · refine hq.flip.back_face_of_comm_cube _ _ _ _ _ _ _ _ _ _ _ _ (by simp [compDomMap]) ?_ ?_
      (.of_hasPullback ..) (.of_hasPullback ..)
    · exact ⟨fan_snd_map _ _ a hp⟩
    · constructor; simp [compDomMap]; ext <;> simp [p]
  · exact hp.flip.back_face_of_comm_cube _ _ _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [p]) (by simp) (.flip (.of_hasPullback ..)) (.flip (.of_hasPullback ..))

end

open TwoSquare

section

variable {E B E' : C} {P : UvPoly E B} {P' : UvPoly E' B} {e : E ⟶ E'} (h : P.p = e ≫ P'.p)

lemma verticalNatTrans_app_fstProj (X : C) :
    (P.verticalNatTrans P' e h).app X ≫ P.fstProj X = P'.fstProj X := by
  unfold verticalNatTrans; lift_lets; intro _ _ _ sq; simp
  set α := sq.natTrans.app X
  apply α.w.trans; simp; rfl

lemma fst_verticalNatTrans_app {Γ : C} (X : C) (pair : Γ ⟶ P' @ X) :
    Equiv.fst P X (pair ≫ (verticalNatTrans P P' e h).app X) = Equiv.fst P' X pair := by
  simp [Equiv.fst, verticalNatTrans_app_fstProj]

open Functor ExponentiableMorphism in
lemma snd'_verticalNatTrans_app {Γ : C} (X : C) (pair : Γ ⟶ P' @ X) {R f g}
    (H : IsPullback (P := R) f g (Equiv.fst P' X pair) P.p) {R' f' g'}
    (H' : IsPullback (P := R') f' g' (Equiv.fst P' X pair) P'.p) :
    Equiv.snd' P X (pair ≫ (verticalNatTrans P P' e h).app X) (by rwa [fst_verticalNatTrans_app]) =
    H'.lift f (g ≫ e) (by simp [H.w, h]) ≫ Equiv.snd' P' X pair H' := by
  simp [Equiv.snd', Equiv.snd]
  rw [← Category.assoc, ← Category.assoc (Iso.hom _)]
  let S  := pullback (P.fstProj X)  P.p
  let S' := pullback (P'.fstProj X) P'.p
  let T := pullback (pullback.snd .. : S' ⟶ _) e
  have eq := ev_naturality (P := P) (P' := P') e (𝟙 _) ⟨by simpa⟩
  let sE  := Over.star E;  let UE  := Over.forget E; let UB := Over.forget B
  let sE' := Over.star E'; let UE' := Over.forget E'
  extract_lets pfwd p'fwd pbk ebk _1bk p'bk β bb at eq
  let Z  : sE  ⋙ pfwd  ⋙ pbk  ⟶ sE  := sE.whiskerLeft  (ev P.p)
  let Z' : sE' ⋙ p'fwd ⋙ p'bk ⟶ sE' := sE'.whiskerLeft (ev P'.p)
  dsimp only [fan]
  rw [← show (Z.app X).left = ε P X by rfl, ← show (Z'.app X).left = ε P' X by rfl]
  let α : sE' ⋙ ebk ⟶ sE := (Over.starPullbackIsoStar e).hom
  let γ : _1bk ≅ 𝟭 _ := Over.pullbackId (X := B)
  let y : sE' ⋙ p'fwd ⟶ sE ⋙ pfwd :=
    sE'.whiskerLeft (p'fwd.whiskerLeft γ.inv ≫ β) ≫ whiskerRight α pfwd
  have yeq : verticalNatTrans P P' e h = whiskerRight y UB := by
    unfold verticalNatTrans; extract_lets _ x1 x2
    simp [hComp, TwoSquare.mk, TwoSquare.natTrans, associator_eq_id]
    rw! [Category.id_comp, Category.id_comp, Category.comp_id]; congr 1
    simp [x1, x2, hComp, TwoSquare.mk, TwoSquare.natTrans, associator_eq_id, TwoSquare.whiskerRight]
    rw! [Category.id_comp, Category.comp_id, ← whiskerLeft_twice', ← whiskerLeft_comp_assoc]
  replace yeq := congr(($yeq).app X); simp [UB] at yeq
  replace eq := congr(sE'.whiskerLeft (whiskerRight (p'fwd.whiskerLeft γ.inv) pbk ≫ $eq) ≫ α)
  conv_rhs at eq => rw [← whiskerRight_comp_assoc, whiskerLeft_comp, Category.assoc]
  have := whiskerLeft_comp_whiskerRight (H := pfwd ⋙ pbk) α (ev P.p)
  rw [id_whiskerRight', ← whiskerLeft_twice'] at this
  rw [this] at eq; clear this
  rw [← whiskerRight_left', ← whiskerRight_twice', ← whiskerRight_comp_assoc,
    ← Category.assoc, whiskerLeft_comp, Category.assoc, ← whiskerRight_left',
    whiskerRight_left', ← whiskerLeft_comp, ← isoWhiskerRight_inv,
    ← Iso.symm_inv, ← Iso.trans_inv] at eq
  set cc : p'bk ⋙ ebk ≅ pbk := bb.symm ≪≫ isoWhiskerRight γ pbk
  change _ ≫ whiskerRight Z' ebk ≫ _ = whiskerRight y pbk ≫ Z at eq
  rw [← isoWhiskerLeft_inv, ← isoWhiskerLeft_inv, Iso.inv_comp_eq] at eq
  replace eq := congr((($eq).app X).left ≫ prod.snd); simp [ebk] at eq
  rw [← Category.assoc, ← Category.assoc] at eq
  let t : T ≅ _ := UE.mapIso (cc.app (p'fwd.obj (sE'.obj X)))
  change let r1 : T ⟶ S := t.hom ≫ _; _ = r1 ≫ _ at eq; extract_lets r1 at eq
  have hT := IsPullback.of_iso_pullback (P := T) ⟨by simp [pullback.condition]⟩ t rfl rfl
  have t1eq : t.hom ≫ pullback.fst .. = pullback.fst .. ≫ pullback.fst .. := by
    simp [t, UE, cc, bb, γ, pbk, _1bk, Over.pullbackId, Adjunction.id, Over.pullbackComp]; rfl
  have t2eq : t.hom ≫ pullback.snd .. = pullback.snd .. := by
    simp [t, UE, cc, bb, γ, pbk, _1bk, Over.pullbackId, Adjunction.id, Over.pullbackComp]; rfl
  rw [t1eq, t2eq] at hT
  conv_lhs at eq => equals pullback.fst .. ≫ (Z'.app X).left ≫ prod.snd =>
    simp [α, Over.starPullbackIsoStar, Over.mapForget]
    rw [Category.id_comp, pullback.lift_fst_assoc, Category.assoc]
  replace eq := congr(hT.lift (f ≫ pair) g (by simp [← H.w]; rfl) ≫ $eq)
  rw [← Category.assoc, ← Category.assoc _ r1] at eq; rw [← Category.assoc (H'.lift ..)]
  convert eq.symm using 2
  · apply pullback.hom_ext <;> simp [r1, pbk]
    · rw! [pullback.lift_fst, reassoc_of% t1eq, reassoc_of% hT.lift_fst ..,
        reassoc_of% IsPullback.isoPullback_hom_fst]; simp [yeq]
    · rw! [IsPullback.isoPullback_hom_snd, pullback.lift_snd, t2eq, hT.lift_snd]
  · apply pullback.hom_ext <;> simp
    · rw! [reassoc_of% IsPullback.isoPullback_hom_fst, hT.lift_fst]; simp
    · rw! [pullback.condition, reassoc_of% hT.lift_snd]
      rw! [IsPullback.isoPullback_hom_snd]; simp

lemma mk'_comp_verticalNatTrans_app {Γ : C} (X : C) (b : Γ ⟶ B) {R f g}
    (H : IsPullback (P := R) f g b P.p) {R' f' g'}
    (H' : IsPullback (P := R') f' g' b P'.p) (x : R' ⟶ X) :
    Equiv.mk' P' X b H' x ≫ (verticalNatTrans P P' e h).app X =
    Equiv.mk' P X b H (H'.lift f (g ≫ e) (by simp [H.w, h]) ≫ x) := by
  fapply Equiv.ext' P _ (by simp [fst_verticalNatTrans_app]; exact H)
  · simp [fst_verticalNatTrans_app]
  · rw [snd'_verticalNatTrans_app h (H := by simpa) (H' := by simpa)]; simp

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
