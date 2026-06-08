import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.Tactic.CategoryTheory.FunctorMap
import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone
import HoTTLean.ForMathlib.CategoryTheory.WeakPullback
import Mathlib.Tactic.DepRewrite

universe v u

noncomputable section

open CategoryTheory Limits Opposite

namespace Model

/-- A natural model with support for dependent types (and nothing more).
The data is a natural transformation with representable fibers,
stored as a choice of representative for each fiber. -/
structure UnstructuredUniverse (Ctx : Type u) [Category Ctx] where
  Tm : Ctx
  Ty : Ctx
  tp : Tm ⟶ Ty
  ext {Γ : Ctx} (A : Γ ⟶ Ty) : Ctx
  disp {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Γ
  var {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Tm
  disp_pullback {Γ : Ctx} (A : Γ ⟶ Ty) :
    IsPullback (var A) (disp A) tp A

namespace UnstructuredUniverse

variable {Ctx : Type u} [Category Ctx] (M : UnstructuredUniverse Ctx)

@[reassoc (attr := simp)]
theorem var_tp {Γ : Ctx} (A : Γ ⟶ M.Ty) : M.var A ≫ M.tp = (M.disp A) ≫ A := by
  simp [(M.disp_pullback A).w]

/-! ## Pullback of representable natural transformation -/

/-- Pull a natural model back along a type. -/
protected def pullback {Γ : Ctx} (A : Γ ⟶ M.Ty) : UnstructuredUniverse Ctx where
  Tm := M.ext A
  Ty := Γ
  tp := M.disp A
  ext := fun B => M.ext (B ≫ A)
  disp := fun B => M.disp (B ≫ A)
  var := fun B => (M.disp_pullback A).lift (M.var (B ≫ A))
    (M.disp (B ≫ A) ≫ B) (by simp [(M.disp_pullback (B ≫ A)).w])
  disp_pullback := fun B =>
    IsPullback.of_right' (M.disp_pullback (B ≫ A)) (M.disp_pullback A)

/--
  Given the pullback square on the right,
  with a natural model structure on `tp : Tm ⟶ Ty`
  giving the outer pullback square.

  Γ.A -.-.- var -.-,-> E ------ toTm ------> Tm
   |                   |                      |
   |                   |                      |
 M.disp                π                     tp
   |                   |                      |
   V                   V                      V
  Γ ------- A -------> U ------ toTy ------> Ty

  construct a natural model structure on `π : E ⟶ U`,
  by pullback pasting.
-/
def ofIsPullback {U E : Ctx} {π : E ⟶ U}
    {toTy : U ⟶ M.Ty} {toTm : E ⟶ M.Tm}
    (pb : IsPullback toTm π M.tp toTy) :
    UnstructuredUniverse Ctx where
  Ty := U
  Tm := E
  tp := π
  ext A := M.ext (A ≫ toTy)
  disp A := M.disp (A ≫ toTy)
  var A := pb.lift (M.var (A ≫ toTy)) (M.disp (A ≫ toTy) ≫ A)
    (by simp [(M.disp_pullback (A ≫ toTy)).w])
  disp_pullback A := IsPullback.of_right' (M.disp_pullback (A ≫ toTy)) pb

/-! ## Substitutions -/

/--
```
Δ ⊢ σ : Γ  Γ ⊢ A type  Δ ⊢ t : A[σ]
-----------------------------------
Δ ⊢ σ.t : Γ.A
```
 ------ Δ ------ t --------¬
 |      ↓ substCons         ↓
 |   M.ext A ---var A---> M.Tm
 |      |                  |
 σ      |                  |
 |    disp A              M.tp
 |      |                  |
 |      V                  V
  ---> Γ ------ A -----> M.Ty
-/
def substCons {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty)
    (t : Δ ⟶ M.Tm) (t_tp : t ≫ M.tp = σ ≫ A) :
    Δ ⟶ M.ext A :=
  (M.disp_pullback A).lift t σ t_tp

@[reassoc (attr := simp)]
theorem substCons_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (t : Δ ⟶ M.Tm)
    (tTp : t ≫ M.tp = σ ≫ A) :
    M.substCons σ A t tTp ≫ M.disp A = σ := by
  simp [substCons]

@[reassoc (attr := simp)]
theorem substCons_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (t : Δ ⟶ M.Tm)
    (aTp : t ≫ M.tp = σ ≫ A) :
    M.substCons σ A t aTp ≫ M.var A = t := by
  simp [substCons]

@[simp]
theorem comp_substCons {Θ Δ Γ : Ctx} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (t : Δ ⟶ M.Tm)
    (aTp : t ≫ M.tp = σ ≫ A) :
    τ ≫ M.substCons σ A t aTp = M.substCons (τ ≫ σ) A (τ ≫ t) (by simp [*]) := by
  apply (M.disp_pullback A).hom_ext
  · simp
  · simp

@[reassoc (attr := simp)]
theorem substCons_apply_comp_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (s : Δ ⟶ M.ext A)
    (s_tp : s ≫ M.disp A = σ) :
    M.substCons σ A (s ≫ M.var A) (by rw [Category.assoc, var_tp, ← Category.assoc, s_tp]) =
    s := by
  apply (disp_pullback ..).hom_ext <;> simp [s_tp]

/--
```
Δ ⊢ σ : Γ.A
------------
Δ ⊢ ↑∘σ : Γ
```
-/
def substFst {Δ Γ : Ctx} {A : Γ ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : Δ ⟶ Γ :=
  σ ≫ M.disp A

/--
```
Δ ⊢ σ : Γ.A
-------------------
Δ ⊢ v₀[σ] : A[↑∘σ]
```
-/
def substSnd {Δ Γ : Ctx} {A : Γ ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : Δ ⟶ M.Tm :=
  σ ≫ M.var A

theorem substSnd_tp {Δ Γ : Ctx} {A : Γ ⟶ M.Ty} (σ : Δ ⟶ M.ext A) :
    M.substSnd σ ≫ M.tp = (M.substFst σ) ≫ A := by
  simp [substSnd, substFst]

/--
Weaken a substitution.
```
Δ ⊢ σ : Γ  Γ ⊢ A type  A' = A[σ]
------------------------------------
Δ.A' ⊢ ↑≫σ : Γ  Δ.A' ⊢ v₀ : A[↑≫σ]
------------------------------------
Δ.A' ⊢ (↑≫σ).v₀ : Γ.A
```
-/
def substWk {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty)
    (A' := σ ≫ A) (eq : σ ≫ A = A' := by rfl) : M.ext A' ⟶ M.ext A :=
  M.substCons (M.disp _ ≫ σ) A (M.var _) (by simp [eq])

@[reassoc (attr := simp)]
theorem substWk_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (A' eq) :
    M.substWk σ A A' eq ≫ M.disp A = M.disp A' ≫ σ := by
  simp [substWk]

@[reassoc (attr := simp)]
theorem substWk_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (A' eq) :
    M.substWk σ A A' eq ≫ M.var A = M.var A' := by
  simp [substWk]

lemma var_comp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) : M.var (σ ≫ A) =
    M.substWk σ A ≫ M.var A := by
  simp

/-- `sec` is the section of `disp A` corresponding to `a`.

  ===== Γ ------ a --------¬
 ‖      ↓ sec             V
 ‖   M.ext A -----------> M.Tm
 ‖      |                  |
 ‖      |                  |
 ‖    disp A              M.tp
 ‖      |                  |
 ‖      V                  V
  ===== Γ ------ A -----> M.Ty -/
def sec {Γ : Ctx} (A : Γ ⟶ M.Ty) (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) : Γ ⟶ M.ext A :=
  M.substCons (𝟙 Γ) A a (by simp [a_tp])

@[reassoc (attr := simp)]
theorem sec_disp {Γ : Ctx} (A : Γ ⟶ M.Ty) (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.sec A a a_tp ≫ M.disp A = 𝟙 _ := by
  simp [sec]

@[reassoc (attr := simp)]
theorem sec_var {Γ : Ctx} (A : Γ ⟶ M.Ty) (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.sec A a a_tp ≫ M.var A = a := by
  simp [sec]

@[reassoc]
theorem comp_sec {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (σA) (eq : σ ≫ A = σA)
    (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    σ ≫ M.sec A a a_tp = M.sec σA (σ ≫ a) (by simp [eq, a_tp]) ≫ M.substWk σ A _ eq := by
  apply (M.disp_pullback _).hom_ext <;>
    simp [sec, substWk]

@[reassoc (attr := simp)]
theorem sec_apply_comp_var {Γ : Ctx} (A : Γ ⟶ M.Ty)
    (s : Γ ⟶ M.ext A) (s_tp : s ≫ M.disp A = 𝟙 _) :
    M.sec A (s ≫ M.var A) (by rw [Category.assoc, var_tp, ← Category.assoc, s_tp]; simp) = s := by
  apply substCons_apply_comp_var _ _ _ _ s_tp

structure PolymorphicSigma (U0 U1 U2 : UnstructuredUniverse Ctx) where
  (Sig : ∀ {Γ} {A : Γ ⟶ U0.Ty}, (U0.ext A ⟶ U1.Ty) → (Γ ⟶ U2.Ty))
  (Sig_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : Γ ⟶ U0.Ty) {σA} (eq) (B : U0.ext A ⟶ U1.Ty),
    Sig (U0.substWk σ A σA eq ≫ B) = σ ≫ Sig B)
  (pair : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (a : Γ ⟶ U0.Tm)
    (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm), b ≫ U1.tp = U0.sec A a a_tp ≫ B →
    (Γ ⟶ U2.Tm))
  (pair_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) (B : U0.ext A ⟶ U1.Ty)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
    (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
    pair (U0.substWk σ A σA eq ≫ B) (σ ≫ a) (by cat_disch) (σ ≫ b)
      (by simp [b_tp, comp_sec_assoc, eq]) =
      σ ≫ pair B a a_tp b b_tp)
  (pair_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
    (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
      pair B a a_tp b b_tp ≫ U2.tp = Sig B)
  (fst : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm),
    s ≫ U2.tp = Sig B → (Γ ⟶ U0.Tm))
  (fst_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
    (s_tp : s ≫ U2.tp = Sig B), fst B s s_tp ≫ U0.tp = A)
  (snd : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm),
    s ≫ U2.tp = Sig B → (Γ ⟶ U1.Tm))
  (snd_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
    (s_tp : s ≫ U2.tp = Sig B), snd B s s_tp ≫ U1.tp = U0.sec A (fst B s s_tp) (fst_tp ..) ≫ B)
  (fst_pair : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
    (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B), fst B (pair B a a_tp b b_tp) (pair_tp ..) = a)
  (snd_pair : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
    (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B), snd B (pair B a a_tp b b_tp) (pair_tp ..) = b)
  (pair_fst_snd : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
    (s_tp : s ≫ U2.tp = Sig B), pair B (fst B s s_tp) (fst_tp ..) (snd B s s_tp) (snd_tp ..) = s)

namespace PolymorphicSigma

attribute [simp] pair_tp fst_tp snd_tp fst_pair snd_pair pair_fst_snd

variable {U0 U1 U2 : UnstructuredUniverse Ctx}

def mk' (Sig : ∀ {Γ} {A : Γ ⟶ U0.Ty}, (U0.ext A ⟶ U1.Ty) → (Γ ⟶ U2.Ty))
    (Sig_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : Γ ⟶ U0.Ty) {σA} (eq) (B : U0.ext A ⟶ U1.Ty),
      Sig (U0.substWk σ A σA eq ≫ B) = σ ≫ Sig B)
    (assoc : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty), U1.ext B ≅ U2.ext (Sig B))
    (assoc_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) (B : U0.ext A ⟶ U1.Ty),
     (assoc (substWk U0 σ A σA eq ≫ B)).hom ≫ substWk U2 σ _ _ (Sig_comp ..).symm =
     substWk _ (substWk _ σ _ _ eq) _ ≫ (assoc B).hom )
    (assoc_disp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty),
      (assoc B).hom ≫ disp .. = disp .. ≫ disp ..) :
    PolymorphicSigma U0 U1 U2 where
  Sig := Sig
  Sig_comp := Sig_comp
  pair B a a_tp b b_tp := U1.substCons (U0.sec _ a a_tp) B b (by simp [b_tp]) ≫
    (assoc B).hom ≫ var ..
  pair_comp σ A σA eq B a a_tp b b_tp := by
    have : σ ≫ U1.substCons (U0.sec A a a_tp) B b b_tp =
      U1.substCons (U0.sec (σA) (σ ≫ a) (by simp [eq, a_tp])) (substWk U0 σ A σA eq ≫ B)
      (σ ≫ b) (by simp [b_tp, comp_sec_assoc, eq]) ≫ substWk U1 (substWk U0 σ A σA eq) B := by
      apply (disp_pullback ..).hom_ext
      · simp
      · apply (disp_pullback ..).hom_ext
        · simp
        · simp [substWk_disp]
    slice_rhs 1 2 => rw [this]
    slice_rhs 2 3 => rw [← assoc_comp]
    simp
  pair_tp B a a_tp b b_tp := by
    slice_lhs 3 4 => rw [var_tp]
    slice_lhs 2 3 => rw [assoc_disp]
    simp
  fst B s s_tp := U2.sec _ s s_tp ≫ (assoc _).inv ≫ disp .. ≫ var ..
  fst_tp B s s_tp := by
    slice_lhs 4 5 => rw [var_tp]
    slice_lhs 3 4 => rw [← assoc_disp]
    simp
  snd B s s_tp := U2.sec _ s s_tp ≫ (assoc _).inv ≫ var ..
  snd_tp B s s_tp := by
    slice_lhs 3 4 => rw [var_tp]
    simp only [← Category.assoc]
    congr 2
    apply (disp_pullback ..).hom_ext
    · simp
    · simp [← assoc_disp]
  fst_pair B a a_tp b b_tp := by
    simp only [← Category.assoc]
    rw [sec_apply_comp_var _ _ _ (by simp [assoc_disp])]
    simp
  snd_pair B a a_tp b b_tp := by
    simp only [← Category.assoc]
    rw [sec_apply_comp_var _ _ _ (by simp [assoc_disp])]
    simp
  pair_fst_snd B s s_tp := by
    simp only [← Category.assoc]
    rw! [sec_apply_comp_var _ _ _ (by simp [← assoc_disp])]
    rw [U1.substCons_apply_comp_var _ _ _ (by simp)]
    simp

variable (S : PolymorphicSigma U0 U1 U2)

lemma fst_comp {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) {B : U0.ext A ⟶ U1.Ty}
    (s : Γ ⟶ U2.Tm) (s_tp : s ≫ U2.tp = S.Sig B) :
    S.fst (U0.substWk σ A σA eq ≫ B) (σ ≫ s) (by simp [s_tp, S.Sig_comp]) =
    σ ≫ S.fst B s s_tp := by
  rw! [(S.pair_fst_snd B s (by simp [s_tp])).symm, ← S.pair_comp, S.fst_pair, S.fst_pair]
  rfl

lemma snd_comp {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) {B : U0.ext A ⟶ U1.Ty}
    (s : Γ ⟶ U2.Tm) (s_tp : s ≫ U2.tp = S.Sig B) :
    S.snd (U0.substWk σ A σA eq ≫ B) (σ ≫ s) (by simp [s_tp, S.Sig_comp]) =
    σ ≫ S.snd B s s_tp := by
  rw! [(S.pair_fst_snd B s (by simp [s_tp])).symm, ← S.pair_comp, S.snd_pair, S.snd_pair]
  rfl

end PolymorphicSigma

structure PolymorphicPi (U0 U1 U2 : UnstructuredUniverse Ctx) where
  (Pi : ∀ {Γ} {A : Γ ⟶ U0.Ty}, (U0.ext A ⟶ U1.Ty) → (Γ ⟶ U2.Ty))
  (Pi_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : Γ ⟶ U0.Ty) {σA} (eq) (B : U0.ext A ⟶ U1.Ty),
    Pi (U0.substWk σ A σA eq ≫ B) = σ ≫ Pi B)
  (lam : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (b : U0.ext A ⟶ U1.Tm), b ≫ U1.tp = B → (Γ ⟶ U2.Tm))
  (lam_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) (B : U0.ext A ⟶ U1.Ty)
    (b : U0.ext A ⟶ U1.Tm) (b_tp : b ≫ U1.tp = B),
    lam (U0.substWk σ A σA eq ≫ B) (U0.substWk σ A σA eq ≫ b) (by cat_disch) =
      σ ≫ lam B b b_tp)
  (lam_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (b : U0.ext A ⟶ U1.Tm) (b_tp : b ≫ U1.tp = B),
      lam B b b_tp ≫ U2.tp = Pi B)
  (unLam : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (f : Γ ⟶ U2.Tm),
    f ≫ U2.tp = Pi B → (U0.ext A ⟶ U1.Tm))
  (unLam_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (f : Γ ⟶ U2.Tm)
    (f_tp : f ≫ U2.tp = Pi B), unLam B f f_tp ≫ U1.tp = B)
  (unLam_lam : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (b : U0.ext A ⟶ U1.Tm) (b_tp : b ≫ U1.tp = B), unLam B (lam B b b_tp) (lam_tp ..) = b)
  (lam_unLam : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (f : Γ ⟶ U2.Tm)
    (f_tp : f ≫ U2.tp = Pi B), lam B (unLam B f f_tp) (unLam_tp ..) = f)

namespace PolymorphicPi

attribute [simp] lam_tp unLam_tp unLam_lam lam_unLam

variable {U0 U1 U2 : UnstructuredUniverse Ctx} (P : PolymorphicPi U0 U1 U2)

lemma unLam_comp {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) {B : U0.ext A ⟶ U1.Ty}
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.Pi B) :
    P.unLam (U0.substWk σ A σA eq ≫ B) (σ ≫ f) (by simp [f_tp, P.Pi_comp]) =
    U0.substWk σ A σA eq ≫ P.unLam B f f_tp := by
  rw [← P.unLam_lam (U0.substWk σ A σA eq ≫ B) (U0.substWk σ A σA eq ≫ P.unLam B f f_tp)]
  . rw! [P.lam_comp σ eq B, P.lam_unLam]
    rfl
  . rw [Category.assoc, P.unLam_tp]

/--
```
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B  Γ ⊢ᵢ a : A
---------------------------------
Γ ⊢ⱼ f a : B[id.a]
``` -/
def app {Γ : Ctx} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.Pi B)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) : Γ ⟶ U1.Tm :=
  U0.sec A a a_tp ≫ P.unLam B f f_tp

@[simp]
theorem app_tp {Γ : Ctx} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.Pi B)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) :
    P.app B f f_tp a a_tp ≫ U1.tp = (U0.sec A a a_tp) ≫ B := by
  simp [app]

theorem app_comp {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    {A : Γ ⟶ U0.Ty} (σA) (eq : σ ≫ A = σA)
    (B : U0.ext A ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.Pi B)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) :
      P.app (U0.substWk σ A _ eq ≫ B)
        (σ ≫ f) (by simp [f_tp, Pi_comp])
        (σ ≫ a) (by simp [a_tp, eq]) =
      σ ≫ P.app B f f_tp a a_tp := by
  rw [app, app, reassoc_of% comp_sec, unLam_comp]

/--
```
Γ ⊢ᵢ A  Γ.A ⊢ⱼ t : B  Γ ⊢ᵢ a : A
--------------------------------
Γ.A ⊢ⱼ (λA. t) a ≡ t[a] : B[a]
``` -/
@[simp]
theorem app_lam {Γ : Ctx} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (t : U0.ext A ⟶ U1.Tm) (t_tp : t ≫ U1.tp = B)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) :
    P.app B (P.lam B t t_tp) (by simp) a a_tp = U0.sec A a a_tp ≫ t := by
  simp [app]

/--
```
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ f : ΠA. B
--------------------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ λA. f[↑] v₀ : ΠA. B
```
-/
def etaExpand {Γ : Ctx} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.Pi B) :
    Γ ⟶ U2.Tm :=
  P.lam B
    (P.app (A := U0.disp A ≫ A) (U0.substWk .. ≫ B)
      (U0.disp A ≫ f) (by simp [Pi_comp, f_tp])
      (U0.var A) (U0.var_tp A))
    (by
      rw [app_tp, substWk, reassoc_of% comp_substCons]
      simp [substCons])

@[simp]
theorem etaExpand_eq {Γ : Ctx} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.Pi B) :
    P.etaExpand B f f_tp = f := by
  unfold etaExpand
  convert P.lam_unLam B f f_tp using 2
  rw [app, unLam_comp (f_tp := f_tp), substWk, reassoc_of% comp_substCons]
  simp [substCons]

end PolymorphicPi

structure PolymorphicIdIntro (U0 U1 : UnstructuredUniverse Ctx) where
  (Id : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm), (a0 ≫ U0.tp = A) → a1 ≫ U0.tp = A →
    (Γ ⟶ U1.Ty))
  (Id_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm)
    (a0_tp : a0 ≫ U0.tp = A) (a1_tp : a1 ≫ U0.tp = A),
    Id (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by cat_disch) (by cat_disch) = σ ≫ Id a0 a1 a0_tp a1_tp)
  (refl : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm), a ≫ U0.tp = A → (Γ ⟶ U1.Tm))
  (refl_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm)
    (a_tp : a ≫ U0.tp = A), refl (σ ≫ a) (by cat_disch) = σ ≫ refl a a_tp)
  (refl_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A),
    refl a a_tp ≫ U1.tp = Id a a a_tp a_tp)

section

variable {U0 U1 : UnstructuredUniverse Ctx} (i : PolymorphicIdIntro U0 U1)

namespace PolymorphicIdIntro

attribute [simp] refl_tp

variable {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)

/-- Given `Γ ⊢ a : A`, this is the identity type `Γ.(y : A) ⊢ Id(a, y) : U1.Ty`. -/
@[simp]
abbrev weakenId : U0.ext A ⟶ U1.Ty :=
  i.Id (A := U0.disp A ≫ A) (U0.disp A ≫ a) (U0.var A) (by simp [*]) (by simp)

lemma weakenId_comp :
    i.weakenId (A := σ ≫ A) (σ ≫ a) (by simp [*]) =
    U0.substWk σ A ≫ i.weakenId a a_tp := by
  simp [← Id_comp]

/-- Given `Γ ⊢ a : A`, this is the context `Γ.(y : A).Id(a, y)`. -/
@[simp]
abbrev motiveCtx : Ctx :=
  U1.ext (i.weakenId a a_tp)

variable (b : Γ ⟶ U0.Tm) (b_tp : b ≫ U0.tp = A)
  (h : Γ ⟶ U1.Tm) (h_tp : h ≫ U1.tp = i.Id a b a_tp b_tp)

/-- Given `Γ ⊢ b : A` and `Γ ⊢ h : Id(a, b)`,
this is the substitution `Γ ⊢ σ.b.h : Γ.(y : A).Id(a, y)`. -/
abbrev motiveInst : Γ ⟶ i.motiveCtx a a_tp :=
  let σb := U0.substCons (𝟙 _) A b (by simp [b_tp])
  U1.substCons σb (i.weakenId a a_tp) h (by simp +zetaDelta [*, ← Id_comp])

/-- Given `Γ ⊢ a : A`, this is the substitution `Γ ⊢ 𝟙.a.refl : Γ.(y : A).Id(a, y)`. -/
abbrev reflInst : Γ ⟶ i.motiveCtx a a_tp :=
  i.motiveInst a a_tp a a_tp (i.refl a a_tp) (by simp)

/-- Given a substitution `Δ ⊢ σ : Γ` and `Γ ⊢ a : A`,
this is the substitution `Δ.(y : σ ≫ A).Id(σ ≫ a, y) ⊢ (↑²≫σ).v₁.v₀ : Γ.(y : A).Id(a, y)`. -/
abbrev motiveSubst {σA} (σA_eq : σA = σ ≫ A := by rfl) :
    i.motiveCtx (A := σA) (σ ≫ a) (by simp [*]) ⟶ i.motiveCtx a a_tp :=
  U1.substWk (U0.substWk σ A σA (by simp [*])) _ _ (by
    simp [← Id_comp, substWk_disp_assoc, σA_eq])

@[reassoc]
lemma motiveInst_comp_motiveSubst
    {σA} (σA_eq : σA = σ ≫ A := by rfl) :
    i.motiveInst (σ ≫ a) (by simp [*]) (σ ≫ b) (by simp [*]) (σ ≫ h) (by simp [*, Id_comp]) ≫
      i.motiveSubst σ a a_tp σA_eq =
    σ ≫ i.motiveInst a a_tp b b_tp h h_tp := by
  subst a_tp σA_eq
  repeat any_goals apply (disp_pullback ..).hom_ext
  any_goals simp [substWk_disp]

@[reassoc]
lemma reflInst_comp_motiveSubst {σA} (σA_eq : σA = σ ≫ A := by rfl) :
    i.reflInst (A := σA) (σ ≫ a) (by simp [*]) ≫ i.motiveSubst σ a a_tp σA_eq =
    σ ≫ i.reflInst a a_tp := by
  convert i.motiveInst_comp_motiveSubst ..
  simp [← refl_comp, *]

end PolymorphicIdIntro

open PolymorphicIdIntro in
structure PolymorphicIdElim (U2 : UnstructuredUniverse Ctx) where
  /-- Paulin-Mohring formulation of the J rule,
  stated over the context `Γ.(y : A).Id(a, y)`. -/
  (jElim : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
    (C : i.motiveCtx a a_tp ⟶ U2.Ty)
    (c : Γ ⟶ U2.Tm), (c ≫ U2.tp = i.reflInst a a_tp ≫ C) →
    (i.motiveCtx a a_tp ⟶ U2.Tm))
  (jElim_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
    (C : i.motiveCtx a a_tp ⟶ U2.Ty)
    (c : Γ ⟶ U2.Tm) (c_tp : c ≫ U2.tp = i.reflInst a a_tp ≫ C),
    jElim (σ ≫ a) (by simp [a_tp]) (i.motiveSubst σ a a_tp rfl ≫ C) (σ ≫ c)
      (by simp [*, reflInst_comp_motiveSubst_assoc]) =
    i.motiveSubst σ a a_tp rfl ≫ jElim a a_tp C c c_tp)
  (jElim_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
    (C : i.motiveCtx a a_tp ⟶ U2.Ty)
    (c : Γ ⟶ U2.Tm) (c_tp : c ≫ U2.tp = i.reflInst a a_tp ≫ C),
    jElim a a_tp C c c_tp ≫ U2.tp = C)
  (reflSubst_jElim : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
    (C : i.motiveCtx a a_tp ⟶ U2.Ty)
    (c : Γ ⟶ U2.Tm) (c_tp : c ≫ U2.tp = i.reflInst a a_tp ≫ C),
    i.reflInst a a_tp ≫ jElim a a_tp C c c_tp = c)

namespace PolymorphicIdElim
open PolymorphicIdIntro

attribute [simp] jElim_tp reflSubst_jElim

variable {i} {U2 : UnstructuredUniverse Ctx} (e : PolymorphicIdElim i U2)
  {Γ Δ} (σ : Δ ⟶ Γ)
  {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
  (I : U0.ext A ⟶ U1.Ty) (I_eq : I = i.weakenId a a_tp := by rfl)
  (M : U1.ext I ⟶ U2.Ty)
  (r : Γ ⟶ U2.Tm)
  (r_tp : r ≫ U2.tp =
    -- TODO: by>
    U1.substCons (U0.sec A a a_tp) I (i.refl a a_tp) (by simp [I_eq, ← Id_comp]) ≫ M)
  (b : Γ ⟶ U0.Tm) (b_tp : b ≫ U0.tp = A)
  (h : Γ ⟶ U1.Tm) (h_tp : h ≫ U1.tp = i.Id a b a_tp b_tp)

def idRec : Γ ⟶ U2.Tm :=
  i.motiveInst a a_tp b b_tp h h_tp ≫
  e.jElim a a_tp (eqToHom (by simp [I_eq]) ≫ M) r
    (by
      rw [r_tp]; congr 1 <;> simp [I_eq]
      . rw! [I_eq]; rfl)

theorem idRec_comp (σA) (σA_eq : σ ≫ A = σA)
    (σI) (σI_eq : U0.substWk σ A σA σA_eq ≫ I = σI) :
    e.idRec (A := σA) (σ ≫ a) (by simp [*])
      σI (by simp [← Id_comp, ← σI_eq, *])
      (U1.substWk (U0.substWk σ _ _ σA_eq) _ _ σI_eq ≫ M)
      (σ ≫ r) (by
        rw [Category.assoc, r_tp]
        simp only [← Category.assoc]; congr 1
        apply (U1.disp_pullback _).hom_ext <;>
          simp [← refl_comp, comp_sec, *])
      (σ ≫ b) (by simp [*])
      (σ ≫ h) (by simp [*, ← Id_comp]) =
    σ ≫ e.idRec a a_tp I I_eq M r r_tp b b_tp h h_tp := by
  unfold idRec
  slice_rhs 1 2 => rw [← motiveInst_comp_motiveSubst]
  slice_rhs 2 3 => rw [← jElim_comp]
  cases I_eq
  have : σI =
      i.Id (A := U0.disp σA ≫ σA) (U0.disp σA ≫ σ ≫ a) (U0.var σA) (by simp [*]) (by simp) := by
    cases σI_eq; simp [← Id_comp, *]
  cases this; cases σA_eq
  simp

@[simp]
theorem idRec_tp :
    e.idRec a a_tp I I_eq M r r_tp b b_tp h h_tp ≫ U2.tp =
      U1.substCons (U0.sec A b b_tp) I h (by simp [h_tp, I_eq, ← Id_comp]) ≫ M := by
  simp only [idRec, Category.assoc, jElim_tp]
  rw! (castMode := .all) [I_eq]
  simp only [← Category.assoc]; congr 1
  simp [motiveInst, sec]

@[simp]
theorem idRec_refl :
    e.idRec a a_tp I I_eq M r r_tp a a_tp (i.refl a a_tp) (by simp) = r := by
  simp [idRec]

end PolymorphicIdElim

end

end UnstructuredUniverse

end Model
