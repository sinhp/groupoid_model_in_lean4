import SEq.Tactic.DepRewrite
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
import Poly.UvPoly.UPFan
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

import GroupoidModel.ForPoly
import GroupoidModel.ForMathlib.Tactic.CategoryTheory.FunctorMap
import GroupoidModel.ForMathlib.CategoryTheory.Yoneda
import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone
import GroupoidModel.ForMathlib.CategoryTheory.WeakPullback

universe v u

noncomputable section

namespace CategoryTheory

open Limits

/-- A category with representable maps (Taichi Uemura thesis Def 3.2.1)
consists of a category `C` with finite limits equipped with a pullback-stable class `R` of
exponentiable arrows. Arrows in `R` are called representable maps.

For compatibility with `Poly` we draw representable maps `g` horizontally, for example in
```
     fst
  P ---->> X
  |        |
  |  (pb)  |
  V        V
  Y ---->> Z
      g
```
-/
structure RepMap (C : Type u) [Category.{v} C] [HasFiniteLimits C] where
  Representable : MorphismProperty C
  exponentiableMorphism : ∀ {X Y} {f : X ⟶ Y}, Representable f → ExponentiableMorphism f
  pullback_stable : ∀ {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z),
    IsPullback fst snd f g → Representable g → Representable fst

namespace RepMap

variable {Ctx : Type u} [Category Ctx] [HasFiniteLimits Ctx] (CwR : RepMap Ctx)

/-- A universe is a representable map that can (furthermore) be treated as a strict model of type
theory. To interpret context extension strictly, a chosen pullback `ext` is given for every
substitution into the universe `A : Γ ⟶ Ty`.
```
    disp
ext ---> Γ
|        |
|var     | A
|        |
V        V
Tm ----> Ty
    tp
```
-/
structure Universe where
  Tm : Ctx
  Ty : Ctx
  tp : Tm ⟶ Ty
  ext {Γ : Ctx} (A : Γ ⟶ Ty) : Ctx
  disp {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Γ
  var {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Tm
  disp_pullback {Γ : Ctx} (A : Γ ⟶ Ty) :
    IsPullback (disp A) (var A) A tp
  tp_representable : CwR.Representable tp

namespace Universe

variable {CwR} (U : Universe CwR) {Γ} (A : Γ ⟶ U.Ty)

@[reassoc (attr := simp)]
theorem var_tp : U.var A ≫ U.tp = U.disp A ≫ A := by
  simp [(U.disp_pullback A).w]

theorem disp_representable :
    CwR.Representable (U.disp A) :=
  CwR.pullback_stable _ _ _ _ (U.disp_pullback A) U.tp_representable

@[simps! hom inv]
def pullbackIsoExt {Γ : Ctx} (A : Γ ⟶ U.Ty) :
    pullback A U.tp ≅ U.ext A :=
  IsPullback.isoPullback (U.disp_pullback A) |>.symm

/-! ## Pullback of universes -/

/-- Pull a universe along a type. -/
protected def pullback {Γ : Ctx} (A : Γ ⟶ U.Ty) : Universe CwR where
  Tm := U.ext A
  Ty := Γ
  tp := U.disp A
  ext B := U.ext (B ≫ A)
  disp B := U.disp (B ≫ A)
  var B := (U.disp_pullback A).lift (U.disp (B ≫ A) ≫ B) (U.var (B ≫ A)) (by simp)
  disp_pullback B := IsPullback.of_bot' (U.disp_pullback (B ≫ A)) (U.disp_pullback A)
  tp_representable := disp_representable _ _

/-- Given the pullback square

  E' ----- toTm ------> Tm
  |                      |
  |                      |
  π'                    tp
  |                      |
  V                      V
  U' ----- toTy ------> Ty

  and a universe `tp : Tm ⟶ Ty`,
  construct a natural model structure on `π : E ⟶ U`,

  Γ.A -.-.- var -.-,-> E' ----- toTm ------> Tm
   |                   |                      |
   |                   |                      |
 M.disp                π'                    tp
   |                   |                      |
   V                   V                      V
  Γ ------- A -------> U' ----- toTy ------> Ty

  by pullback pasting.

  FIXME: flip these diagrams
-/
def ofIsPullback {U' E' : Ctx} {π' : E' ⟶ U'}
    {toTy : U' ⟶ U.Ty} {toTm : E' ⟶ U.Tm}
    (pb : IsPullback π' toTm toTy U.tp) :
    Universe CwR where
  Ty := U'
  Tm := E'
  tp := π'
  ext A := U.ext (A ≫ toTy)
  disp A := U.disp (A ≫ toTy)
  var A := pb.lift ((U.disp (A ≫ toTy)) ≫ A) (U.var (A ≫ toTy)) (by simp)
  disp_pullback A := IsPullback.of_bot' (U.disp_pullback (A ≫ toTy)) pb
  tp_representable := CwR.pullback_stable _ _ _ _ pb U.tp_representable

section substitution
/-! ## Substitutions -/

section
variable {Δ : Ctx} (σ : Δ ⟶ Γ) (a : Δ ⟶ U.Tm) (a_tp : σ ≫ A = a ≫ U.tp)

/--
```
Δ ⊢ σ : Γ  Γ ⊢ A type  Δ ⊢ t : A[σ]
-----------------------------------
Δ ⊢ σ.t : Γ.A
```
 ------ Δ ------ t --------¬
 |      ↓ substCons         ↓
 |     ext A ---var A---> Tm
 |      |                  |
 σ      |                  |
 |    disp A              tp
 |      |                  |
 |      V                  V
  ---> Γ ------ A ----->  Ty
-/
def substCons : Δ ⟶ U.ext A :=
  (U.disp_pullback A).lift σ a a_tp

@[functor_map (attr := reassoc (attr := simp))]
theorem substCons_disp : U.substCons A σ a a_tp ≫ U.disp A = σ := by
  simp [substCons]

@[reassoc (attr := simp)]
theorem substCons_var : U.substCons A σ a a_tp ≫ U.var A = a := by
  simp [substCons]

@[simp]
theorem comp_substCons {Θ : Ctx} (τ : Θ ⟶ Δ) :
    τ ≫ U.substCons A σ a a_tp = U.substCons A (τ ≫ σ) (τ ≫ a) (by simp [*]) := by
  apply (U.disp_pullback A).hom_ext
  · simp
  · simp

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
def substWk (A' := σ ≫ A) (eq : σ ≫ A = A' := by rfl) : U.ext A' ⟶ U.ext A :=
  U.substCons A (U.disp _ ≫ σ) (U.var _) (by simp [eq])

@[reassoc]
theorem substWk_disp (A' eq) :
    U.substWk A σ A' eq ≫ U.disp A = U.disp A' ≫ σ := by
  simp [substWk]

@[reassoc (attr := simp)]
theorem substWk_var (A' eq) :
    U.substWk A σ A' eq ≫ U.var A = U.var A' := by
  simp [substWk]

end

section
variable {A} {Δ : Ctx} (σ : Δ ⟶ U.ext A)

/--
```
Δ ⊢ σ : Γ.A
------------
Δ ⊢ ↑∘σ : Γ
```
-/
def substFst : Δ ⟶ Γ :=
  σ ≫ U.disp A

/--
```
Δ ⊢ σ : Γ.A
-------------------
Δ ⊢ v₀[σ] : A[↑∘σ]
```
-/
def substSnd (σ : Δ ⟶ U.ext A) : Δ ⟶ U.Tm :=
  σ ≫ U.var A

theorem substSnd_tp : U.substSnd σ ≫ U.tp = U.substFst σ ≫ A := by
  simp [substSnd, substFst]

end

section

variable (a : Γ ⟶ U.Tm) (a_tp : a ≫ U.tp = A)

/-- `sec` is the section of `disp A` corresponding to `a`.

  ===== Γ ------ a --------¬
 ‖      ↓ sec             V
 ‖   U.ext A -----------> U.Tm
 ‖      |                  |
 ‖      |                  |
 ‖    disp A              U.tp
 ‖      |                  |
 ‖      V                  V
  ===== Γ ------ A -----> U.Ty -/
def sec : Γ ⟶ U.ext A := U.substCons A (𝟙 Γ) a (by simp [a_tp])

@[functor_map (attr := reassoc (attr := simp))]
theorem sec_disp : U.sec A a a_tp ≫ U.disp A = 𝟙 _ := by
  simp [sec]

@[reassoc (attr := simp)]
theorem sec_var : U.sec A a a_tp ≫ U.var A = a := by
  simp [sec]

@[functor_map (attr := reassoc)]
theorem comp_sec {Δ : Ctx} (σ : Δ ⟶ Γ) (σA) (eq : σ ≫ A = σA) :
    σ ≫ U.sec A a a_tp = U.sec σA (σ ≫ a) (by simp [eq, a_tp]) ≫ U.substWk A σ _ eq := by
  apply (U.disp_pullback _).hom_ext <;> simp [sec, substWk_disp]

end

end substitution

instance : ExponentiableMorphism U.tp :=
  CwR.exponentiableMorphism U.tp_representable

/-! ## Polynomial functor on `tp`

Specializations of results from the `Poly` package to natural models. -/

@[simps] def uvPolyTp : UvPoly U.Tm U.Ty := ⟨U.tp, inferInstance⟩

def Ptp : Ctx ⥤ Ctx := U.uvPolyTp.functor

namespace PtpEquiv

variable {Γ : Ctx} {X : Ctx}

-- TODO: possibly want to remove U.uvPolyTp.equiv
-- and directly define `fst`, `snd`, etc.
/--
A map `(AB : Γ ⟶ U.Ptp.obj X)` is equivalent to a pair of maps
`A : Γ ⟶ U.Ty` and `B : U.ext (fst U.AB) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`.
`PtpEquiv.fst` is the `A` in this pair.
-/
def fst (AB : Γ ⟶ U.Ptp.obj X) : Γ ⟶ U.Ty :=
  UvPoly.Equiv.fst U.uvPolyTp X AB

/--
A map `(AB : Γ) ⟶ U.Ptp.obj X)` is equivalent to a pair of maps
`A : Γ ⟶ U.Ty` and `B : U.ext (fst U.AB) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.snd` is the `B` in this pair.
-/
def snd (AB : Γ ⟶ U.Ptp.obj X) (A := fst U AB) (eq : fst U AB = A := by rfl) : U.ext A ⟶ X :=
  UvPoly.Equiv.snd' U.uvPolyTp X AB (by rw [← fst, eq]; exact (U.disp_pullback _))

/--
A map `(AB : Γ ⟶ U.Ptp.obj X)` is equivalent to a pair of maps
`A : Γ ⟶ U.Ty` and `B : U.ext (fst U.AB) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-/
def mk (A : Γ ⟶ U.Ty) (B : U.ext A ⟶ X) : Γ ⟶ U.Ptp.obj X :=
  UvPoly.Equiv.mk' U.uvPolyTp X A (U.disp_pullback _) B

@[simp]
lemma fst_mk (A : Γ ⟶ U.Ty) (B : U.ext A ⟶ X) :
    fst U (mk U A B) = A := by
  simp [fst, mk]

@[simp]
lemma snd_mk (A : Γ ⟶ U.Ty) (B : U.ext A ⟶ X) :
    snd U (mk U A B) _ (fst_mk ..) = B := by
  dsimp only [snd, mk]
  rw! [UvPoly.Equiv.snd'_mk']

section
variable {Δ : Ctx} {σ : Δ ⟶ Γ} {AB : Γ ⟶ U.Ptp.obj X}

theorem fst_comp_left (σ : Δ ⟶ Γ) : fst U (σ ≫ AB) = σ ≫ fst U AB :=
  UvPoly.Equiv.fst_comp_left ..

theorem fst_comp_right {Y} (σ : X ⟶ Y) : fst U (AB ≫ U.Ptp.map σ) = fst U AB :=
  UvPoly.Equiv.fst_comp_right ..

theorem snd_comp_right {Y} (σ : X ⟶ Y) {A} (eq : fst U AB = A) :
    snd U (AB ≫ U.Ptp.map σ) _ (fst_comp_right U σ ▸ eq) = snd U AB _ eq ≫ σ := by
  simp only [snd, Ptp]
  rw [UvPoly.Equiv.snd'_comp_right U.uvPolyTp X Y σ AB]

theorem snd_comp_left {A} (eqA : fst U AB = A) {σA} (eqσ : σ ≫ A = σA) :
    snd U (σ ≫ AB) σA (by simp [fst_comp_left, eqA, eqσ]) =
    U.substWk _ σ _ eqσ ≫ snd U AB _ eqA := by
  have H1 : IsPullback (U.disp A) (U.var A) (UvPoly.Equiv.fst U.uvPolyTp X AB) U.uvPolyTp.p := by
    rw [← fst, eqA]; exact U.disp_pullback _
  have H2 : IsPullback (U.disp σA) (U.var σA)
    (σ ≫ UvPoly.Equiv.fst U.uvPolyTp X AB) U.uvPolyTp.p := by
    rw [← fst, eqA, eqσ]; exact U.disp_pullback _
  convert UvPoly.Equiv.snd'_comp_left U.uvPolyTp X AB H1 _ H2
  apply H1.hom_ext <;> simp [substWk]

theorem ext {AB' : Γ ⟶ U.Ptp.obj X}
    (A := fst U AB) (eq : fst U AB = A := by rfl)
    (h1 : fst U AB = fst U AB')
    (h2 : snd U AB A eq = snd U AB' A (h1 ▸ eq)) :
    AB = AB' := UvPoly.Equiv.ext' _ _ _ h1 h2

variable (AB) in
theorem eta : mk U (fst U AB) (snd U AB) = AB :=
  .symm <| ext _ _ rfl (by simp) (by simp)

end

section
variable {Δ : Ctx} {X Y : Ctx} (A : Γ ⟶ U.Ty) (B : U.ext A ⟶ X)

theorem mk_comp_left {σ : Δ ⟶ Γ} (σA) (eq : σ ≫ A = σA) :
    σ ≫ PtpEquiv.mk U A B = PtpEquiv.mk U σA (U.substWk A σ _ eq ≫ B) := by
  dsimp [PtpEquiv.mk]
  exact UvPoly.Equiv.mk'_comp_left U.uvPolyTp X A (U.disp_pullback A) B σ
    σA eq (U.disp_pullback σA)

theorem mk_comp_right (α : X ⟶ Y) :
    PtpEquiv.mk U A B ≫ U.Ptp.map α = PtpEquiv.mk U A (B ≫ α) :=
  UvPoly.Equiv.mk'_comp_right U.uvPolyTp X Y α A (U.disp_pullback A) B

@[reassoc]
theorem mk_map (α : X ⟶ Y) : mk U A B ≫ U.Ptp.map α = mk U A (B ≫ α) := by
  simp [mk, Ptp, UvPoly.Equiv.mk'_comp_right]

end

end PtpEquiv

namespace compDomEquiv

/-! ## Polynomial composition `U.tp ▸ N.tp` -/

open UvPoly

variable {U} {V : Universe CwR} {Δ : Ctx} (σ : Δ ⟶ Γ)

/-- Universal property of `compDom`, decomposition (part 1).

A map `ab : Γ ⟶ U.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`. The map `fst : Γ ⟶ U.Tm`
is the `(a : A)` in `(a : A) × (b : B a)`.
-/
def fst (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) : Γ ⟶ U.Tm :=
  ab ≫ pullback.snd V.tp (UvPoly.PartialProduct.fan U.uvPolyTp V.Ty).snd ≫
    pullback.snd (U.uvPolyTp.fstProj V.Ty) U.uvPolyTp.p

/-- Computation of `comp` (part 1).

`fst_tp` is (part 1) of the computation that
      (α, B, β, h)
     Γ ⟶ compDom
      \        |
       \       | comp
(α ≫ tp, B)    |
         \     V
           >  P_tp Ty
V.mely the first projection `α ≫ tp` agrees.
-/
theorem fst_tp (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) :
    fst ab ≫ U.tp = PtpEquiv.fst U (ab ≫ (U.uvPolyTp.compP _)) := by
  have : pullback.snd (U.uvPolyTp.fstProj V.Ty) U.tp ≫ U.tp =
    pullback.fst (U.uvPolyTp.fstProj V.Ty) U.tp ≫ U.uvPolyTp.fstProj V.Ty :=
      Eq.symm pullback.condition
  simp [PtpEquiv.fst, fst, this]
  -- rfl
  sorry

theorem comp_fst (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) (σ : Δ ⟶ Γ) :
    σ ≫ fst ab = fst (σ ≫ ab) := by simp [fst]

/-- Universal property of `compDom`, decomposition (part 2).

A map `ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `dependent : U.ext (fst V.ab ≫ U.tp) ⟶ U.Ty`
is the `B : A ⟶ Type` in `(a : A) × (b : B a)`.
Here `A` is implicit, derived by the typing of `fst`, or `(a : A)`.
-/
def dependent (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp)
    (A := fst ab ≫ U.tp) (eq : fst ab ≫ U.tp = A := by rfl) :
    U.ext A ⟶ V.Ty :=
  PtpEquiv.snd U (ab ≫ (U.uvPolyTp.compP _)) _ (by rw [← eq, fst_tp])

theorem comp_dependent (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp)
    {A} (eq1 : fst ab ≫ U.tp = A)
    {σA} (eq2 : σ ≫ A = σA) :
    substWk U _ σ _ eq2 ≫ dependent ab A eq1 =
    dependent (σ ≫ ab) σA (by simp [← comp_fst, eq1, eq2]) := by
  rw [dependent, ← PtpEquiv.snd_comp_left]; sorry

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `snd : Γ ⟶ U.Tm`
is the `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) : Γ ⟶ V.Tm :=
  ab ≫ pullback.fst V.tp (PartialProduct.fan U.uvPolyTp V.Ty).snd

theorem comp_snd (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) :
    σ ≫ snd ab = snd (σ ≫ ab) := by simp [snd]

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The equation `snd_tp` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_tp (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp)
    {A} (eq : fst ab ≫ U.tp = A) :
    snd ab ≫ V.tp = U.sec _ (fst ab) eq ≫ dependent ab A eq := by
  simp [snd, pullback.condition, dependent, PtpEquiv.snd, Equiv.snd'_eq]
  simp only [← Category.assoc]; congr! 1
  apply pullback.hom_ext <;> simp [fst, UvPoly.compP]

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : Γ ⟶ U.Tm) {A} (eq : α ≫ U.tp = A) (B : U.ext A ⟶ V.Ty) (β : Γ ⟶ V.Tm)
    (h : β ≫ V.tp = U.sec _ α eq ≫ B) : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp := by
  refine pullback.lift β (pullback.lift (PtpEquiv.mk _ A B) α ?_) ?_
  · simp [← Equiv.fst_eq, ← PtpEquiv.fst.eq_def, eq]
  · simp [h]
    conv_lhs => arg 2; exact
      Equiv.snd'_mk' U.uvPolyTp V.Ty A _ B
        |>.symm.trans <| Equiv.snd'_eq U.uvPolyTp V.Ty (PtpEquiv.mk U A B) _
    simp only [← Category.assoc]; congr! 1
    apply pullback.hom_ext <;> simp

@[simp]
theorem fst_mk (α : Γ ⟶ U.Tm) {A} (eq : α ≫ U.tp = A) (B : (U.ext A) ⟶ V.Ty) (β : (Γ) ⟶ V.Tm)
    (h : β ≫ V.tp = U.sec _ α eq ≫ B) : fst (mk α eq B β h) = α := by
  simp [mk, fst]

@[simp]
theorem dependent_mk (α : (Γ) ⟶ U.Tm) {A} (eq : α ≫ U.tp = A)
    (B : (U.ext A) ⟶ V.Ty) (β : (Γ) ⟶ V.Tm)
    (h : β ≫ V.tp = (U.sec _ α eq) ≫ B) :
    dependent (mk α eq B β h) A (by simp [fst_mk, eq]) = B := by
  simp [mk, dependent, UvPoly.compP]
  convert PtpEquiv.snd_mk U A B using 2
  slice_lhs 1 2 => apply pullback.lift_snd
  simp

@[simp]
theorem snd_mk (α : (Γ) ⟶ U.Tm) {A} (eq : α ≫ U.tp = A) (B : (U.ext A) ⟶ V.Ty) (β : (Γ) ⟶ V.Tm)
    (h : β ≫ V.tp = (U.sec _ α eq) ≫ B) : snd (mk α eq B β h) = β := by
  simp [mk, snd]

theorem ext {ab₁ ab₂ : (Γ) ⟶ U.uvPolyTp.compDom V.uvPolyTp}
    {A} (eq : fst ab₁ ≫ U.tp = A)
    (h1 : fst ab₁ = fst ab₂)
    (h2 : dependent ab₁ A eq = dependent ab₂ A (h1 ▸ eq))
    (h3 : snd ab₁ = snd ab₂) : ab₁ = ab₂ := by
  -- refine pullback.hom_ext h3 (pullback.hom_ext ?_ h1)
  -- simp only [dependent, PtpEquiv.snd] at h2
  -- generalize_proofs _ _ H at h2
  -- refine Equiv.ext' U.uvPolyTp V.Ty H ?_ h2
  -- simp [Equiv.fst, pullback.condition]
  -- simp only [← Category.assoc]; congr 1
  sorry

theorem comp_mk
    (α : Γ ⟶ U.Tm) {A} (e1 : α ≫ U.tp = A)
    (B : U.ext A ⟶ V.Ty)
    (β : Γ ⟶ V.Tm)
    (e2 : β ≫ V.tp = U.sec A α e1 ≫ B)
    (σ : Δ ⟶ Γ) {σA} (e3 : σ ≫ A = σA) :
    (σ) ≫ mk α e1 B β e2 =
    mk (σ ≫ α) (by simp [e1, e3])
      ((U.substWk A σ _ e3) ≫ B) ((σ) ≫ β)
      (by simp [e2]; rw [comp_sec_assoc]) := by
  apply ext (A := σA) (by simp [← comp_fst, e1, e3]) <;> simp [← comp_fst, ← comp_snd]
  rw [← comp_dependent, dependent_mk]

theorem eta (ab : (Γ) ⟶ U.uvPolyTp.compDom V.uvPolyTp)
    {A} (eq : fst ab ≫ U.tp = A) :
    mk (fst ab) eq (dependent ab A eq) (snd ab) (snd_tp ab eq) = ab := by
  symm; apply ext (eq := eq) <;> simp

end compDomEquiv
end Universe

end RepMap

end CategoryTheory

#exit


/-! ## Pi and Sigma types -/

set_option linter.dupNamespace false in
protected structure Pi where
  Pi : U.Ptp.obj U.Ty ⟶ U.Ty
  lam : U.Ptp.obj U.Tm ⟶ U.Tm
  Pi_pullback : IsPullback lam (U.Ptp.map U.tp) U.tp Pi

protected structure Sigma where
  Sig : U.Ptp.obj U.Ty ⟶ U.Ty
  pair : UvPoly.compDom (uvPolyTp U. (uvPolyTp U. ⟶ U.Tm
  Sig_pullback : IsPullback pair ((uvPolyTp U..compP (uvPolyTp U.) U.tp Sig

/--
NaturalU.del.IdIntro consists of the following commutative square
       refl
U.Tm ------> U.Tm
 |            |
 |            |
diag         U.tp
 |            |
 |            |
 V            V
 k --------> U.Ty
      Id

where `K` (for "Kernel" of `tp`) is a chosen pullback for the square
       k1
 k ---------> Tm
 |             |
 |             |
 k2            | tp
 |             |
 V             V
Tm ----------> Ty
        tp
and `diag` denotes the diagonal into the pullback `K`.

We require a choice of pullback because,
although all pullbacks exist in presheaf categories,
when constructing a model it is convenient to know
that `K` is some specific construction on-the-nose.
-/
structure IdIntro where
  k : Psh Ctx
  k1 : k ⟶ U.Tm
  k2 : k ⟶ U.Tm
  isKernelPair : IsKernelPair U.tp k1 k2
  Id : k ⟶ U.Ty
  refl : U.Tm ⟶ U.Tm
  refl_tp : refl ≫ U.tp =
    (IsPullback.lift isKernelPair (𝟙 U.Tm) (𝟙 U.Tm) (by simp)) ≫ Id

namespace IdIntro

variable {U. (idIntro : IdIntro U. {Γ : Ctx}

/-- The introduction rule for identity types.
To minimize the number of arguments, we infer the type from the terms. -/
def mkId (a0 a1 : y(Γ) ⟶ U.Tm)
    (a0_tp_eq_a1_tp : a0 ≫ U.tp = a1 ≫ U.tp) :
    y(Γ) ⟶ U.Ty :=
  idIntro.isKernelPair.lift a1 a0 (by rw [a0_tp_eq_a1_tp]) ≫ idIntro.Id

theorem comp_mkId {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (a0 a1 : y(Γ) ⟶ U.Tm) (eq : a0 ≫ U.tp = a1 ≫ U.tp) :
    ym(σ) ≫ mkId idIntro a0 a1 eq =
      mkId idIntro (ym(σ) ≫ a0) (ym(σ) ≫ a1) (by simp [eq]) := by
  simp [mkId]; rw [← Category.assoc]; congr 1
  apply idIntro.isKernelPair.hom_ext <;> simp

def mkRefl (a : y(Γ) ⟶ U.Tm) : y(Γ) ⟶ U.Tm :=
  a ≫ idIntro.refl

theorem comp_mkRefl {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ U.Tm) :
    ym(σ) ≫ idIntro.mkRefl a = idIntro.mkRefl (ym(σ) ≫ a) :=
  rfl

@[simp]
theorem mkRefl_tp (a : y(Γ) ⟶ U.Tm) :
    idIntro.mkRefl a ≫ U.tp = idIntro.mkId a a rfl := by
  simp only [mkRefl, Category.assoc, idIntro.refl_tp, mkId]
  rw [← Category.assoc]
  congr 1
  apply idIntro.isKernelPair.hom_ext <;> simp

/-- The context appearing in the motive for identity elimination `J`
  Γ ⊢ A
  Γ ⊢ a : A
  Γ.(x:A).(h:Id(A,a,x)) ⊢ M
  ...
-/
def motiveCtx (a : y(Γ) ⟶ U.Tm) : Ctx :=
  U.ext (idIntro.mkId (ym(U.disp (a ≫ U.tp)) ≫ a) (U.var _) (by simp))

def motiveSubst {Γ Δ} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ U.Tm) :
    motiveCtx idIntro (ym(σ) ≫ a) ⟶ motiveCtx idIntro a := by
  refine substWk _ (substWk _ σ _ _ (by simp)) _ _ ?_
  simp [comp_mkId]; congr 1; simp only [← Functor.map_comp_assoc, substWk_disp]

/-- The substitution `(a,refl)` appearing in identity elimination `J`
  `(a,refl) : y(Γ) ⟶ y(Γ.(x:A).(h:Id(A,a,x)))`
  so that we can write
  `Γ ⊢ r : U.a,refl)`
-/
def reflSubst (a : y(Γ) ⟶ U.Tm) : Γ ⟶ idIntro.motiveCtx a :=
  U.substCons (U.substCons (𝟙 Γ) (a ≫ U.tp) a (by simp)) _ (idIntro.mkRefl a) (by
    simp only [mkRefl_tp, mkId, ← Category.assoc]
    congr 1
    apply idIntro.isKernelPair.hom_ext <;> simp)

@[reassoc]
theorem comp_reflSubst' {Γ Δ} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ U.Tm) :
    ym(σ) ≫ ym(idIntro.reflSubst a) =
    ym(idIntro.reflSubst (ym(σ) ≫ a)) ≫ ym(idIntro.motiveSubst σ a) := by
  apply (U.disp_pullback _).hom_ext <;> simp [reflSubst, motiveSubst, mkRefl]
  apply (U.disp_pullback _).hom_ext <;> simp [substWk]

@[simp, reassoc]
lemma comp_reflSubst (a : y(Γ) ⟶ U.Tm) {Δ} (σ : Δ ⟶ Γ) :
    reflSubst idIntro (ym(σ) ≫ a) ≫ idIntro.motiveSubst σ a = σ ≫ reflSubst idIntro a := by
  apply Yoneda.fullyFaithful.map_injective
  simp [Functor.map_comp, comp_reflSubst']

end IdIntro

/-- The full structure interpreting the natural model semantics for identity types
requires an `IdIntro` and an elimination rule `j` which satisfies a typing rule `j_tp`
and a β-rule `reflSubst_j`.
There is an equivalent formulation of these extra conditions later in `Id'`
that uses the language of polynomial endofunctors.

Note that the universe/model `N` for the motive `C` is different from the universe `U. that the
identity type lives in.
-/
protected structure Id (N : NaturalU.del Ctx) (i : IdIntro U. where
  j {Γ} (a : y(Γ) ⟶ U.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) :
    y(i.motiveCtx a) ⟶ N.Tm
  j_tp {Γ} (a : y(Γ) ⟶ U.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) : j a C r r_tp ≫ N.tp = C
  comp_j {Γ Δ} (σ : Δ ⟶ Γ)
    (a : y(Γ) ⟶ U.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) :
    ym(i.motiveSubst σ _) ≫ j a C r r_tp =
    j (ym(σ) ≫ a) (ym(i.motiveSubst σ _) ≫ C) (ym(σ) ≫ r) (by
      simp [r_tp, IdIntro.comp_reflSubst'_assoc])
  reflSubst_j {Γ} (a : y(Γ) ⟶ U.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) :
    ym(i.reflSubst a) ≫ j a C r r_tp = r

namespace Id

variable {U. {N : NaturalU.del Ctx} {ii : U.IdIntro} (i : U.Id N ii) {Γ : Ctx} (a : y(Γ) ⟶ U.Tm)
  (C : y(ii.motiveCtx a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
  (r_tp : r ≫ N.tp = ym(ii.reflSubst a) ≫ C) (b : y(Γ) ⟶ U.Tm) (b_tp : b ≫ U.tp = a ≫ U.tp)
  (h : y(Γ) ⟶ U.Tm) (h_tp : h ≫ U.tp = ii.isKernelPair.lift b a (by aesop) ≫ ii.Id)

def endPtSubst : Γ ⟶ ii.motiveCtx a :=
  U.substCons (U.substCons (𝟙 _) _ b (by aesop)) _ h (by
    simp only [h_tp, IdIntro.mkId, ← Category.assoc]
    congr 1
    apply ii.isKernelPair.hom_ext
    · simp
    · simp)

/-- The elimination rule for identity types, now with the parameters as explicit terms.
  `Γ ⊢ A` is the type with a term `Γ ⊢ a : A`.
  `Γ (y : A) (p : Id(A,a,y)) ⊢ C` is the motive for the elimination.
  `Γ ⊢ b : A` is a second term in `A` and `Γ ⊢ h : Id(A,a,b)` is a path from `a` to `b`.
  Then `Γ ⊢ mkJ' : C [b/y,h/p]` is a term of the motive with `b` and `h` substituted
-/
def mkJ : y(Γ) ⟶ N.Tm :=
  ym(endPtSubst a b b_tp h h_tp) ≫ i.j a C r r_tp

/-- Typing for elimination rule `J` -/
lemma mkJ_tp : i.mkJ a C r r_tp b b_tp h h_tp ≫ N.tp = ym(endPtSubst a b b_tp h h_tp) ≫ C := by
  rw [mkJ, Category.assoc, i.j_tp]

/-- β rule for identity types. Substituting `J` with `refl` gives the user-supplied value `r` -/
lemma mkJ_refl : i.mkJ a C r r_tp a rfl (ii.mkRefl a) (by aesop) = r :=
  calc ym(endPtSubst a a _ (ii.mkRefl a) _) ≫ i.j a C r r_tp
    _ = ym(ii.reflSubst a) ≫ i.j a C r r_tp := rfl
    _ = r := by rw [i.reflSubst_j]

end Id

/--
`NaturalU.delBase.IdElimBase` extends the structure `NaturalU.delBase.IdIntro`
with a chosen pullback of `Id`
       i1
 i --------> U.Tm
 |            |
 |            |
i2           U.tp
 |            |
 V            V
 k --------> U.Ty
      Id

Again, we always have a pullback,
but when we construct a natural model,
this may not be definitionally equal to the pullbacks we construct,
for example using context extension.
-/
structure IdElimBase extends IdIntro U.where
  i : Psh Ctx
  i1 : i ⟶ U.Tm
  i2 : i ⟶ k
  i_isPullback : IsPullback i1 i2 U.tp Id

namespace IdElimBase
variable {U. (idElimBase : IdElimBase U.

/-- The comparison map `U.tm ⟶ i` induced by the pullback universal property of `i`.

          refl
 U.Tm --------->
           i1
 |   i --------> U.Tm
 |   |            |
diag |            |
 |  i2           U.tp
 |   |            |
 |   V            V
 V   k --------> U.Ty
          Id
-/
def comparison : U.Tm ⟶ idElimBase.i :=
  idElimBase.i_isPullback.lift idElimBase.refl
  (IsPullback.lift idElimBase.isKernelPair (𝟙 U.Tm) (𝟙 U.Tm) (by simp))
  idElimBase.refl_tp

@[simp]
lemma comparison_comp_i1 : idElimBase.comparison ≫ idElimBase.i1 = idElimBase.refl := by
  simp [comparison]

@[simp, reassoc]
lemma comparison_comp_i2_comp_k1 : idElimBase.comparison ≫ idElimBase.i2 ≫ idElimBase.k1 =
    𝟙 _ := by
  simp [comparison]

@[simp, reassoc]
lemma comparison_comp_i2_comp_k2 : idElimBase.comparison ≫ idElimBase.i2 ≫ idElimBase.k2 =
    𝟙 _ := by
  simp [comparison]

/-- `i` over `Tm` can be informally thought of as the context extension
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty) (a : A)`
which is defined by the composition of (maps informally thought of as) context extensions
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty).(a b : A) ->> (A : Ty).(a : A)`
This is the signature for a polynomial functor `iUvPoly` on the presheaf category `Psh Ctx`.
-/
@[simps] def iUvPoly : UvPoly idElimBase.i U.Tm := ⟨idElimBase.i2 ≫ idElimBase.k2, inferInstance⟩

/-- The functor part of the polynomial endofunctor `iOverUvPoly` -/
abbrev iFunctor : Psh Ctx ⥤ Psh Ctx := idElimBase.iUvPoly.functor

/-- Consider the comparison map `comparison : Tm ⟶ i` in the slice over `Tm`.
Then the contravariant action `UVPoly.verticalNatTrans` of taking `UvPoly` on a slice
results in a natural transformation `P_iOver ⟶ P_(𝟙 Tm)`
between the polynomial endofunctors `iUvPoly` and `UvPoly.id U.Tm` respectively.
  comparison
Tm ----> i
 \      /
 𝟙\    /i2 ≫ k2
   \  /
    VV
    Tm
-/
def verticalNatTrans : idElimBase.iFunctor ⟶ (UvPoly.id U.Tm).functor :=
    UvPoly.verticalNatTrans (UvPoly.id U.Tm) idElimBase.iUvPoly
  idElimBase.comparison (by simp [iUvPoly])

section reflCase

variable (i : IdIntro U. {N : NaturalU.del Ctx}

variable {Γ : Ctx} (a : y(Γ) ⟶ U.Tm) (r : y(Γ) ⟶ N.Tm)

lemma reflCase_aux : IsPullback (𝟙 y(Γ)) a a (UvPoly.id U.Tm).p :=
  have : IsIso (UvPoly.id U.Tm).p := by simp; infer_instance
  IsPullback.of_horiz_isIso (by simp)

/-- The variable `r` witnesses the motive for the case `refl`,
This gives a map `(a,r) : Γ ⟶ P_𝟙Tm Tm ≅ Tm × Tm` where
```
    fst ≫ r
N.Tm <--   Γ  --------> Tm
    <      ‖            ‖
     \     ‖   (pb)     ‖ 𝟙_Tm
    r \    ‖            ‖
       \   ‖            ‖
        \  Γ  --------> Tm
                 a
```
-/
def reflCase : y(Γ) ⟶ (UvPoly.id U.Tm).functor.obj N.Tm :=
  UvPoly.Equiv.mk' (UvPoly.id U.Tm) N.Tm a (R := y(Γ)) (f := 𝟙 _) (g := a)
  (reflCase_aux a) r
-- TODO: consider generalizing
-- TODO: consider showing UvPoly on identity `(P_𝟙_Y X)` is isomorphic to product `Y × X`

end reflCase

open IdElimBase IdIntro

section Equiv

variable {Γ : Ctx} {X : Psh Ctx}

section
variable (a : y(Γ) ⟶ U.Tm)
/-
In the following lemmas we build the following diagram of pullbacks,
where `pullback` is the pullback of `i₂ ≫ k₂` along `a` given by `HasPullback`.
  X
  Λ
  |
  | x
  |
 y(Γ.a≫tp.Id(...)) ------> i ------> Tm
  |                        |         |
  |                        | i₂      V
  |                        |         Ty
  V                        V
 y(Γ.a≫tp) ------------>   k ------> Tm
  |                        |    k₁   |
  |                        |k₂       |tp
  |                        |         |
  |                        V         V
 y(Γ) ---------------->   Tm -----> Ty
               a               tp
-/

def toK : y(U.ext (a ≫ U.tp)) ⟶ idElimBase.k :=
  idElimBase.isKernelPair.lift (U.var _) (ym(U.disp _) ≫ a) (by simp)

lemma toK_comp_k1 : idElimBase.toK a ≫ idElimBase.k1 = U.var _ := by simp [toK]

lemma toK_comp_left {Δ} (σ : Δ ⟶ Γ) : toK idElimBase (ym(σ) ≫ a) =
    ym(U.substWk σ (a ≫ U.tp)) ≫ toK idElimBase a := by
  dsimp [toK]
  apply idElimBase.isKernelPair.hom_ext
  · rw! [Category.assoc]
    simp
  · simp only [IsKernelPair.lift_snd, Category.assoc]
    slice_rhs 1 2 => rw [← Functor.map_comp, substWk_disp]
    rw! [Category.assoc]
    simp

lemma ext_a_tp_isPullback : IsPullback (toK idElimBase a) ym(U.disp _)
    idElimBase.k2 a :=
  IsPullback.of_right' (U.disp_pullback _) idElimBase.isKernelPair

def toI : y(idElimBase.motiveCtx a) ⟶ idElimBase.i :=
  idElimBase.i_isPullback.lift (U.var _) (ym(U.disp _) ≫ toK idElimBase a)
  (by rw [(U.disp_pullback _).w]; simp [IdIntro.mkId, toK])

lemma toI_comp_i1 : idElimBase.toI a ≫ idElimBase.i1 = U.var _ := by simp [toI]

lemma toI_comp_i2 : idElimBase.toI a ≫ idElimBase.i2 = ym(U.disp _) ≫ idElimBase.toK a :=
  by simp [toI]

lemma toI_comp_left {Δ} (σ : Δ ⟶ Γ) : toI idElimBase (ym(σ) ≫ a) =
    ym(idElimBase.motiveSubst σ a) ≫ toI idElimBase a := by
  dsimp [toI]
  apply idElimBase.i_isPullback.hom_ext
  · simp [motiveSubst]
  · simp [toK_comp_left, motiveSubst, substWk, substCons]
    rfl

theorem motiveCtx_isPullback :
    IsPullback (toI idElimBase a) ym(U.disp _) idElimBase.i2 (toK idElimBase a) :=
  IsPullback.of_right' (U.disp_pullback _) idElimBase.i_isPullback

theorem motiveCtx_isPullback' :
    IsPullback (toI idElimBase a) (ym(U.disp (idElimBase.mkId (ym(U.disp (a ≫ U.tp)) ≫ a)
      (U.var (a ≫ U.tp)) (by simp))) ≫ ym(U.disp (a ≫ U.tp))) (iUvPoly idElimBase).p a :=
  IsPullback.paste_vert (idElimBase.motiveCtx_isPullback a)
    (idElimBase.ext_a_tp_isPullback a)

def equivU. (x : y(idElimBase.motiveCtx a) ⟶ X) : y(Γ) ⟶ idElimBase.iFunctor.obj X :=
  UvPoly.Equiv.mk' idElimBase.iUvPoly X a (idElimBase.motiveCtx_isPullback' a).flip x

def equivFst (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    y(Γ) ⟶ U.Tm :=
  UvPoly.Equiv.fst idElimBase.iUvPoly X pair

lemma equivFst_comp_left (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X)
    {Δ} (σ : Δ ⟶ Γ) :
    idElimBase.equivFst (ym(σ) ≫ pair) = ym(σ) ≫ idElimBase.equivFst pair := by
  dsimp [equivFst]
  rw [UvPoly.Equiv.fst_comp_left]

def equivSnd (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    y(idElimBase.motiveCtx (equivFst idElimBase pair)) ⟶ X :=
  UvPoly.Equiv.snd' idElimBase.iUvPoly X pair (idElimBase.motiveCtx_isPullback' _).flip

lemma equivSnd_comp_left (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X)
    {Δ} (σ : Δ ⟶ Γ) :
    idElimBase.equivSnd (ym(σ) ≫ pair) =
    ym(idElimBase.motiveSubst σ _) ≫ idElimBase.equivSnd pair := by
  dsimp only [equivSnd]
  let a := idElimBase.equivFst pair
  have H : IsPullback (idElimBase.toI a)
    (ym(U.disp (idElimBase.mkId (ym(U.disp (a ≫ U.tp)) ≫ a) (U.var (a ≫ U.tp)) _)) ≫
    ym(U.disp (a ≫ U.tp))) idElimBase.iUvPoly.p
    (UvPoly.Equiv.fst idElimBase.iUvPoly X pair) := (motiveCtx_isPullback' _ _)
  have H' : IsPullback (ym(U.disp
      (idElimBase.mkId (ym(U.disp (idElimBase.equivFst (ym(σ) ≫ pair) ≫ U.tp)) ≫
      idElimBase.equivFst (ym(σ) ≫ pair))
      (U.var (idElimBase.equivFst (ym(σ) ≫ pair) ≫ U.tp)) _)) ≫
      ym(U.disp (idElimBase.equivFst (ym(σ) ≫ pair) ≫ U.tp)))
      (idElimBase.toI (idElimBase.equivFst (ym(σ) ≫ pair)))
      (ym(σ) ≫ UvPoly.Equiv.fst idElimBase.iUvPoly X pair)
      idElimBase.iUvPoly.p :=
    (motiveCtx_isPullback' _ _).flip
  rw [UvPoly.Equiv.snd'_comp_left (H := H.flip) (H' := H')]
  · congr 1
    have h : idElimBase.toI (idElimBase.equivFst (ym(σ) ≫ pair)) =
        ym(idElimBase.motiveSubst σ (idElimBase.equivFst pair)) ≫ idElimBase.toI a :=
      idElimBase.toI_comp_left a σ
    apply (IsPullback.flip H).hom_ext
    · simp only [iUvPoly_p, Category.assoc, IsPullback.lift_fst]
      simp [motiveSubst, substWk, substCons, a]; rfl
    · apply idElimBase.i_isPullback.hom_ext
      · simp [IsPullback.lift_snd, h]
      · apply idElimBase.isKernelPair.hom_ext
        · simp [IsPullback.lift_snd, h]
        · simp only [iUvPoly_p, IsPullback.lift_snd, IdElimBase.toI_comp_i2, ← h, toI_comp_i2]

lemma equivFst_verticalNatTrans_app {Γ : Ctx} {X : Psh Ctx}
    (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    idElimBase.equivFst pair = UvPoly.Equiv.fst (UvPoly.id U.Tm) X
    (pair ≫ idElimBase.verticalNatTrans.app X) := by
  dsimp [equivFst, verticalNatTrans]
  rw [← UvPoly.fst_verticalNatTrans_app]

lemma equivSnd_verticalNatTrans_app {Γ : Ctx} {X : Psh Ctx}
    (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    UvPoly.Equiv.snd' (UvPoly.id U.Tm) X (pair ≫ idElimBase.verticalNatTrans.app X)
      (R := y(Γ)) (f := 𝟙 _) (g := idElimBase.equivFst pair) (by
        convert reflCase_aux (idElimBase.equivFst pair)
        rw [equivFst_verticalNatTrans_app]) =
      ym(idElimBase.reflSubst (idElimBase.equivFst pair)) ≫
      idElimBase.equivSnd pair :=
  calc _
  _ = _ ≫ idElimBase.equivSnd pair := by
    dsimp [equivSnd, verticalNatTrans]
    rw [UvPoly.snd'_verticalNatTrans_app (UvPoly.id U.Tm) idElimBase.iUvPoly
      (idElimBase.comparison) _ _ pair _]
    apply reflCase_aux (idElimBase.equivFst pair)
  _ = _ := by
    congr 1
    apply (U.disp_pullback _).hom_ext
    · conv => lhs; rw [← toI_comp_i1]
      simp [reflSubst, comparison, mkRefl]
    · apply (U.disp_pullback _).hom_ext
      · slice_lhs 3 4 => rw [← idElimBase.toK_comp_k1]
        slice_lhs 2 3 => rw [← idElimBase.toI_comp_i2]
        simp [reflSubst]
      · simp [reflSubst]

lemma equivU._comp_verticalNatTrans_app {Γ : Ctx} {X : Psh Ctx} (a : y(Γ) ⟶ U.Tm)
    (x : y(idElimBase.motiveCtx a) ⟶ X) :
    idElimBase.equivU. a x ≫ (idElimBase.verticalNatTrans).app X =
    UvPoly.Equiv.mk' (UvPoly.id U.Tm) X a (R := y(Γ)) (f := 𝟙 _) (g := a)
    (reflCase_aux a) (ym(idElimBase.reflSubst a) ≫ x) := by
  dsimp only [equivU., verticalNatTrans]
  rw [UvPoly.mk'_comp_verticalNatTrans_app (R' := y(Γ)) (f' := 𝟙 _) (g' := a)
    (H' := reflCase_aux a)]
  congr 2
  apply (U.disp_pullback _).hom_ext
  · conv => lhs; rw [← toI_comp_i1]
    simp [reflSubst, comparison, mkRefl]
  · apply (U.disp_pullback _).hom_ext
    · slice_lhs 3 4 => rw [← idElimBase.toK_comp_k1]
      slice_lhs 2 3 => rw [← idElimBase.toI_comp_i2]
      simp [reflSubst]
    · simp [reflSubst]

end

end Equiv

end IdElimBase

/-- In the high-tech formulation by Richard Garner and Steve Awodey:
The full structure interpreting the natural model semantics for identity types
requires an `IdIntro`,
(and `IdElimBase` which can be generated by pullback in the presheaf category,)
and that the following commutative square generated by
`IdBaseComparison.verticalNatTrans` is a weak pullback.

```
  verticalNatTrans.app Tm
iFunctor Tm --------> P_𝟙Tm Tm
  |                    |
  |                    |
iFunctor tp           P_𝟙Tm tp
  |                    |
  |                    |
  V                    V
iFunctor Ty --------> P_𝟙Tm Ty
  verticalNatTrans.app Ty
```

This can be thought of as saying the following.
Fix `A : Ty` and `a : A` - we are working in the slice over `U.Tm`.
For any context `Γ`, any map `(a, r) : Γ → P_𝟙Tm Tm`
and `(a, C) : Γ ⟶ iFunctor Ty` such that `r ≫ U.tp = C[x/y, refl_x/p]`,
there is a map `(a,c) : Γ ⟶ iFunctor Tm` such that `c ≫ U.tp = C` and `c[a/y, refl_a/p] = r`.
Here we are thinking
  `Γ (y : A) (p : A) ⊢ C : Ty`
  `Γ ⊢ r : C[a/y, refl_a/p]`
  `Γ (y : A) (p : A) ⊢ c : Ty`
This witnesses the elimination principle for identity types since
we can take `J (y.p.C;x.r) := c`.
-/
structure Id' (N : NaturalU.del Ctx) extends IdElimBase U.where
  weakPullback : WeakPullback
    (toIdElimBase.verticalNatTrans.app N.Tm)
    (toIdElimBase.iFunctor.map N.tp)
    ((UvPoly.id U.Tm).functor.map N.tp)
    (toIdElimBase.verticalNatTrans.app N.Ty)

namespace Id'

variable {U. {N : NaturalU.del Ctx} (i : Id' U.N)

variable {Γ Δ : Ctx} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ U.Tm)
  (C : y(i.motiveCtx a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
  (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C)

open IdElimBase IdIntro

lemma reflCase_aux : IsPullback (𝟙 y(Γ)) a a (UvPoly.id U.Tm).p :=
  have : IsIso (UvPoly.id U.Tm).p := by simp; infer_instance
  IsPullback.of_horiz_isIso (by simp)

/-- The variable `r` witnesses the motive for the case `refl`,
This gives a map `(a,r) : Γ ⟶ P_𝟙Tm Tm ≅ Tm × Tm` where
```
    fst ≫ r
Tm <--   Γ  --------> Tm
  <      ‖            ‖
   \     ‖   (pb)     ‖ 𝟙_Tm
  r \    ‖            ‖
     \   ‖            ‖
      \  Γ  --------> Tm
              a
```
-/
def reflCase : y(Γ) ⟶ (UvPoly.id U.Tm).functor.obj N.Tm :=
  UvPoly.Equiv.mk' (UvPoly.id U.Tm) N.Tm a (R := y(Γ)) (f := 𝟙 _) (g := a)
  (reflCase_aux a) r
-- TODO: consider generalizing
-- TODO: consider showing UvPoly on identity `(P_𝟙_Y X)` is isomorphic to product `Y × X`

/-- The variable `C` is the motive for elimination,
This gives a map `(a, C) : Γ ⟶ iFunctor Ty`
```
    C
Ty <-- y(motiveCtx) ----> i
             |            |
             |            | i2 ≫ k2
             |            |
             V            V
             Γ  --------> Tm
                  a
```
-/
abbrev motive : y(Γ) ⟶ i.iFunctor.obj N.Ty :=
  i.equivU. a C

lemma motive_comp_left : ym(σ) ≫ i.motive a C =
    i.motive (ym(σ) ≫ a) (ym(i.motiveSubst σ a) ≫ C) := by
  dsimp [motive, equivU.]
  rw [UvPoly.Equiv.mk'_comp_left (iUvPoly i.toIdElimBase) _ a
    (i.motiveCtx_isPullback' a).flip C ym(σ) _ rfl (i.motiveCtx_isPullback' _).flip]
  congr 2
  simp only [Functor.map_comp, iUvPoly_p, Category.assoc, motiveSubst, substWk, substCons,
    Functor.FullyFaithful.map_preimage]
  apply (U.disp_pullback _).hom_ext <;> simp only [IsPullback.lift_fst, IsPullback.lift_snd]
  · simp [← toI_comp_i1]
  · apply (U.disp_pullback _).hom_ext <;> simp
    · slice_lhs 3 4 => rw [← i.toK_comp_k1]
      slice_rhs 2 3 => rw [← i.toK_comp_k1]
      slice_lhs 2 3 => rw [← i.toI_comp_i2]
      slice_rhs 1 2 => rw [← i.toI_comp_i2]
      simp

def lift : y(Γ) ⟶ i.iFunctor.obj N.Tm :=
  i.weakPullback.coherentLift (reflCase a r) (motive i a C) (by
    dsimp only [motive, equivU., verticalNatTrans, reflCase]
    rw [UvPoly.mk'_comp_verticalNatTrans_app (UvPoly.id U.Tm) i.iUvPoly i.comparison
      _ N.Ty a (i.motiveCtx_isPullback' a).flip C (reflCase_aux a),
      UvPoly.Equiv.mk'_comp_right, r_tp, reflSubst]
    congr
    apply (U.disp_pullback _).hom_ext
    · conv => right; rw [← toI_comp_i1]
      simp [mkRefl, comparison]
    · apply (U.disp_pullback _).hom_ext
      · slice_rhs 3 4 => rw [← i.toK_comp_k1]
        slice_rhs 2 3 => rw [← toI_comp_i2]
        simp
      · simp)

lemma lift_comp_left {Δ} (σ : Δ ⟶ Γ) : i.lift (ym(σ) ≫ a) (ym(i.motiveSubst σ a) ≫ C)
    (ym(σ) ≫ r) (by simp [r_tp, comp_reflSubst'_assoc]) =
    ym(σ) ≫ i.lift a C r r_tp := by
  dsimp [lift]
  rw [WeakPullback.coherentLift_comp_left]
  congr 1
  · dsimp [reflCase]
    rw [UvPoly.Equiv.mk'_comp_left (UvPoly.id U.Tm) N.Tm a (reflCase_aux a) r ym(σ) _ rfl
      (reflCase_aux (ym(σ) ≫ a))]
    congr 2
    apply (reflCase_aux a).hom_ext
    · simp only [IsPullback.lift_fst]
      simp
    · simp
  · rw [motive_comp_left]

lemma equivFst_lift_eq : i.equivFst (i.lift a C r r_tp) = a :=
  calc i.equivFst (i.lift a C r r_tp)
  _ = i.equivFst (i.lift a C r r_tp ≫ i.iFunctor.map N.tp) := by
    dsimp [IdElimBase.equivFst]
    rw [UvPoly.Equiv.fst_comp_right]
  _ = _ := by
    dsimp [lift, motive, IdElimBase.equivFst, IdElimBase.equivU.]
    rw [WeakPullback.coherentLift_snd, UvPoly.Equiv.fst_mk']

/-- The elimination rule for identity types.
  `Γ ⊢ A` is the type with a term `Γ ⊢ a : A`.
  `Γ (y : A) (h : Id(A,a,y)) ⊢ C` is the motive for the elimination.
  Then we obtain a section of the motive
  `Γ (y : A) (h : Id(A,a,y)) ⊢ mkJ : A`
-/
def j : y(i.motiveCtx a) ⟶ N.Tm :=
  eqToHom (by rw [equivFst_lift_eq]) ≫ i.equivSnd (i.lift a C r r_tp)

/-- Typing for elimination rule `J` -/
lemma j_tp : j i a C r r_tp ≫ N.tp = C := by
  simp only [j, Category.assoc, IdElimBase.equivSnd, ← UvPoly.Equiv.snd'_comp_right]
  rw! [WeakPullback.coherentLift_snd]
  simp only [IdElimBase.equivU.]
  rw! [equivFst_lift_eq]
  simp

lemma comp_j : ym(i.motiveSubst σ _) ≫ j i a C r r_tp =
    j i (ym(σ) ≫ a) (ym(i.motiveSubst σ _) ≫ C) (ym(σ) ≫ r) (by
      simp [r_tp, IdIntro.comp_reflSubst'_assoc]) := by
  simp only [j]
  conv => rhs; rw! [i.lift_comp_left a C r r_tp]
  rw [i.equivSnd_comp_left]
  simp only [← Category.assoc]
  congr 1
  simp [← heq_eq_eq]
  rw [equivFst_lift_eq]

/-- β rule for identity types. Substituting `J` with `refl` gives the user-supplied value `r` -/
lemma reflSubst_j : ym(i.reflSubst a) ≫ j i a C r r_tp = r := by
  have h := i.equivSnd_verticalNatTrans_app (i.lift a C r r_tp)
  rw! [i.weakPullback.coherentLift_fst] at h
  unfold reflCase at h
  rw [UvPoly.Equiv.snd'_eq_snd', UvPoly.Equiv.snd'_mk', ← Iso.eq_inv_comp] at h
  conv => right; rw [h]
  simp only [j, ← Category.assoc, UvPoly.Equiv.fst_mk', UvPoly.id_p]
  congr 1
  have pb : IsPullback (𝟙 _) a a (𝟙 _) := IsPullback.of_id_fst
  have : (IsPullback.isoIsPullback y(Γ) U.Tm pb pb).inv = 𝟙 _ := by
    apply pb.hom_ext
    · simp only [IsPullback.isoIsPullback_inv_fst]
      simp
    · simp
  simp only [← heq_eq_eq, comp_eqToHom_heq_iff]
  rw! [equivFst_lift_eq]
  simp [this]

variable (b : y(Γ) ⟶ U.Tm) (b_tp : b ≫ U.tp = a ≫ U.tp)
  (h : y(Γ) ⟶ U.Tm) (h_tp : h ≫ U.tp = i.isKernelPair.lift b a (by aesop) ≫ i.Id)

def endPtSubst : Γ ⟶ i.motiveCtx a :=
  U.substCons (U.substCons (𝟙 _) _ b (by aesop)) _ h (by
    simp only [h_tp, IdIntro.mkId, ← Category.assoc]
    congr 1
    apply i.isKernelPair.hom_ext
    · simp
    · simp)

/-- `Id'` is equivalent to `Id` (one half). -/
def toId : U.Id N i.toIdIntro where
  j := i.j
  j_tp := i.j_tp
  comp_j := i.comp_j
  reflSubst_j := i.reflSubst_j
-- TODO: prove the other half of the equivalence.
-- Generalize this version so that the universe for elimination is not also `U.

end Id'

namespace Id

variable {U. (base : U.IdElimBase) {N : NaturalU.del Ctx}
  (i : U.Id N base.toIdIntro)

open IdIntro IdElimBase

variable {Γ} (ar : y(Γ) ⟶ (UvPoly.id U.Tm).functor.obj N.Tm)
  (aC : y(Γ) ⟶ (IdElimBase.iFunctor base).obj N.Ty)
  (hrC : ar ≫ (UvPoly.id U.Tm).functor.map N.tp =
    aC ≫ (IdElimBase.verticalNatTrans base).app N.Ty)

include hrC in
lemma fst_eq_fst : UvPoly.Equiv.fst _ _ ar = base.equivFst aC :=
  calc _
  _ = UvPoly.Equiv.fst _ _ (ar ≫ (UvPoly.id U.Tm).functor.map N.tp) := by
    rw [UvPoly.Equiv.fst_comp_right]
  _ = UvPoly.Equiv.fst _ _  (aC ≫ (IdElimBase.verticalNatTrans base).app N.Ty) := by
    rw [hrC]
  _ = _ := by
    rw [base.equivFst_verticalNatTrans_app]

abbrev motive : y(base.motiveCtx (base.equivFst aC)) ⟶ N.Ty :=
  base.equivSnd aC

lemma comp_motive {Δ} (σ : Δ ⟶ Γ) : motive base (ym(σ) ≫ aC) =
    ym(base.motiveSubst σ (base.equivFst aC)) ≫ motive base aC := by
  simp only [motive, equivSnd_comp_left base aC σ]

abbrev reflCase : y(Γ) ⟶ N.Tm := UvPoly.Equiv.snd' _ _ ar (Id'.reflCase_aux _)

lemma comp_reflCase {Δ} (σ : Δ ⟶ Γ) : reflCase (ym(σ) ≫ ar) = ym(σ) ≫ reflCase ar := by
  simp only [reflCase]
  rw [UvPoly.Equiv.snd'_comp_left (UvPoly.id U.Tm) N.Tm ar
    (Id'.reflCase_aux (UvPoly.Equiv.fst (UvPoly.id U.Tm) N.Tm ar)) ym(σ)
    (Id'.reflCase_aux _)]
  congr 1
  apply (Id'.reflCase_aux (UvPoly.Equiv.fst (UvPoly.id U.Tm) N.Tm ar)).hom_ext
  · simp only [IsPullback.lift_fst]
    simp
  · simp

include hrC in
lemma reflCase_comp_tp : reflCase ar ≫ N.tp =
    ym(base.reflSubst (base.equivFst aC)) ≫ motive base aC := by
  dsimp [reflCase, motive]
  rw! [← UvPoly.Equiv.snd'_comp_right, hrC]
  have H : IsPullback ym(U.disp (base.mkId
      (ym(U.disp (base.equivFst aC ≫ U.tp)) ≫ base.equivFst aC)
      (U.var (base.equivFst aC ≫ U.tp)) (by simp)) ≫
      U.disp (base.equivFst aC ≫ U.tp))
    (base.toI (base.equivFst aC)) (UvPoly.Equiv.fst base.iUvPoly N.Ty aC) base.iUvPoly.p := by
    convert (base.motiveCtx_isPullback' (base.equivFst aC)).flip
    simp
  rw! [UvPoly.snd'_verticalNatTrans_app
    (R := y(base.motiveCtx (base.equivFst aC)))
    (H := H)
    (R' := y(Γ)) (f' := 𝟙 _) (g' := UvPoly.Equiv.fst (UvPoly.id U.Tm) N.Tm ar)
    (H' := by
    rw [fst_eq_fst base ar aC hrC]
    exact Id'.reflCase_aux _)]
  simp only [Functor.map_comp, iUvPoly_p, equivSnd]
  congr 1
  apply (U.disp_pullback _).hom_ext <;>
    simp only [reflSubst, substCons_var, substCons_disp_functor_map, substCons_var]
  · simp [← base.toI_comp_i1 (base.equivFst aC), fst_eq_fst base ar aC hrC, mkRefl]
  · apply (U.disp_pullback _).hom_ext
    · rw! [fst_eq_fst base ar aC hrC]
      slice_lhs 3 4 => rw [← base.toK_comp_k1]
      slice_lhs 2 3 => rw [← base.toI_comp_i2]
      simp
    · simp

def lift : y(Γ) ⟶ (IdElimBase.iFunctor base).obj N.Tm :=
  base.equivU. (base.equivFst aC) (i.j (base.equivFst aC) (motive base aC)
   (reflCase ar) (reflCase_comp_tp base ar aC hrC))

lemma lift_fst : lift base i ar aC hrC ≫ base.verticalNatTrans.app N.Tm = ar := by
  dsimp only [lift]
  rw [equivU._comp_verticalNatTrans_app]
  apply UvPoly.Equiv.ext' (UvPoly.id U.Tm) N.Tm (by convert reflCase_aux (base.equivFst aC); simp)
  · rw! [i.reflSubst_j]
    simp [reflCase, fst_eq_fst base ar aC hrC]
  · simp [fst_eq_fst base ar aC hrC]

lemma lift_snd : lift base i ar aC hrC ≫ base.iFunctor.map N.tp = aC := by
  dsimp only [lift, equivU.]
  rw [UvPoly.Equiv.mk'_comp_right]
  apply UvPoly.Equiv.ext' base.iUvPoly N.Ty
  · rw! [i.j_tp]
    rw [UvPoly.Equiv.snd'_mk']
    simp [motive, equivSnd]
  · simp only [UvPoly.Equiv.fst_mk', iUvPoly_p]
    exact (base.motiveCtx_isPullback' _).flip
  · simp [equivFst]

lemma comp_lift {Δ} (σ : Δ ⟶ Γ) : ym(σ) ≫ lift base i ar aC hrC =
    lift base i (ym(σ) ≫ ar) (ym(σ) ≫ aC) (by simp [hrC]) := by
  dsimp [lift, equivU.]
  rw [UvPoly.Equiv.mk'_comp_left base.iUvPoly N.Tm (base.equivFst aC) _
    (i.j (base.equivFst aC) (motive base aC) (reflCase ar) _) ym(σ) _ rfl
    (by simp only [iUvPoly_p]; exact (base.motiveCtx_isPullback' _).flip)]
  congr 1
  have h := i.comp_j σ (base.equivFst aC) _ _ (reflCase_comp_tp base ar aC hrC)
  rw! (castU.de := .all) [← comp_motive, ← comp_reflCase, ← equivFst_comp_left] at h
  rw [← h]
  congr 1
  simp only [Functor.map_comp, iUvPoly_p, Category.assoc]
  apply (U.disp_pullback _).hom_ext
  · simp [toI_comp_left, ← toI_comp_i1]
  · apply (U.disp_pullback _).hom_ext
    · slice_rhs 3 4 => rw [← toK_comp_k1 base]
      slice_rhs 2 3 => rw [← toI_comp_i2]
      slice_lhs 3 4 => rw [← toK_comp_k1 base]
      slice_lhs 2 3 => rw [← toI_comp_i2]
      simp [toI_comp_left]
    · simp [motiveSubst, substWk]

def toId' : U.Id' N where
  __ := base
  weakPullback := RepPullbackCone.WeakPullback.mk
    ((IdElimBase.verticalNatTrans base).naturality _).symm
    (fun s => lift base i s.fst s.snd s.condition)
    (fun s => lift_fst base i s.fst s.snd s.condition)
    (fun s => lift_snd base i s.fst s.snd s.condition)
    (fun s _ σ => comp_lift base i s.fst s.snd s.condition σ)

end Id

end NaturalU.del
