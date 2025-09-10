import SEq.Tactic.DepRewrite
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
import Poly.UvPoly.UPFan
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.MorphismProperty.Limits

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
class MorphismProperty.RepresentableMap {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (R : MorphismProperty C) extends R.IsStableUnderBaseChange where
  exponentiableMorphism : ∀ {X Y} {f : X ⟶ Y}, R f → ExponentiableMorphism f
-- FIXME: syntax to make Lean infer [ExponentiableMorphism f]?

namespace MorphismProperty

variable {Ctx : Type u} [Category Ctx] [HasFiniteLimits Ctx]
  (CwR : MorphismProperty Ctx) [CwR.RepresentableMap]

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
  tp_representable : CwR tp

namespace Universe

variable {CwR} (U : Universe CwR) {Γ} (A : Γ ⟶ U.Ty)

-- FIXME should be automatic
instance : ExponentiableMorphism U.tp :=
  MorphismProperty.RepresentableMap.exponentiableMorphism U.tp_representable

@[reassoc (attr := simp)]
theorem var_tp : U.var A ≫ U.tp = U.disp A ≫ A := by
  simp [(U.disp_pullback A).w]

theorem disp_representable :
    CwR (U.disp A) :=
  CwR.of_isPullback (U.disp_pullback A).flip U.tp_representable

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
  tp_representable := CwR.of_isPullback pb.flip U.tp_representable

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

@[reassoc (attr := simp)]
theorem sec_disp : U.sec A a a_tp ≫ U.disp A = 𝟙 _ := by
  simp [sec]

@[reassoc (attr := simp)]
theorem sec_var : U.sec A a a_tp ≫ U.var A = a := by
  simp [sec]

@[reassoc]
theorem comp_sec {Δ : Ctx} (σ : Δ ⟶ Γ) (σA) (eq : σ ≫ A = σA) :
    σ ≫ U.sec A a a_tp = U.sec σA (σ ≫ a) (by simp [eq, a_tp]) ≫ U.substWk A σ _ eq := by
  apply (U.disp_pullback _).hom_ext <;> simp [sec, substWk_disp]

end

end substitution

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
  UvPoly.compDomEquiv.fst ab

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
    fst ab ≫ U.tp = PtpEquiv.fst U (ab ≫ (U.uvPolyTp.compP _)) :=
  UvPoly.compDomEquiv.fst_comp_p ab

theorem comp_fst (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) (σ : Δ ⟶ Γ) :
    σ ≫ fst ab = fst (σ ≫ ab) := by
  simp [fst, UvPoly.compDomEquiv.comp_fst]

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
  UvPoly.compDomEquiv.dependent ab (U.ext A) (U.disp A) (U.var _) (by convert U.disp_pullback A)

theorem dependent_eq (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) : dependent ab =
    eqToHom (by rw [fst_tp]) ≫ PtpEquiv.snd U (ab ≫ (U.uvPolyTp.compP _)) := by
  simp only [dependent, UvPoly.compDomEquiv.dependent_eq, comp_p, uvPolyTp_p, PtpEquiv.snd]
  rw [Equiv.snd'_eq_snd']
  congr 1
  rw! [fst_tp]
  apply (U.disp_pullback _).hom_ext
  · simp
  · simp

theorem comp_dependent (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp)
    {A} (eq1 : fst ab ≫ U.tp = A)
    {σA} (eq2 : σ ≫ A = σA) :
    substWk U _ σ _ eq2 ≫ dependent ab A eq1 =
    dependent (σ ≫ ab) σA (by simp [← comp_fst, eq1, eq2]) := by
  simp only [dependent, UvPoly.compDomEquiv.dependent]
  rw! [Category.assoc]
  rw [Equiv.snd'_comp_left (σ := σ) (H' := by
    convert U.disp_pullback σA
    rw [← eq2, ← eq1, fst_tp]
    rfl)]
  congr 1
  apply (U.disp_pullback A).hom_ext
  · simp [substWk_disp]
  · simp

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `snd : Γ ⟶ U.Tm`
is the `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) : Γ ⟶ V.Tm :=
  UvPoly.compDomEquiv.snd ab
  -- ab ≫ pullback.fst V.tp (PartialProduct.fan U.uvPolyTp V.Ty).snd

theorem comp_snd (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp) :
    σ ≫ snd ab = snd (σ ≫ ab) := by simp [snd, UvPoly.compDomEquiv.comp_snd]

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The equation `snd_tp` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_tp (ab : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp)
    {A} (eq : fst ab ≫ U.tp = A) :
    snd ab ≫ V.tp = U.sec _ (fst ab) eq ≫ dependent ab A eq := by
  erw [UvPoly.compDomEquiv.snd_comp_p (P := U.uvPolyTp) (P' := V.uvPolyTp) ab]
  · congr
  · convert U.disp_pullback A

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : Γ ⟶ U.Tm) {A} (eq : α ≫ U.tp = A) (B : U.ext A ⟶ V.Ty) (β : Γ ⟶ V.Tm)
    (h : β ≫ V.tp = U.sec _ α eq ≫ B) : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp :=
  UvPoly.compDomEquiv.mk (P := U.uvPolyTp) (P' := V.uvPolyTp) α _ (U.disp _) (U.var _)
  (by convert (U.disp_pullback _)) B β (by
    convert h
    apply (U.disp_pullback _).hom_ext <;> simp)

@[simp]
theorem fst_mk (α : Γ ⟶ U.Tm) {A} (eq : α ≫ U.tp = A) (B : (U.ext A) ⟶ V.Ty) (β : (Γ) ⟶ V.Tm)
    (h : β ≫ V.tp = U.sec _ α eq ≫ B) : fst (mk α eq B β h) = α := by
  simp [mk, fst, UvPoly.compDomEquiv.fst_mk]

@[simp]
theorem dependent_mk (α : (Γ) ⟶ U.Tm) {A} (eq : α ≫ U.tp = A)
    (B : (U.ext A) ⟶ V.Ty) (β : (Γ) ⟶ V.Tm)
    (h : β ≫ V.tp = (U.sec _ α eq) ≫ B) :
    dependent (mk α eq B β h) A (by simp [fst_mk, eq]) = B := by
  dsimp only [mk, dependent]
  rw [UvPoly.compDomEquiv.dependent_mk]

@[simp]
theorem snd_mk (α : Γ ⟶ U.Tm) {A} (eq : α ≫ U.tp = A) (B : (U.ext A) ⟶ V.Ty) (β : (Γ) ⟶ V.Tm)
    (h : β ≫ V.tp = (U.sec _ α eq) ≫ B) : snd (mk α eq B β h) = β := by
  simp [mk, snd]

theorem ext {ab₁ ab₂ : Γ ⟶ U.uvPolyTp.compDom V.uvPolyTp}
    {A} (eq : fst ab₁ ≫ U.tp = A)
    (h1 : fst ab₁ = fst ab₂)
    (h2 : dependent ab₁ A eq = dependent ab₂ A (h1 ▸ eq))
    (h3 : snd ab₁ = snd ab₂) : ab₁ = ab₂ := by
  apply UvPoly.compDomEquiv.ext <;> assumption

theorem comp_mk
    (α : Γ ⟶ U.Tm) {A} (e1 : α ≫ U.tp = A)
    (B : U.ext A ⟶ V.Ty)
    (β : Γ ⟶ V.Tm)
    (e2 : β ≫ V.tp = U.sec A α e1 ≫ B)
    (σ : Δ ⟶ Γ) {σA} (e3 : σ ≫ A = σA) :
    (σ) ≫ mk α e1 B β e2 =
    mk (σ ≫ α) (by simp [e1, e3]) ((U.substWk A σ _ e3) ≫ B) ((σ) ≫ β)
      (by simp [e2]; rw [comp_sec_assoc]) := by
  apply ext (A := σA) (by simp [← comp_fst, e1, e3]) <;> simp [← comp_fst, ← comp_snd]
  rw [← comp_dependent, dependent_mk]

theorem eta (ab : (Γ) ⟶ U.uvPolyTp.compDom V.uvPolyTp)
    {A} (eq : fst ab ≫ U.tp = A) :
    mk (fst ab) eq (dependent ab A eq) (snd ab) (snd_tp ab eq) = ab := by
  symm; apply ext (eq := eq) <;> simp

end compDomEquiv

/-! ## Pi and Sigma types -/

set_option linter.dupNamespace false in
protected structure Pi where
  Pi : U.Ptp.obj U.Ty ⟶ U.Ty
  lam : U.Ptp.obj U.Tm ⟶ U.Tm
  Pi_pullback : IsPullback (U.Ptp.map U.tp) lam Pi U.tp

protected structure Sigma where
  Sig : U.Ptp.obj U.Ty ⟶ U.Ty
  pair : UvPoly.compDom (uvPolyTp U) (uvPolyTp U) ⟶ U.Tm
  Sig_pullback : IsPullback ((uvPolyTp U).compP (uvPolyTp U)) pair Sig U.tp

end Universe

end MorphismProperty

end CategoryTheory
