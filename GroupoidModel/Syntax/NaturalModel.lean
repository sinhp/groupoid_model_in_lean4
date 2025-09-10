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

open CategoryTheory Limits Opposite

namespace NaturalModel

/-- A natural model with support for dependent types (and nothing more).
The data is a natural transformation with representable fibers,
stored as a choice of representative for each fiber. -/
structure Universe (Ctx : Type u) [Category Ctx] where
  Tm : Psh Ctx
  Ty : Psh Ctx
  tp : Tm ⟶ Ty
  ext {Γ : Ctx} (A : y(Γ) ⟶ Ty) : Ctx
  disp {Γ : Ctx} (A : y(Γ) ⟶ Ty) : ext A ⟶ Γ
  var {Γ : Ctx} (A : y(Γ) ⟶ Ty) : y(ext A) ⟶ Tm
  disp_pullback {Γ : Ctx} (A : y(Γ) ⟶ Ty) :
    IsPullback (var A) ym(disp A) tp A

namespace Universe

variable {Ctx : Type u} [SmallCategory Ctx] (M : Universe Ctx)

@[simps! hom inv]
def pullbackIsoExt {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) :
    pullback A M.tp ≅ yoneda.obj (M.ext A) :=
  -- The use of `IsPullback.flip` suggests an inconsistency in convention.
  IsPullback.isoPullback (M.disp_pullback A).flip |>.symm

/-! ## Pullback of representable natural transformation -/

/-- Pull a natural model back along a type. -/
protected def pullback {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) : Universe Ctx where
  Tm := y(M.ext A)
  Ty := y(Γ)
  tp := ym(M.disp A)
  ext := fun B => M.ext (B ≫ A)
  disp := fun B => M.disp (B ≫ A)
  var := fun B =>
    (M.disp_pullback A).lift (M.var (B ≫ A)) (ym(M.disp (B ≫ A)) ≫ B) (M.disp_pullback (B ≫ A)).w
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
def ofIsPullback {U E : Psh Ctx} {π : E ⟶ U}
    {toTy : U ⟶ M.Ty} {toTm : E ⟶ M.Tm}
    (pb : IsPullback toTm π M.tp toTy) :
    Universe Ctx where
  Ty := U
  Tm := E
  tp := π
  ext A := M.ext (A ≫ toTy)
  disp A := M.disp (A ≫ toTy)
  var A := pb.lift
    (M.var (A ≫ toTy))
    (ym(M.disp (A ≫ toTy)) ≫ A)
    (M.disp_pullback (A ≫ toTy)).w
  disp_pullback A :=
    IsPullback.of_right'
      (M.disp_pullback (A ≫ toTy))
      pb

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
def substCons {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty)
    (t : y(Δ) ⟶ M.Tm) (t_tp : t ≫ M.tp = ym(σ) ≫ A) :
    Δ ⟶ M.ext A :=
  uy((M.disp_pullback A).lift t ym(σ) t_tp)

@[functor_map (attr := reassoc (attr := simp))]
theorem substCons_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (t : y(Δ) ⟶ M.Tm)
    (tTp : t ≫ M.tp = ym(σ) ≫ A) :
    M.substCons σ A t tTp ≫ M.disp A = σ := by
  apply Yoneda.fullyFaithful.map_injective
  simp [substCons]

@[reassoc (attr := simp)]
theorem substCons_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (t : y(Δ) ⟶ M.Tm)
    (aTp : t ≫ M.tp = ym(σ) ≫ A) :
    ym(M.substCons σ A t aTp) ≫ M.var A = t := by
  simp [substCons]

@[simp]
theorem comp_substCons {Θ Δ Γ : Ctx} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (t : y(Δ) ⟶ M.Tm)
    (aTp : t ≫ M.tp = ym(σ) ≫ A) :
    τ ≫ M.substCons σ A t aTp = M.substCons (τ ≫ σ) A (ym(τ) ≫ t) (by simp [*]) := by
  apply Yoneda.fullyFaithful.map_injective
  apply (M.disp_pullback A).hom_ext
  · simp
  · simp

/--
```
Δ ⊢ σ : Γ.A
------------
Δ ⊢ ↑∘σ : Γ
```
-/
def substFst {Δ Γ : Ctx} {A : y(Γ) ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : Δ ⟶ Γ :=
  σ ≫ M.disp A

/--
```
Δ ⊢ σ : Γ.A
-------------------
Δ ⊢ v₀[σ] : A[↑∘σ]
```
-/
def substSnd {Δ Γ : Ctx} {A : y(Γ) ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : y(Δ) ⟶ M.Tm :=
  ym(σ) ≫ M.var A

theorem substSnd_tp {Δ Γ : Ctx} {A : y(Γ) ⟶ M.Ty} (σ : Δ ⟶ M.ext A) :
    M.substSnd σ ≫ M.tp = ym(M.substFst σ) ≫ A := by
  simp [substSnd, substFst]; rw [(M.disp_pullback _).w]

@[reassoc (attr := simp)]
theorem var_tp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) : M.var A ≫ M.tp = ym(M.disp A) ≫ A := by
  simp [(M.disp_pullback A).w]

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
def substWk {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty)
    (A' := ym(σ) ≫ A) (eq : ym(σ) ≫ A = A' := by rfl) : M.ext A' ⟶ M.ext A :=
  M.substCons (M.disp _ ≫ σ) A (M.var _) (by simp [eq])

@[functor_map (attr := reassoc)]
theorem substWk_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (A' eq) :
    M.substWk σ A A' eq ≫ M.disp A = M.disp A' ≫ σ := by
  simp [substWk]

@[reassoc (attr := simp)]
theorem substWk_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (A' eq) :
    ym(M.substWk σ A A' eq) ≫ M.var A = M.var A' := by
  simp [substWk]

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
def sec {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) : Γ ⟶ M.ext A :=
  M.substCons (𝟙 Γ) A a (by simp [a_tp])

@[functor_map (attr := reassoc (attr := simp))]
theorem sec_disp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.sec A a a_tp ≫ M.disp A = 𝟙 _ := by
  simp [sec]

@[reassoc (attr := simp)]
theorem sec_var {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    ym(M.sec A a a_tp) ≫ M.var A = a := by
  simp [sec]

@[functor_map (attr := reassoc)]
theorem comp_sec {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (σA) (eq : ym(σ) ≫ A = σA)
    (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    σ ≫ M.sec A a a_tp = M.sec σA (ym(σ) ≫ a) (by simp [eq, a_tp]) ≫ M.substWk σ A _ eq := by
  apply Yoneda.fullyFaithful.map_injective
  apply (M.disp_pullback _).hom_ext <;>
    simp [sec, substWk_disp_functor_map]

/-! ## Polynomial functor on `tp`

Specializations of results from the `Poly` package to natural models. -/

@[simps] def uvPolyTp : UvPoly M.Tm M.Ty := ⟨M.tp, inferInstance⟩
def Ptp : Psh Ctx ⥤ Psh Ctx := M.uvPolyTp.functor

namespace PtpEquiv

variable {Γ : Ctx} {X : Psh Ctx}

-- TODO: possibly want to remove M.uvPolyTp.equiv
-- and directly define `fst`, `snd`, etc.
/--
A map `(AB : y(Γ) ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : y(Γ) ⟶ M.Ty` and `B : y(M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`.
`PtpEquiv.fst` is the `A` in this pair.
-/
def fst (AB : y(Γ) ⟶ M.Ptp.obj X) : y(Γ) ⟶ M.Ty :=
  UvPoly.Equiv.fst M.uvPolyTp X AB

/--
A map `(AB : y(Γ) ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : y(Γ) ⟶ M.Ty` and `B : y(M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.snd` is the `B` in this pair.
-/
def snd (AB : y(Γ) ⟶ M.Ptp.obj X) (A := fst M AB) (eq : fst M AB = A := by rfl) : y(M.ext A) ⟶ X :=
  UvPoly.Equiv.snd' M.uvPolyTp X AB (by rw [← fst, eq]; exact (M.disp_pullback _).flip)

/--
A map `(AB : y(Γ) ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : y(Γ) ⟶ M.Ty` and `B : y(M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-/
def mk (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) : y(Γ) ⟶ M.Ptp.obj X :=
  UvPoly.Equiv.mk' M.uvPolyTp X A (M.disp_pullback _).flip B

@[simp]
lemma fst_mk (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    fst M (mk M A B) = A := by
  simp [fst, mk]

@[simp]
lemma snd_mk (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    snd M (mk M A B) _ (fst_mk ..) = B := by
  dsimp only [snd, mk]
  rw! [UvPoly.Equiv.snd'_mk']

section
variable {Δ : Ctx} {σ : Δ ⟶ Γ} {AB : y(Γ) ⟶ M.Ptp.obj X}

theorem fst_comp_left (σ : y(Δ) ⟶ y(Γ)) : fst M (σ ≫ AB) = σ ≫ fst M AB :=
  UvPoly.Equiv.fst_comp_left ..

theorem fst_comp_right {Y} (σ : X ⟶ Y) : fst M (AB ≫ M.Ptp.map σ) = fst M AB :=
  UvPoly.Equiv.fst_comp_right ..

theorem snd_comp_right {Y} (σ : X ⟶ Y) {A} (eq : fst M AB = A) :
    snd M (AB ≫ M.Ptp.map σ) _ (fst_comp_right M σ ▸ eq) = snd M AB _ eq ≫ σ := by
  simp only [snd, Ptp]
  rw [UvPoly.Equiv.snd'_comp_right M.uvPolyTp X Y σ AB]

theorem snd_comp_left {A} (eqA : fst M AB = A) {σA} (eqσ : ym(σ) ≫ A = σA) :
    snd M (ym(σ) ≫ AB) σA (by simp [fst_comp_left, eqA, eqσ]) =
    ym(M.substWk σ _ _ eqσ) ≫ snd M AB _ eqA := by
  have H1 : IsPullback ym(M.disp A) (M.var A) (UvPoly.Equiv.fst M.uvPolyTp X AB) M.uvPolyTp.p := by
    rw [← fst, eqA]; exact (M.disp_pullback _).flip
  have H2 : IsPullback ym(M.disp σA) (M.var σA)
    (ym(σ) ≫ UvPoly.Equiv.fst M.uvPolyTp X AB) M.uvPolyTp.p := by
    rw [← fst, eqA, eqσ]; exact (M.disp_pullback _).flip
  convert UvPoly.Equiv.snd'_comp_left M.uvPolyTp X AB H1 _ H2
  apply H1.hom_ext <;> simp [← Functor.map_comp, substWk]

theorem mk_comp_left {Δ Γ : Ctx} (M : Universe Ctx) (σ : Δ ⟶ Γ)
    {X : Psh Ctx} (A : y(Γ) ⟶ M.Ty) (σA) (eq : ym(σ) ≫ A = σA) (B : y(M.ext A) ⟶ X) :
    ym(σ) ≫ PtpEquiv.mk M A B = PtpEquiv.mk M σA (ym(M.substWk σ A _ eq) ≫ B) := by
  dsimp [PtpEquiv.mk]
  have h := UvPoly.Equiv.mk'_comp_left M.uvPolyTp X A (M.disp_pullback A).flip B ym(σ)
    σA eq (M.disp_pullback σA).flip
  convert h
  apply (M.disp_pullback _).hom_ext
  · simp
  · simp [← Functor.map_comp, substWk_disp]

theorem mk_comp_right {Γ : Ctx} (M : Universe Ctx)
    {X Y : Psh Ctx} (σ : X ⟶ Y) (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    PtpEquiv.mk M A B ≫ M.Ptp.map σ = PtpEquiv.mk M A (B ≫ σ) :=
  UvPoly.Equiv.mk'_comp_right M.uvPolyTp X Y σ A (M.disp_pullback A).flip B

theorem ext {AB AB' : y(Γ) ⟶ M.Ptp.obj X}
    (A := fst M AB) (eq : fst M AB = A := by rfl)
    (h1 : fst M AB = fst M AB')
    (h2 : snd M AB A eq = snd M AB' A (h1 ▸ eq))
    : AB = AB' := UvPoly.Equiv.ext' _ _ _ h1 h2

theorem eta (AB : y(Γ) ⟶ M.Ptp.obj X) : mk M (fst M AB) (snd M AB) = AB :=
  .symm <| ext _ _ rfl (by simp) (by simp)

def lift {Y} (mk : ∀ {Γ} {A : y(Γ) ⟶ M.Ty}, (y(M.ext A) ⟶ X) → (y(Γ) ⟶ Y))
    (comp_mk : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) {σA} (eq) (B : y(M.ext A) ⟶ X),
      ym(σ) ≫ mk B = mk (A := σA) (ym(M.substWk σ A σA eq) ≫ B))
    : M.Ptp.obj X ⟶ Y where
  app Γ' A := yonedaEquiv (mk (snd M (yonedaEquiv.symm A)))
  naturality A B σ := by
    ext C; dsimp
    set σC := (M.Ptp.obj X).map σ C
    set C' := yonedaEquiv.symm C
    set σC' := yonedaEquiv.symm σC
    have : σC' = ym(σ.unop) ≫ C' := (yonedaEquiv_symm_naturality_left _ _ _).symm
    rw [yonedaEquiv_naturality', comp_mk σ.unop (fst M C') (σA := fst M σC') _ (snd M C'),
      ← snd_comp_left]
    · congr! 3
    · rw [← fst_comp_left, this]

theorem comp_lift {Y} (mk comp_mk) {Γ} (ab : y(Γ) ⟶ M.Ptp.obj X)
    (A := fst M ab) (eq : fst M ab = A := by rfl) :
    ab ≫ lift M (Y := Y) mk comp_mk = mk (snd M ab A eq) := by
  cases eq
  obtain ⟨ab, rfl⟩ := yonedaEquiv.symm.surjective ab
  apply yonedaEquiv.injective
  trans (lift M mk comp_mk).app ⟨Γ⟩ ab
  · simp [yonedaEquiv_symm_naturality_right]
  · simp [lift]

end

end PtpEquiv

@[reassoc]
theorem PtpEquiv.mk_map {Γ : Ctx} {X Y : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (x : y(M.ext A) ⟶ X) (α : X ⟶ Y) :
    mk M A x ≫ M.Ptp.map α = mk M A (x ≫ α) := by
  simp [mk, Ptp, UvPoly.Equiv.mk'_comp_right]

/-! ## Polynomial composition `M.tp ▸ N.tp` -/

-- -- `private` lemma for the equivalence below.
-- private lemma lift_ev {Γ : Ctx} {N : Universe Ctx}
--     {AB : y(Γ) ⟶ M.Ptp.obj N.Ty} {α : y(Γ) ⟶ M.Tm}
--     (hA : AB ≫ M.uvPolyTp.fstProj N.Ty = α ≫ M.tp) :
--     pullback.lift AB α hA ≫ (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).snd =
--       ym(M.sec (α ≫ M.tp) α rfl) ≫
--         (M.disp_pullback _).lift (M.var _) ym(M.disp _)
--           (by dsimp; rw [hA, (M.disp_pullback _).w]) ≫
--         (M.Ptp_equiv AB).2 :=
--   sorry

namespace compDomEquiv
open UvPoly

variable {M N : Universe Ctx} {Γ Δ : Ctx} (σ : Δ ⟶ Γ)

/-- Universal property of `compDom`, decomposition (part 1).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`. The map `fst : y(Γ) ⟶ M.Tm`
is the `(a : A)` in `(a : A) × (b : B a)`.
-/
def fst (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : y(Γ) ⟶ M.Tm :=
  ab ≫ pullback.snd N.tp (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).snd ≫
    pullback.snd (M.uvPolyTp.fstProj N.Ty) M.uvPolyTp.p

/-- Computation of `comp` (part 1).

`fst_tp` is (part 1) of the computation that
      (α, B, β, h)
     Γ ⟶ compDom
      \        |
       \       | comp
(α ≫ tp, B)    |
         \     V
           >  P_tp Ty
Namely the first projection `α ≫ tp` agrees.
-/
theorem fst_tp (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
    fst ab ≫ M.tp = PtpEquiv.fst M (ab ≫ (M.uvPolyTp.compP _)) := by
  have : pullback.snd (M.uvPolyTp.fstProj N.Ty) M.tp ≫ M.tp =
    pullback.fst (M.uvPolyTp.fstProj N.Ty) M.tp ≫ M.uvPolyTp.fstProj N.Ty :=
      Eq.symm pullback.condition
  simp [PtpEquiv.fst, fst, this]
  rfl

theorem comp_fst (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) (σ : y(Δ) ⟶ y(Γ)) :
    σ ≫ fst ab = fst (σ ≫ ab) := by simp [fst]

/-- Universal property of `compDom`, decomposition (part 2).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `dependent : y(M.ext (fst N ab ≫ M.tp)) ⟶ M.Ty`
is the `B : A ⟶ Type` in `(a : A) × (b : B a)`.
Here `A` is implicit, derived by the typing of `fst`, or `(a : A)`.
-/
def dependent (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    (A := fst ab ≫ M.tp) (eq : fst ab ≫ M.tp = A := by rfl) :
    y(M.ext A) ⟶ N.Ty :=
  PtpEquiv.snd M (ab ≫ (M.uvPolyTp.compP _)) _ (by rw [← eq, fst_tp])

theorem comp_dependent (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq1 : fst ab ≫ M.tp = A)
    {σA} (eq2 : ym(σ) ≫ A = σA) :
    ym(substWk M σ _ _ eq2) ≫ dependent ab A eq1 =
    dependent (ym(σ) ≫ ab) σA (by simp [← comp_fst, eq1, eq2]) := by
  rw [dependent, ← PtpEquiv.snd_comp_left]; rfl

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `snd : y(Γ) ⟶ M.Tm`
is the `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : y(Γ) ⟶ N.Tm :=
  ab ≫ pullback.fst N.tp (PartialProduct.fan M.uvPolyTp N.Ty).snd

theorem comp_snd (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) (σ : y(Δ) ⟶ y(Γ)) :
    σ ≫ snd ab = snd (σ ≫ ab) := by simp [snd]

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The equation `snd_tp` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_tp (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq : fst ab ≫ M.tp = A) :
    snd ab ≫ N.tp = ym(M.sec _ (fst ab) eq) ≫ dependent ab A eq := by
  simp [snd, pullback.condition, dependent, PtpEquiv.snd, Equiv.snd'_eq]
  simp only [← Category.assoc]; congr! 1
  apply pullback.hom_ext <;> simp [fst, UvPoly.compP]

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : y(Γ) ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : y(M.ext A) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm)
    (h : β ≫ N.tp = ym(M.sec _ α eq) ≫ B) : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp := by
  refine pullback.lift β (pullback.lift (PtpEquiv.mk _ A B) α ?_) ?_
  · simp [← Equiv.fst_eq, ← PtpEquiv.fst.eq_def, eq]
  · simp [h]
    conv_lhs => arg 2; exact
      Equiv.snd'_mk' M.uvPolyTp N.Ty A _ B
        |>.symm.trans <| Equiv.snd'_eq M.uvPolyTp N.Ty (PtpEquiv.mk M A B) _
    simp only [← Category.assoc]; congr! 1
    apply pullback.hom_ext <;> simp

@[simp]
theorem fst_mk (α : y(Γ) ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : y(M.ext A) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm)
    (h : β ≫ N.tp = ym(M.sec _ α eq) ≫ B) : fst (mk α eq B β h) = α := by
  simp [mk, fst]

@[simp]
theorem dependent_mk (α : y(Γ) ⟶ M.Tm) {A} (eq : α ≫ M.tp = A)
    (B : y(M.ext A) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm)
    (h : β ≫ N.tp = ym(M.sec _ α eq) ≫ B) :
    dependent (mk α eq B β h) A (by simp [fst_mk, eq]) = B := by
  simp [mk, dependent, UvPoly.compP]
  convert PtpEquiv.snd_mk M A B using 2
  slice_lhs 1 2 => apply pullback.lift_snd
  simp

@[simp]
theorem snd_mk (α : y(Γ) ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : y(M.ext A) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm)
    (h : β ≫ N.tp = ym(M.sec _ α eq) ≫ B) : snd (mk α eq B β h) = β := by
  simp [mk, snd]

theorem ext {ab₁ ab₂ : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp}
    {A} (eq : fst ab₁ ≫ M.tp = A)
    (h1 : fst ab₁ = fst ab₂)
    (h2 : dependent ab₁ A eq = dependent ab₂ A (h1 ▸ eq))
    (h3 : snd ab₁ = snd ab₂) : ab₁ = ab₂ := by
  refine pullback.hom_ext h3 (pullback.hom_ext ?_ h1)
  simp only [dependent, PtpEquiv.snd] at h2
  generalize_proofs _ _ H at h2
  refine Equiv.ext' M.uvPolyTp N.Ty H ?_ h2
  simp [Equiv.fst, pullback.condition]
  simp only [← Category.assoc]; congr 1

theorem comp_mk
    (α : y(Γ) ⟶ M.Tm) {A} (e1 : α ≫ M.tp = A)
    (B : y(M.ext A) ⟶ N.Ty)
    (β : y(Γ) ⟶ N.Tm)
    (e2 : β ≫ N.tp = ym(M.sec A α e1) ≫ B)
    (σ : Δ ⟶ Γ) {σA} (e3 : ym(σ) ≫ A = σA) :
    ym(σ) ≫ mk α e1 B β e2 =
    mk (ym(σ) ≫ α) (by simp [e1, e3])
      (ym(M.substWk σ A _ e3) ≫ B) (ym(σ) ≫ β)
      (by simp [e2]; rw [← Functor.map_comp_assoc, comp_sec]; simp; congr!) := by
  apply ext (A := σA) (by simp [← comp_fst, e1, e3]) <;> simp [← comp_fst, ← comp_snd]
  rw [← comp_dependent, dependent_mk]

theorem eta (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq : fst ab ≫ M.tp = A) :
    mk (fst ab) eq (dependent ab A eq) (snd ab) (snd_tp ab eq) = ab := by
  symm; apply ext (eq := eq) <;> simp

def lift {Y}
    (mk : ∀ {Γ} (α : y(Γ) ⟶ M.Tm) {A} (eq : α ≫ M.tp = A)
      (B : y(M.ext A) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm),
      β ≫ N.tp = ym(M.sec A α eq) ≫ B → (y(Γ) ⟶ Y))
    (comp_mk : ∀ {Γ Δ} (σ : Δ ⟶ Γ)
      (α : y(Γ) ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) {σA} (eqA : ym(σ) ≫ A = σA)
      (B : y(M.ext A) ⟶ N.Ty)
      (β : y(Γ) ⟶ N.Tm)
      (eqB : β ≫ N.tp = ym(M.sec A α eq) ≫ B),
      ym(σ) ≫ mk α eq B β eqB =
      mk (ym(σ) ≫ α) (by simp [eq, eqA])
        (ym(M.substWk σ A _ eqA) ≫ B) (ym(σ) ≫ β)
        (by simp [eqB]; rw [← Functor.map_comp_assoc, comp_sec]; simp; congr!))
    : M.uvPolyTp.compDom N.uvPolyTp ⟶ Y where
  app Γ' A :=
    have A := yonedaEquiv.symm A
    yonedaEquiv (mk (fst A) rfl (dependent A) (snd A) (snd_tp A rfl))
  naturality A B σ := by
    ext C; dsimp
    set σC := (M.uvPolyTp.compDom N.uvPolyTp).map σ C
    set C' := yonedaEquiv.symm C
    set σC' := yonedaEquiv.symm σC
    have : σC' = ym(σ.unop) ≫ C' := (yonedaEquiv_symm_naturality_left _ _ _).symm
    have : fst σC' = ym(σ.unop) ≫ fst C' := by simp [this, comp_fst]
    have : ym(σ.unop) ≫ fst C' ≫ M.tp = fst σC' ≫ M.tp := by simp [this]
    rw [yonedaEquiv_naturality', comp_mk σ.unop (σA := fst σC' ≫ M.tp)]
    congr! 2
    · rw [comp_dependent]; congr! 1; assumption
    · simp [comp_snd, *]

theorem comp_lift {Y} (mk comp_mk) {Γ} (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    (A := fst ab ≫ M.tp) (eq : fst ab ≫ M.tp = A := by rfl)
    (B := dependent ab A eq) (eqB : dependent ab A eq = B := by rfl) :
    ab ≫ lift (M := M) (N := N) (Y := Y) mk comp_mk =
    mk (fst ab) eq B (snd ab) (eqB ▸ snd_tp ab eq) := by
  cases eq
  obtain ⟨ab, rfl⟩ := yonedaEquiv.symm.surjective ab
  apply yonedaEquiv.injective
  trans (lift mk comp_mk).app ⟨Γ⟩ ab
  · simp [yonedaEquiv_symm_naturality_right]
  · simp [eqB, lift]

theorem comp_lift_mk {Y} (mk' comp_mk) {Γ}
    (α : y(Γ) ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : y(M.ext A) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm)
    (h : β ≫ N.tp = ym(M.sec _ α eq) ≫ B) :
    mk α eq B β h ≫ lift (M := M) (N := N) (Y := Y) mk' comp_mk =
    mk' α eq B β h := by rw [comp_lift (A := A) (eq := by simp [eq])]; simp

end compDomEquiv

/-! ## Pi and Sigma types -/

set_option linter.dupNamespace false in
protected structure Pi where
  Pi : M.Ptp.obj M.Ty ⟶ M.Ty
  lam : M.Ptp.obj M.Tm ⟶ M.Tm
  Pi_pullback : IsPullback lam (M.Ptp.map M.tp) M.tp Pi

protected structure Sigma where
  Sig : M.Ptp.obj M.Ty ⟶ M.Ty
  pair : UvPoly.compDom (uvPolyTp M) (uvPolyTp M) ⟶ M.Tm
  Sig_pullback : IsPullback pair ((uvPolyTp M).compP (uvPolyTp M)) M.tp Sig

variable {M} in
open compDomEquiv in
def Sigma.mk'
    (Sig : ∀ {Γ} {A : y(Γ) ⟶ M.Ty}, (y(M.ext A) ⟶ M.Ty) → (y(Γ) ⟶ M.Ty))
    (comp_Sig : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) {σA} (eq) (B : y(M.ext A) ⟶ M.Ty),
      ym(σ) ≫ Sig B = Sig (ym(M.substWk σ A σA eq) ≫ B))
    (assoc : ∀ {Γ} {A : y(Γ) ⟶ M.Ty} (B : y(M.ext A) ⟶ M.Ty), M.ext B ≅ M.ext (Sig B))
    (comp_assoc : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : y(Γ) ⟶ M.Ty} {σA} (eq) (B : y(M.ext A) ⟶ M.Ty),
      substWk _ (substWk _ σ _ _ eq) _ ≫ (assoc B).hom =
      (assoc (ym(substWk M σ A σA eq) ≫ B)).hom ≫ substWk M σ _ _ (comp_Sig ..))
    (assoc_disp : ∀ {Γ} {A : y(Γ) ⟶ M.Ty} (B : y(M.ext A) ⟶ M.Ty),
      (assoc B).hom ≫ M.disp _ = M.disp _ ≫ M.disp _)
    : M.Sigma where
  Sig := PtpEquiv.lift M Sig comp_Sig
  pair := by
    fapply compDomEquiv.lift
    · intro Γ α A eq B β eqB
      refine ym(?_ ≫ (assoc B).hom) ≫ M.var _
      exact substCons _ (substCons _ (𝟙 _) _ α (by simp [eq])) _ β eqB
    · as_aux_lemma =>
      intro Γ Δ σ α A eq σA eqA B β eqB
      have := comp_assoc σ eqA B
      replace := congr(ym($this) ≫ M.var _)
      simp at this ⊢; rw [← this]; clear this
      simp only [← Category.assoc]; congr! 2
      apply (M.disp_pullback _).hom_ext <;> simp
      apply (M.disp_pullback _).hom_ext <;> simp [substWk_disp_functor_map]
  Sig_pullback := by
    fapply RepPullbackCone.is_pullback'
    · refine hom_ext_yoneda fun Γ A => ?_
      rw [reassoc_of% compDomEquiv.comp_lift, ← Category.assoc A, PtpEquiv.comp_lift]
      have := assoc_disp (dependent A _ rfl)
      simp; simp only [← Functor.map_comp_assoc]; rw [this, comp_Sig]; congr! 1
      case eq => simp [fst_tp]
      rw [comp_dependent, dependent]; congr! 2
      simp [substCons_disp]
    · intro s
      let A := PtpEquiv.fst M s.snd
      let B : y(M.ext A) ⟶ M.Ty := PtpEquiv.snd M s.snd
      have ptp := s.condition
      simp [PtpEquiv.comp_lift] at ptp; change _ = Sig B at ptp
      let σ := M.sec (Sig B) _ ptp ≫ (assoc B).inv
      have := assoc_disp B
      rw [← Iso.eq_inv_comp, eq_comm] at this
      replace : σ ≫ M.disp B ≫ M.disp A = M.sec (Sig B) .. ≫ _ :=
        (Category.assoc ..).trans congr(M.sec _ _ ptp ≫ $this)
      replace := congr(ym($this)); simp at this
      refine
        let t := compDomEquiv.mk (ym(σ ≫ M.disp _) ≫ M.var _) ?_ B (ym(σ) ≫ M.var _) ?_
        ⟨t, ?_⟩
      · simp [reassoc_of% this]
      · simp; rw [← Category.assoc]; congr! 1
        apply (M.disp_pullback A).hom_ext <;> simp [this]
      · have ttp : fst t ≫ M.tp = A := by simp [t, reassoc_of% this]
        have t1 : fst t = ym(σ ≫ M.disp _) ≫ M.var _ := fst_mk ..
        have td : dependent t _ ttp = B := dependent_mk ..
        have t2 : snd t = ym(σ) ≫ M.var _ := snd_mk ..
        refine ⟨?_, ?_, fun m h1 h2 => ?_⟩
        · rw [comp_lift_mk]
          convert (show ym(M.sec _ _ ptp) ≫ M.var _ = s.fst by simp) using 3
          rw [← Iso.eq_comp_inv]
          apply Yoneda.yoneda_faithful.1
          apply (M.disp_pullback _).hom_ext <;> simp [σ]
          apply (M.disp_pullback _).hom_ext <;> simp
          simpa [σ] using this.symm
        · symm; fapply PtpEquiv.ext (A := A)
          · rw [← fst_tp, ttp]
          · exact (dependent_mk ..).symm
        · have mtp : fst m ≫ M.tp = A := by rw [fst_tp]; unfold A; congr! 1
          have md : dependent m _ mtp = B := by unfold dependent B; congr! 1
          rw [comp_lift (A := A) (eq := mtp) (B := B) (eqB := md)] at h1
          refine let σ' := _; have h1 : ym(σ' ≫ _) ≫ _ = _ := h1; ?_
          have H : σ' ≫ (assoc B).hom = M.sec _ s.fst ptp := by
            apply Yoneda.yoneda_faithful.1
            apply (M.disp_pullback _).hom_ext
            · rw [h1]; simp
            · simp; rw [← Functor.map_comp, assoc_disp]; simp [σ']
          simp [← Iso.eq_comp_inv, σ'] at H
          have m1 : fst m = ym(σ ≫ M.disp B) ≫ M.var A := by
            simpa [σ] using congr(ym($H ≫ M.disp _) ≫ M.var _)
          symm; fapply compDomEquiv.ext (A := A) (eq := by simp [t, reassoc_of% this])
          · simp [m1, t1]
          · simp [md, td]
          · simpa [σ, t2] using congr(ym($H.symm) ≫ M.var _)

/--
Universe.IdIntro consists of the following commutative square
       refl
M.Tm ------> M.Tm
 |            |
 |            |
diag         M.tp
 |            |
 |            |
 V            V
 k --------> M.Ty
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
  k1 : k ⟶ M.Tm
  k2 : k ⟶ M.Tm
  isKernelPair : IsKernelPair M.tp k1 k2
  Id : k ⟶ M.Ty
  refl : M.Tm ⟶ M.Tm
  refl_tp : refl ≫ M.tp =
    (IsPullback.lift isKernelPair (𝟙 M.Tm) (𝟙 M.Tm) (by simp)) ≫ Id

namespace IdIntro

variable {M} (idIntro : IdIntro M) {Γ : Ctx}

/-- The introduction rule for identity types.
To minimize the number of arguments, we infer the type from the terms. -/
def mkId (a0 a1 : y(Γ) ⟶ M.Tm)
    (a0_tp_eq_a1_tp : a0 ≫ M.tp = a1 ≫ M.tp) :
    y(Γ) ⟶ M.Ty :=
  idIntro.isKernelPair.lift a1 a0 (by rw [a0_tp_eq_a1_tp]) ≫ idIntro.Id

theorem comp_mkId {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (a0 a1 : y(Γ) ⟶ M.Tm) (eq : a0 ≫ M.tp = a1 ≫ M.tp) :
    ym(σ) ≫ mkId idIntro a0 a1 eq =
      mkId idIntro (ym(σ) ≫ a0) (ym(σ) ≫ a1) (by simp [eq]) := by
  simp [mkId]; rw [← Category.assoc]; congr 1
  apply idIntro.isKernelPair.hom_ext <;> simp

def mkRefl (a : y(Γ) ⟶ M.Tm) : y(Γ) ⟶ M.Tm :=
  a ≫ idIntro.refl

theorem comp_mkRefl {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ M.Tm) :
    ym(σ) ≫ idIntro.mkRefl a = idIntro.mkRefl (ym(σ) ≫ a) :=
  rfl

@[simp]
theorem mkRefl_tp (a : y(Γ) ⟶ M.Tm) :
    idIntro.mkRefl a ≫ M.tp = idIntro.mkId a a rfl := by
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
def motiveCtx (a : y(Γ) ⟶ M.Tm) : Ctx :=
  M.ext (idIntro.mkId (ym(M.disp (a ≫ M.tp)) ≫ a) (M.var _) (by simp))

def motiveSubst {Γ Δ} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ M.Tm) :
    motiveCtx idIntro (ym(σ) ≫ a) ⟶ motiveCtx idIntro a := by
  refine substWk _ (substWk _ σ _ _ (by simp)) _ _ ?_
  simp [comp_mkId]; congr 1; simp only [← Functor.map_comp_assoc, substWk_disp]

/-- The substitution `(a,refl)` appearing in identity elimination `J`
  `(a,refl) : y(Γ) ⟶ y(Γ.(x:A).(h:Id(A,a,x)))`
  so that we can write
  `Γ ⊢ r : M(a,refl)`
-/
def reflSubst (a : y(Γ) ⟶ M.Tm) : Γ ⟶ idIntro.motiveCtx a :=
  M.substCons (M.substCons (𝟙 Γ) (a ≫ M.tp) a (by simp)) _ (idIntro.mkRefl a) (by
    simp only [mkRefl_tp, mkId, ← Category.assoc]
    congr 1
    apply idIntro.isKernelPair.hom_ext <;> simp)

@[reassoc]
theorem comp_reflSubst' {Γ Δ} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ M.Tm) :
    ym(σ) ≫ ym(idIntro.reflSubst a) =
    ym(idIntro.reflSubst (ym(σ) ≫ a)) ≫ ym(idIntro.motiveSubst σ a) := by
  apply (M.disp_pullback _).hom_ext <;> simp [reflSubst, motiveSubst, mkRefl]
  apply (M.disp_pullback _).hom_ext <;> simp [substWk]

@[simp, reassoc]
lemma comp_reflSubst (a : y(Γ) ⟶ M.Tm) {Δ} (σ : Δ ⟶ Γ) :
    reflSubst idIntro (ym(σ) ≫ a) ≫ idIntro.motiveSubst σ a = σ ≫ reflSubst idIntro a := by
  apply Yoneda.fullyFaithful.map_injective
  simp [Functor.map_comp, comp_reflSubst']

end IdIntro

/-- The full structure interpreting the natural model semantics for identity types
requires an `IdIntro` and an elimination rule `j` which satisfies a typing rule `j_tp`
and a β-rule `reflSubst_j`.
There is an equivalent formulation of these extra conditions later in `Id'`
that uses the language of polynomial endofunctors.

Note that the universe/model `N` for the motive `C` is different from the universe `M` that the
identity type lives in.
-/
protected structure Id (N : Universe Ctx) (i : IdIntro M) where
  j {Γ} (a : y(Γ) ⟶ M.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) :
    y(i.motiveCtx a) ⟶ N.Tm
  j_tp {Γ} (a : y(Γ) ⟶ M.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) : j a C r r_tp ≫ N.tp = C
  comp_j {Γ Δ} (σ : Δ ⟶ Γ)
    (a : y(Γ) ⟶ M.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) :
    ym(i.motiveSubst σ _) ≫ j a C r r_tp =
    j (ym(σ) ≫ a) (ym(i.motiveSubst σ _) ≫ C) (ym(σ) ≫ r) (by
      simp [r_tp, IdIntro.comp_reflSubst'_assoc])
  reflSubst_j {Γ} (a : y(Γ) ⟶ M.Tm) (C : y(IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
    (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C) :
    ym(i.reflSubst a) ≫ j a C r r_tp = r

namespace Id

variable {M} {N : Universe Ctx} {ii : M.IdIntro} (i : M.Id N ii) {Γ : Ctx} (a : y(Γ) ⟶ M.Tm)
  (C : y(ii.motiveCtx a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
  (r_tp : r ≫ N.tp = ym(ii.reflSubst a) ≫ C) (b : y(Γ) ⟶ M.Tm) (b_tp : b ≫ M.tp = a ≫ M.tp)
  (h : y(Γ) ⟶ M.Tm) (h_tp : h ≫ M.tp = ii.isKernelPair.lift b a (by aesop) ≫ ii.Id)

def endPtSubst : Γ ⟶ ii.motiveCtx a :=
  M.substCons (M.substCons (𝟙 _) _ b (by aesop)) _ h (by
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
`UniverseBase.IdElimBase` extends the structure `UniverseBase.IdIntro`
with a chosen pullback of `Id`
       i1
 i --------> M.Tm
 |            |
 |            |
i2           M.tp
 |            |
 V            V
 k --------> M.Ty
      Id

Again, we always have a pullback,
but when we construct a natural model,
this may not be definitionally equal to the pullbacks we construct,
for example using context extension.
-/
structure IdElimBase extends IdIntro M where
  i : Psh Ctx
  i1 : i ⟶ M.Tm
  i2 : i ⟶ k
  i_isPullback : IsPullback i1 i2 M.tp Id

namespace IdElimBase
variable {M} (idElimBase : IdElimBase M)

/-- The comparison map `M.tm ⟶ i` induced by the pullback universal property of `i`.

          refl
 M.Tm --------->
           i1
 |   i --------> M.Tm
 |   |            |
diag |            |
 |  i2           M.tp
 |   |            |
 |   V            V
 V   k --------> M.Ty
          Id
-/
def comparison : M.Tm ⟶ idElimBase.i :=
  idElimBase.i_isPullback.lift idElimBase.refl
  (IsPullback.lift idElimBase.isKernelPair (𝟙 M.Tm) (𝟙 M.Tm) (by simp))
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
@[simps] def iUvPoly : UvPoly idElimBase.i M.Tm := ⟨idElimBase.i2 ≫ idElimBase.k2, inferInstance⟩

/-- The functor part of the polynomial endofunctor `iOverUvPoly` -/
abbrev iFunctor : Psh Ctx ⥤ Psh Ctx := idElimBase.iUvPoly.functor

/-- Consider the comparison map `comparison : Tm ⟶ i` in the slice over `Tm`.
Then the contravariant action `UVPoly.verticalNatTrans` of taking `UvPoly` on a slice
results in a natural transformation `P_iOver ⟶ P_(𝟙 Tm)`
between the polynomial endofunctors `iUvPoly` and `UvPoly.id M.Tm` respectively.
  comparison
Tm ----> i
 \      /
 𝟙\    /i2 ≫ k2
   \  /
    VV
    Tm
-/
def verticalNatTrans : idElimBase.iFunctor ⟶ (UvPoly.id M.Tm).functor :=
    UvPoly.verticalNatTrans (UvPoly.id M.Tm) idElimBase.iUvPoly
  idElimBase.comparison (by simp [iUvPoly])

section reflCase

variable (i : IdIntro M) {N : Universe Ctx}

variable {Γ : Ctx} (a : y(Γ) ⟶ M.Tm) (r : y(Γ) ⟶ N.Tm)

lemma reflCase_aux : IsPullback (𝟙 y(Γ)) a a (UvPoly.id M.Tm).p :=
  have : IsIso (UvPoly.id M.Tm).p := by simp; infer_instance
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
def reflCase : y(Γ) ⟶ (UvPoly.id M.Tm).functor.obj N.Tm :=
  UvPoly.Equiv.mk' (UvPoly.id M.Tm) N.Tm a (R := y(Γ)) (f := 𝟙 _) (g := a)
  (reflCase_aux a) r
-- TODO: consider generalizing
-- TODO: consider showing UvPoly on identity `(P_𝟙_Y X)` is isomorphic to product `Y × X`

end reflCase

open IdElimBase IdIntro

section Equiv

variable {Γ : Ctx} {X : Psh Ctx}

section
variable (a : y(Γ) ⟶ M.Tm)
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

def toK : y(M.ext (a ≫ M.tp)) ⟶ idElimBase.k :=
  idElimBase.isKernelPair.lift (M.var _) (ym(M.disp _) ≫ a) (by simp)

lemma toK_comp_k1 : idElimBase.toK a ≫ idElimBase.k1 = M.var _ := by simp [toK]

lemma toK_comp_left {Δ} (σ : Δ ⟶ Γ) : toK idElimBase (ym(σ) ≫ a) =
    ym(M.substWk σ (a ≫ M.tp)) ≫ toK idElimBase a := by
  dsimp [toK]
  apply idElimBase.isKernelPair.hom_ext
  · rw! [Category.assoc]
    simp
  · simp only [IsKernelPair.lift_snd, Category.assoc]
    slice_rhs 1 2 => rw [← Functor.map_comp, substWk_disp]
    rw! [Category.assoc]
    simp

lemma ext_a_tp_isPullback : IsPullback (toK idElimBase a) ym(M.disp _)
    idElimBase.k2 a :=
  IsPullback.of_right' (M.disp_pullback _) idElimBase.isKernelPair

def toI : y(idElimBase.motiveCtx a) ⟶ idElimBase.i :=
  idElimBase.i_isPullback.lift (M.var _) (ym(M.disp _) ≫ toK idElimBase a)
  (by rw [(M.disp_pullback _).w]; simp [IdIntro.mkId, toK])

lemma toI_comp_i1 : idElimBase.toI a ≫ idElimBase.i1 = M.var _ := by simp [toI]

lemma toI_comp_i2 : idElimBase.toI a ≫ idElimBase.i2 = ym(M.disp _) ≫ idElimBase.toK a :=
  by simp [toI]

lemma toI_comp_left {Δ} (σ : Δ ⟶ Γ) : toI idElimBase (ym(σ) ≫ a) =
    ym(idElimBase.motiveSubst σ a) ≫ toI idElimBase a := by
  dsimp [toI]
  apply idElimBase.i_isPullback.hom_ext
  · simp [motiveSubst]
  · simp [toK_comp_left, motiveSubst, substWk, substCons]
    rfl

theorem motiveCtx_isPullback :
    IsPullback (toI idElimBase a) ym(M.disp _) idElimBase.i2 (toK idElimBase a) :=
  IsPullback.of_right' (M.disp_pullback _) idElimBase.i_isPullback

theorem motiveCtx_isPullback' :
    IsPullback (toI idElimBase a) (ym(M.disp (idElimBase.mkId (ym(M.disp (a ≫ M.tp)) ≫ a)
      (M.var (a ≫ M.tp)) (by simp))) ≫ ym(M.disp (a ≫ M.tp))) (iUvPoly idElimBase).p a :=
  IsPullback.paste_vert (idElimBase.motiveCtx_isPullback a)
    (idElimBase.ext_a_tp_isPullback a)

def equivMk (x : y(idElimBase.motiveCtx a) ⟶ X) : y(Γ) ⟶ idElimBase.iFunctor.obj X :=
  UvPoly.Equiv.mk' idElimBase.iUvPoly X a (idElimBase.motiveCtx_isPullback' a).flip x

def equivFst (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    y(Γ) ⟶ M.Tm :=
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
    (ym(M.disp (idElimBase.mkId (ym(M.disp (a ≫ M.tp)) ≫ a) (M.var (a ≫ M.tp)) _)) ≫
    ym(M.disp (a ≫ M.tp))) idElimBase.iUvPoly.p
    (UvPoly.Equiv.fst idElimBase.iUvPoly X pair) := (motiveCtx_isPullback' _ _)
  have H' : IsPullback (ym(M.disp
      (idElimBase.mkId (ym(M.disp (idElimBase.equivFst (ym(σ) ≫ pair) ≫ M.tp)) ≫
      idElimBase.equivFst (ym(σ) ≫ pair))
      (M.var (idElimBase.equivFst (ym(σ) ≫ pair) ≫ M.tp)) _)) ≫
      ym(M.disp (idElimBase.equivFst (ym(σ) ≫ pair) ≫ M.tp)))
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
    idElimBase.equivFst pair = UvPoly.Equiv.fst (UvPoly.id M.Tm) X
    (pair ≫ idElimBase.verticalNatTrans.app X) := by
  dsimp [equivFst, verticalNatTrans]
  rw [← UvPoly.fst_verticalNatTrans_app]

lemma equivSnd_verticalNatTrans_app {Γ : Ctx} {X : Psh Ctx}
    (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    UvPoly.Equiv.snd' (UvPoly.id M.Tm) X (pair ≫ idElimBase.verticalNatTrans.app X)
      (R := y(Γ)) (f := 𝟙 _) (g := idElimBase.equivFst pair) (by
        convert reflCase_aux (idElimBase.equivFst pair)
        rw [equivFst_verticalNatTrans_app]) =
      ym(idElimBase.reflSubst (idElimBase.equivFst pair)) ≫
      idElimBase.equivSnd pair :=
  calc _
  _ = _ ≫ idElimBase.equivSnd pair := by
    dsimp [equivSnd, verticalNatTrans]
    rw [UvPoly.snd'_verticalNatTrans_app (UvPoly.id M.Tm) idElimBase.iUvPoly
      (idElimBase.comparison) _ _ pair _]
    apply reflCase_aux (idElimBase.equivFst pair)
  _ = _ := by
    congr 1
    apply (M.disp_pullback _).hom_ext
    · conv => lhs; rw [← toI_comp_i1]
      simp [reflSubst, comparison, mkRefl]
    · apply (M.disp_pullback _).hom_ext
      · slice_lhs 3 4 => rw [← idElimBase.toK_comp_k1]
        slice_lhs 2 3 => rw [← idElimBase.toI_comp_i2]
        simp [reflSubst]
      · simp [reflSubst]

lemma equivMk_comp_verticalNatTrans_app {Γ : Ctx} {X : Psh Ctx} (a : y(Γ) ⟶ M.Tm)
    (x : y(idElimBase.motiveCtx a) ⟶ X) :
    idElimBase.equivMk a x ≫ (idElimBase.verticalNatTrans).app X =
    UvPoly.Equiv.mk' (UvPoly.id M.Tm) X a (R := y(Γ)) (f := 𝟙 _) (g := a)
    (reflCase_aux a) (ym(idElimBase.reflSubst a) ≫ x) := by
  dsimp only [equivMk, verticalNatTrans]
  rw [UvPoly.mk'_comp_verticalNatTrans_app (R' := y(Γ)) (f' := 𝟙 _) (g' := a)
    (H' := reflCase_aux a)]
  congr 2
  apply (M.disp_pullback _).hom_ext
  · conv => lhs; rw [← toI_comp_i1]
    simp [reflSubst, comparison, mkRefl]
  · apply (M.disp_pullback _).hom_ext
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
Fix `A : Ty` and `a : A` - we are working in the slice over `M.Tm`.
For any context `Γ`, any map `(a, r) : Γ → P_𝟙Tm Tm`
and `(a, C) : Γ ⟶ iFunctor Ty` such that `r ≫ M.tp = C[x/y, refl_x/p]`,
there is a map `(a,c) : Γ ⟶ iFunctor Tm` such that `c ≫ M.tp = C` and `c[a/y, refl_a/p] = r`.
Here we are thinking
  `Γ (y : A) (p : A) ⊢ C : Ty`
  `Γ ⊢ r : C[a/y, refl_a/p]`
  `Γ (y : A) (p : A) ⊢ c : Ty`
This witnesses the elimination principle for identity types since
we can take `J (y.p.C;x.r) := c`.
-/
structure Id' (N : Universe Ctx) extends IdElimBase M where
  weakPullback : WeakPullback
    (toIdElimBase.verticalNatTrans.app N.Tm)
    (toIdElimBase.iFunctor.map N.tp)
    ((UvPoly.id M.Tm).functor.map N.tp)
    (toIdElimBase.verticalNatTrans.app N.Ty)

namespace Id'

variable {M} {N : Universe Ctx} (i : Id' M N)

variable {Γ Δ : Ctx} (σ : Δ ⟶ Γ) (a : y(Γ) ⟶ M.Tm)
  (C : y(i.motiveCtx a) ⟶ N.Ty) (r : y(Γ) ⟶ N.Tm)
  (r_tp : r ≫ N.tp = ym(i.reflSubst a) ≫ C)

open IdElimBase IdIntro

lemma reflCase_aux : IsPullback (𝟙 y(Γ)) a a (UvPoly.id M.Tm).p :=
  have : IsIso (UvPoly.id M.Tm).p := by simp; infer_instance
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
def reflCase : y(Γ) ⟶ (UvPoly.id M.Tm).functor.obj N.Tm :=
  UvPoly.Equiv.mk' (UvPoly.id M.Tm) N.Tm a (R := y(Γ)) (f := 𝟙 _) (g := a)
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
  i.equivMk a C

lemma motive_comp_left : ym(σ) ≫ i.motive a C =
    i.motive (ym(σ) ≫ a) (ym(i.motiveSubst σ a) ≫ C) := by
  dsimp [motive, equivMk]
  rw [UvPoly.Equiv.mk'_comp_left (iUvPoly i.toIdElimBase) _ a
    (i.motiveCtx_isPullback' a).flip C ym(σ) _ rfl (i.motiveCtx_isPullback' _).flip]
  congr 2
  simp only [Functor.map_comp, iUvPoly_p, Category.assoc, motiveSubst, substWk, substCons,
    Functor.FullyFaithful.map_preimage]
  apply (M.disp_pullback _).hom_ext <;> simp only [IsPullback.lift_fst, IsPullback.lift_snd]
  · simp [← toI_comp_i1]
  · apply (M.disp_pullback _).hom_ext <;> simp
    · slice_lhs 3 4 => rw [← i.toK_comp_k1]
      slice_rhs 2 3 => rw [← i.toK_comp_k1]
      slice_lhs 2 3 => rw [← i.toI_comp_i2]
      slice_rhs 1 2 => rw [← i.toI_comp_i2]
      simp

def lift : y(Γ) ⟶ i.iFunctor.obj N.Tm :=
  i.weakPullback.coherentLift (reflCase a r) (motive i a C) (by
    dsimp only [motive, equivMk, verticalNatTrans, reflCase]
    rw [UvPoly.mk'_comp_verticalNatTrans_app (UvPoly.id M.Tm) i.iUvPoly i.comparison
      _ N.Ty a (i.motiveCtx_isPullback' a).flip C (reflCase_aux a),
      UvPoly.Equiv.mk'_comp_right, r_tp, reflSubst]
    congr
    apply (M.disp_pullback _).hom_ext
    · conv => right; rw [← toI_comp_i1]
      simp [mkRefl, comparison]
    · apply (M.disp_pullback _).hom_ext
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
    rw [UvPoly.Equiv.mk'_comp_left (UvPoly.id M.Tm) N.Tm a (reflCase_aux a) r ym(σ) _ rfl
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
    dsimp [lift, motive, IdElimBase.equivFst, IdElimBase.equivMk]
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
  simp only [IdElimBase.equivMk]
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
  have : (IsPullback.isoIsPullback y(Γ) M.Tm pb pb).inv = 𝟙 _ := by
    apply pb.hom_ext
    · simp only [IsPullback.isoIsPullback_inv_fst]
      simp
    · simp
  simp only [← heq_eq_eq, comp_eqToHom_heq_iff]
  rw! [equivFst_lift_eq]
  simp [this]

variable (b : y(Γ) ⟶ M.Tm) (b_tp : b ≫ M.tp = a ≫ M.tp)
  (h : y(Γ) ⟶ M.Tm) (h_tp : h ≫ M.tp = i.isKernelPair.lift b a (by aesop) ≫ i.Id)

def endPtSubst : Γ ⟶ i.motiveCtx a :=
  M.substCons (M.substCons (𝟙 _) _ b (by aesop)) _ h (by
    simp only [h_tp, IdIntro.mkId, ← Category.assoc]
    congr 1
    apply i.isKernelPair.hom_ext
    · simp
    · simp)

/-- `Id'` is equivalent to `Id` (one half). -/
def toId : M.Id N i.toIdIntro where
  j := i.j
  j_tp := i.j_tp
  comp_j := i.comp_j
  reflSubst_j := i.reflSubst_j
-- TODO: prove the other half of the equivalence.
-- Generalize this version so that the universe for elimination is not also `M`

end Id'

namespace Id

variable {M} (base : M.IdElimBase) {N : Universe Ctx}
  (i : M.Id N base.toIdIntro)

open IdIntro IdElimBase

variable {Γ} (ar : y(Γ) ⟶ (UvPoly.id M.Tm).functor.obj N.Tm)
  (aC : y(Γ) ⟶ (IdElimBase.iFunctor base).obj N.Ty)
  (hrC : ar ≫ (UvPoly.id M.Tm).functor.map N.tp =
    aC ≫ (IdElimBase.verticalNatTrans base).app N.Ty)

include hrC in
lemma fst_eq_fst : UvPoly.Equiv.fst _ _ ar = base.equivFst aC :=
  calc _
  _ = UvPoly.Equiv.fst _ _ (ar ≫ (UvPoly.id M.Tm).functor.map N.tp) := by
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
  rw [UvPoly.Equiv.snd'_comp_left (UvPoly.id M.Tm) N.Tm ar
    (Id'.reflCase_aux (UvPoly.Equiv.fst (UvPoly.id M.Tm) N.Tm ar)) ym(σ)
    (Id'.reflCase_aux _)]
  congr 1
  apply (Id'.reflCase_aux (UvPoly.Equiv.fst (UvPoly.id M.Tm) N.Tm ar)).hom_ext
  · simp only [IsPullback.lift_fst]
    simp
  · simp

include hrC in
lemma reflCase_comp_tp : reflCase ar ≫ N.tp =
    ym(base.reflSubst (base.equivFst aC)) ≫ motive base aC := by
  dsimp [reflCase, motive]
  rw! [← UvPoly.Equiv.snd'_comp_right, hrC]
  have H : IsPullback ym(M.disp (base.mkId
      (ym(M.disp (base.equivFst aC ≫ M.tp)) ≫ base.equivFst aC)
      (M.var (base.equivFst aC ≫ M.tp)) (by simp)) ≫
      M.disp (base.equivFst aC ≫ M.tp))
    (base.toI (base.equivFst aC)) (UvPoly.Equiv.fst base.iUvPoly N.Ty aC) base.iUvPoly.p := by
    convert (base.motiveCtx_isPullback' (base.equivFst aC)).flip
    simp
  rw! [UvPoly.snd'_verticalNatTrans_app
    (R := y(base.motiveCtx (base.equivFst aC)))
    (H := H)
    (R' := y(Γ)) (f' := 𝟙 _) (g' := UvPoly.Equiv.fst (UvPoly.id M.Tm) N.Tm ar)
    (H' := by
    rw [fst_eq_fst base ar aC hrC]
    exact Id'.reflCase_aux _)]
  simp only [Functor.map_comp, iUvPoly_p, equivSnd]
  congr 1
  apply (M.disp_pullback _).hom_ext <;>
    simp only [reflSubst, substCons_var, substCons_disp_functor_map, substCons_var]
  · simp [← base.toI_comp_i1 (base.equivFst aC), fst_eq_fst base ar aC hrC, mkRefl]
  · apply (M.disp_pullback _).hom_ext
    · rw! [fst_eq_fst base ar aC hrC]
      slice_lhs 3 4 => rw [← base.toK_comp_k1]
      slice_lhs 2 3 => rw [← base.toI_comp_i2]
      simp
    · simp

def lift : y(Γ) ⟶ (IdElimBase.iFunctor base).obj N.Tm :=
  base.equivMk (base.equivFst aC) (i.j (base.equivFst aC) (motive base aC)
   (reflCase ar) (reflCase_comp_tp base ar aC hrC))

lemma lift_fst : lift base i ar aC hrC ≫ base.verticalNatTrans.app N.Tm = ar := by
  dsimp only [lift]
  rw [equivMk_comp_verticalNatTrans_app]
  apply UvPoly.Equiv.ext' (UvPoly.id M.Tm) N.Tm (by convert reflCase_aux (base.equivFst aC); simp)
  · rw! [i.reflSubst_j]
    simp [reflCase, fst_eq_fst base ar aC hrC]
  · simp [fst_eq_fst base ar aC hrC]

lemma lift_snd : lift base i ar aC hrC ≫ base.iFunctor.map N.tp = aC := by
  dsimp only [lift, equivMk]
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
  dsimp [lift, equivMk]
  rw [UvPoly.Equiv.mk'_comp_left base.iUvPoly N.Tm (base.equivFst aC) _
    (i.j (base.equivFst aC) (motive base aC) (reflCase ar) _) ym(σ) _ rfl
    (by simp only [iUvPoly_p]; exact (base.motiveCtx_isPullback' _).flip)]
  congr 1
  have h := i.comp_j σ (base.equivFst aC) _ _ (reflCase_comp_tp base ar aC hrC)
  rw! (castMode := .all) [← comp_motive, ← comp_reflCase, ← equivFst_comp_left] at h
  rw [← h]
  congr 1
  simp only [iUvPoly_p, Category.assoc]
  apply (M.disp_pullback _).hom_ext
  · simp [toI_comp_left, ← toI_comp_i1]
  · apply (M.disp_pullback _).hom_ext
    · slice_rhs 3 4 => rw [← toK_comp_k1 base]
      slice_rhs 2 3 => rw [← toI_comp_i2]
      slice_lhs 3 4 => rw [← toK_comp_k1 base]
      slice_lhs 2 3 => rw [← toI_comp_i2]
      simp [toI_comp_left]
    · simp [motiveSubst, substWk]

def toId' : M.Id' N where
  __ := base
  weakPullback := RepPullbackCone.WeakPullback.mk
    ((IdElimBase.verticalNatTrans base).naturality _).symm
    (fun s => lift base i s.fst s.snd s.condition)
    (fun s => lift_fst base i s.fst s.snd s.condition)
    (fun s => lift_snd base i s.fst s.snd s.condition)
    (fun s _ σ => comp_lift base i s.fst s.snd s.condition σ)

end Id

end Universe

end NaturalModel
