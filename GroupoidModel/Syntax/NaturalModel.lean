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

/-- A natural model with support for dependent types (and nothing more).
The data is a natural transformation with representable fibers,
stored as a choice of representative for each fiber. -/
structure NaturalModelBase (Ctx : Type u) [Category Ctx] where
  Tm : Psh Ctx
  Ty : Psh Ctx
  tp : Tm ⟶ Ty
  ext {Γ : Ctx} (A : y(Γ) ⟶ Ty) : Ctx
  disp {Γ : Ctx} (A : y(Γ) ⟶ Ty) : ext A ⟶ Γ
  var {Γ : Ctx} (A : y(Γ) ⟶ Ty) : y(ext A) ⟶ Tm
  disp_pullback {Γ : Ctx} (A : y(Γ) ⟶ Ty) :
    IsPullback (var A) ym(disp A) tp A

namespace NaturalModelBase

variable {Ctx : Type u} [SmallCategory Ctx] (M : NaturalModelBase Ctx)

@[simps! hom inv]
def pullbackIsoExt {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) :
    pullback A M.tp ≅ yoneda.obj (M.ext A) :=
  -- The use of `IsPullback.flip` suggests an inconsistency in convention.
  IsPullback.isoPullback (M.disp_pullback A).flip |>.symm

/-! ## Pullback of representable natural transformation -/

/-- Pull a natural model back along a type. -/
protected def pullback {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) : NaturalModelBase Ctx where
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
    NaturalModelBase Ctx where
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
  let i : y(M.ext A) ≅ pullback M.tp A := (M.disp_pullback A).isoPullback
  Yoneda.fullyFaithful.1 <| pullback.lift t ym(σ) t_tp ≫ i.inv

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
  sorry

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
def substWk' {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty)
    (A') (eq : ym(σ) ≫ A = A') : M.ext A' ⟶ M.ext A :=
  M.substCons (M.disp _ ≫ σ) A (M.var _) (by simp [eq])

@[functor_map (attr := reassoc)]
theorem substWk'_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (A' eq) :
    M.substWk' σ A A' eq ≫ M.disp A = M.disp A' ≫ σ := by
  simp [substWk']

@[reassoc (attr := simp)]
theorem substWk'_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (A' eq) :
    ym(M.substWk' σ A A' eq) ≫ M.var A = M.var A' := by
  simp [substWk']

/--
Weaken a substitution.
```
Δ ⊢ σ : Γ  Γ ⊢ A type
----------------------------------------
Δ.A[σ] ⊢ ↑≫σ : Γ  Δ.A[σ] ⊢ v₀ : A[↑≫σ]
----------------------------------------
Δ.A[σ] ⊢ (↑≫σ).v₀ : Γ.A
```
-/
def substWk {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) : M.ext (ym(σ) ≫ A) ⟶ M.ext A :=
  M.substWk' σ A _ rfl

@[functor_map (attr := reassoc)]
theorem substWk_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) :
    M.substWk σ A ≫ M.disp A = M.disp (ym(σ) ≫ A) ≫ σ := by
  simp [substWk, substWk'_disp]

@[reassoc (attr := simp)]
theorem substWk_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) :
    ym(M.substWk σ A) ≫ M.var A = M.var (ym(σ) ≫ A) := by
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
theorem comp_sec {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty)
    (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    σ ≫ M.sec A a a_tp = M.sec (ym(σ) ≫ A) (ym(σ) ≫ a) (by simp [a_tp]) ≫ M.substWk σ A := by
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
def snd (AB : y(Γ) ⟶ M.Ptp.obj X) : y(M.ext (fst M AB)) ⟶ X :=
  (M.pullbackIsoExt _).inv ≫ UvPoly.Equiv.snd M.uvPolyTp X AB

/--
A map `(AB : y(Γ) ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : y(Γ) ⟶ M.Ty` and `B : y(M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-/
def mk (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) : y(Γ) ⟶ M.Ptp.obj X :=
  UvPoly.Equiv.mk M.uvPolyTp X A ((M.pullbackIsoExt _).hom ≫ B)

@[simp]
lemma fst_mk (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    fst M (mk M A B) = A := by
  simp [fst, mk]

@[simp]
lemma snd_mk (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    snd M (mk M A B) = ym(eqToHom (by rw [fst_mk M A B])) ≫ B := by
  simp [snd, mk, UvPoly.Equiv.snd_mk]
  generalize_proofs _ _ _ _ _ _ h1 _ h2 h3
  suffices ∀ (A' : y(Γ) ⟶ M.Ty) (h1 : IsPullback ym(M.disp A') (M.var A') A' M.tp)
      (h2 : A' = A),
      h1.isoPullback.hom ≫ eqToHom (h2 ▸ rfl) ≫ h3.isoPullback.inv ≫ B =
      ym(eqToHom (by rw [h2])) ≫ B from
    this _ _ (by simp [fst])
  rintro _ _ rfl; simp

lemma snd_mk_heq (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    snd M (mk M A B) ≍ B := by
  simp [eqToHom_map]

section
variable {Δ : Ctx} {σ : Δ ⟶ Γ} {AB : y(Γ) ⟶ M.Ptp.obj X}

theorem fst_comp_left (σ : y(Δ) ⟶ y(Γ)) : fst M (σ ≫ AB) = σ ≫ fst M AB :=
  UvPoly.Equiv.fst_comp_left ..

theorem fst_comp_right {Y} (σ : X ⟶ Y) : fst M (AB ≫ M.Ptp.map σ) = fst M AB :=
  UvPoly.Equiv.fst_comp_right ..

attribute [-simp] pullbackIsoExt_inv in
theorem snd_comp_right {Y} (σ : X ⟶ Y) : snd M (AB ≫ M.Ptp.map σ) =
    ym(eqToHom congr(M.ext $(fst_comp_right ..))) ≫ snd M AB ≫ σ := by
  simp [snd]; conv_lhs => rhs; apply UvPoly.Equiv.snd_comp_right
  simp only [← Category.assoc]; congr! 2
  suffices ∀ A (h : A = fst M AB),
    (M.pullbackIsoExt A).inv ≫ eqToHom (h ▸ rfl) =
    ym(eqToHom (h ▸ rfl)) ≫ (M.pullbackIsoExt (fst M AB)).inv from this _ (fst_comp_right ..)
  rintro _ rfl; simp

theorem snd_comp_left : snd M (ym(σ) ≫ AB) = ym(M.substWk σ _) ≫ snd M AB := by
  sorry

end

end PtpEquiv

@[reassoc]
theorem PtpEquiv.mk_map {Γ : Ctx} {X Y : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (x : y(M.ext A) ⟶ X) (α : X ⟶ Y) :
    mk M A x ≫ M.Ptp.map α = mk M A (x ≫ α) := by
  sorry

/-! ## Polynomial composition `M.tp ▸ N.tp` -/

-- -- `private` lemma for the equivalence below.
-- private lemma lift_ev {Γ : Ctx} {N : NaturalModelBase Ctx}
--     {AB : y(Γ) ⟶ M.Ptp.obj N.Ty} {α : y(Γ) ⟶ M.Tm}
--     (hA : AB ≫ M.uvPolyTp.fstProj N.Ty = α ≫ M.tp) :
--     pullback.lift AB α hA ≫ (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).snd =
--       ym(M.sec (α ≫ M.tp) α rfl) ≫
--         (M.disp_pullback _).lift (M.var _) ym(M.disp _)
--           (by dsimp; rw [hA, (M.disp_pullback _).w]) ≫
--         (M.Ptp_equiv AB).2 :=
--   sorry

namespace compDomEquiv

variable {M} (N : NaturalModelBase Ctx) {Γ Δ : Ctx} (σ : Δ ⟶ Γ)

/-- Universal property of `compDom`, decomposition (part 1).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `snd_tp`. The map `fst : y(Γ) ⟶ M.Tm`
is the `(a : A)` in `(a : A) × (b : B a)`.
-/
def fst (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : y(Γ) ⟶ M.Tm :=
  ab ≫ pullback.snd N.tp (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).snd ≫
    pullback.snd (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).fst M.uvPolyTp.p

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
    fst N ab ≫ M.tp = PtpEquiv.fst M (ab ≫ (M.uvPolyTp.comp _).p) := by
  have : pullback.snd (M.uvPolyTp.fstProj N.Ty) M.tp ≫ M.tp =
    pullback.fst (M.uvPolyTp.fstProj N.Ty) M.tp ≫ M.uvPolyTp.fstProj N.Ty :=
      Eq.symm pullback.condition
  simp [PtpEquiv.fst, fst, this]
  rfl

/-- Universal property of `compDom`, decomposition (part 2).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `snd_tp`.
The map `dependent : y(M.ext (fst N ab ≫ M.tp)) ⟶ M.Ty`
is the `B : A ⟶ Type` in `(a : A) × (b : B a)`.
Here `A` is implicit, derived by the typing of `fst`, or `(a : A)`.
-/
def dependent (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
    y(M.ext (fst N ab ≫ M.tp)) ⟶ N.Ty :=
  ym(eqToHom (by rw [fst_tp])) ≫ PtpEquiv.snd M (ab ≫ (M.uvPolyTp.comp _).p)


/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `snd_tp`.
The map `snd : y(Γ) ⟶ M.Tm`
is the `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : y(Γ) ⟶ N.Tm :=
  ab ≫ pullback.fst N.tp (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).snd

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `snd_tp`.
The equation `snd_tp` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_tp (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : snd N ab ≫ N.tp =
    ym(M.sec _ (fst N ab) rfl) ≫ dependent N ab := by
  sorry

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : y(Γ) ⟶ M.Tm) (B : y(M.ext (α ≫ M.tp)) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm)
    (h : β ≫ N.tp = ym(M.sec _ α rfl) ≫ B) : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp :=
  sorry
  -- let AB := M.Ptp_equiv.symm ⟨α ≫ M.tp, B⟩
  -- pullback.lift
  --   β                     -- snd component
  --   (pullback.lift
  --     AB                  -- first part of dependent pair
  --     α                   -- fst component
  --     (by sorry))  -- proof they agree
  --   (by sorry)

def fst_naturality (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
    fst N (ym(σ) ≫ ab) = ym(σ) ≫ fst N ab := by
  simp only [fst, Category.assoc]

def dependent_naturality (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : dependent N (ym(σ) ≫ ab)
    = ym(eqToHom (by simp [fst_naturality]) ≫ M.substWk σ _) ≫ dependent N ab := by
  --simp[dependent, substWk, substCons]
  sorry

def snd_naturality (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
    snd N (ym(σ) ≫ ab) = ym(σ) ≫ snd N ab := by
  simp only [snd, Category.assoc]

end compDomEquiv

-- /-- A specialization of the universal property of `UvPoly.compDom` to `M.uvPolyTp`,
--   using the chosen pullback `M.ext` instead of `pullback`. -/
-- def uvPolyTpCompDomEquiv (N : NaturalModelBase Ctx) (Γ : Ctx) :
--     (y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp)
--     ≃ (α : y(Γ) ⟶ M.Tm)
--     × (B : y(M.ext (α ≫ M.tp)) ⟶ N.Ty)
--     × (β : y(Γ) ⟶ N.Tm)
--     ×' β ≫ N.tp = ym(M.sec (α ≫ M.tp) α rfl) ≫ B :=
--   calc
--     _ ≃ _ := UvPoly.compDomEquiv
--     _ ≃ _ := {
--       toFun := fun ⟨ AB, α, β, hA, hB ⟩ =>
--         ⟨ α,
--           (M.disp_pullback _).lift (M.var _) ym(M.disp _)
--             (by dsimp; rw [hA, (M.disp_pullback _).w, uvPolyTp_p]) ≫
--           (M.Ptp_equiv AB).2,
--           β,
--           hB.trans (M.lift_ev hA)
--         ⟩
--       invFun := fun ⟨ α, B, β, h ⟩ =>
--         ⟨ M.Ptp_equiv.symm ⟨ α ≫ M.tp, B ⟩, α, β,
--           by simp [uvPolyTp_p, Ptp_equiv_symm_apply_comp_fstProj],
--           by
--             refine h.trans ?_
--             rw! [M.lift_ev, Equiv.apply_symm_apply]
--             simp
--         ⟩
--       left_inv := fun ⟨ AB, α, β, hA, hB ⟩ => by
--         congr!
--         erw [Equiv.symm_apply_eq]
--         refine Eq.trans ?_ (Sigma.eta _)
--         ext : 1
--         . dsimp
--           erw [← hA, M.Ptp_equiv_apply_fst]
--         . dsimp
--           rw! (castMode := .all) [hA]
--           simp; rfl
--       right_inv := fun ⟨ α, B, β, h ⟩ => by
--         congr!
--         rw! [Equiv.apply_symm_apply]
--         simp
--     }

-- theorem uvPolyTpCompDomEquiv_apply_fst_tp (N : NaturalModelBase Ctx) {Γ}
--     (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
--     (M.uvPolyTpCompDomEquiv N Γ ab).fst ≫ M.tp
--     = (M.Ptp_equiv (ab ≫ (M.uvPolyTp.comp N.uvPolyTp).p)).fst :=
--   sorry

-- theorem uvPolyTpCompDomEquiv_apply_snd_fst_aux (N : NaturalModelBase Ctx)
--     {Γ : Ctx} (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
--     M.ext (((M.uvPolyTpCompDomEquiv N Γ) ab).fst ≫ M.tp) =
--     M.ext (M.Ptp_equiv (ab ≫ (M.uvPolyTp.comp N.uvPolyTp).p)).fst := by
--   rw [uvPolyTpCompDomEquiv_apply_fst_tp]

-- -- NOTE could define ym(eqToHom ⋯) =
-- -- (M.disp_pullback _).lift (M.var _) ym(M.disp _) (by
--       -- rw [(M.disp_pullback _).w, uvPolyTpCompDomEquiv_apply_fst_tp])
-- -- in this theorem, but it is convenient to have it as ym(⋯)
-- theorem uvPolyTpCompDomEquiv_apply_snd_fst (N : NaturalModelBase Ctx) {Γ : Ctx}
--     (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
--     (M.uvPolyTpCompDomEquiv N Γ ab).snd.fst
--     = (M.disp_pullback _).lift (M.var _) ym(M.disp _) (by
--         rw [(M.disp_pullback _).w, uvPolyTpCompDomEquiv_apply_fst_tp]) ≫
--       (M.Ptp_equiv (ab ≫ (M.uvPolyTp.comp N.uvPolyTp).p)).snd := by
--   sorry

/-! ## Pi and Sigma types -/

structure NaturalModelPi where
  Pi : M.Ptp.obj M.Ty ⟶ M.Ty
  lam : M.Ptp.obj M.Tm ⟶ M.Tm
  Pi_pullback : IsPullback lam (M.Ptp.map M.tp) M.tp Pi

structure NaturalModelSigma where
  Sig : M.Ptp.obj M.Ty ⟶ M.Ty
  pair : UvPoly.compDom (uvPolyTp M) (uvPolyTp M) ⟶ M.Tm
  Sig_pullback : IsPullback pair ((uvPolyTp M).comp (uvPolyTp M)).p M.tp Sig

/--
NaturalModelBase.IdBase consists of the following commutative square
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

def mkRefl (a : y(Γ) ⟶ M.Tm) : y(Γ) ⟶ M.Tm :=
  a ≫ idIntro.refl

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

end IdIntro

/--
This structure extends `IdIntro` with the data of an elimination form:
a chosen pullback of `Id`
       i1
 i --------> M.Tm
 |            |
 |            |
i2           M.tp
 |            |
 V            V
 k --------> M.Ty
      Id

Like in `IdIntro`, we require a choice of pullback.
-/
structure IdElimBase extends IdIntro M where
  i : Psh Ctx
  i1 : i ⟶ M.Tm
  i2 : i ⟶ k
  i_isPullback : IsPullback i1 i2 M.tp Id

/-- The identity `𝟙 Tm` as the signature for a polynomial endofunctor on `Psh Ctx`. -/
def tmUvPoly : UvPoly M.Tm M.Tm := ⟨𝟙 M.Tm, inferInstance⟩

namespace IdElimBase
variable (idElimBase : IdElimBase M)

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

/-- `i` over `Tm` can be informally thought of as the context extension
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty) (a : A)`
which is defined by the composition of (maps informally thought of as) context extensions
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty).(a b : A) ->> (A : Ty).(a : A)`
This is the signature for a polynomial functor `iUvPoly` on the presheaf category `Psh Ctx`.
-/
def iUvPoly : UvPoly idElimBase.i M.Tm := ⟨idElimBase.i2 ≫ idElimBase.k2, inferInstance⟩

/-- The functor part of the polynomial endofunctor `iOverUvPoly` -/
abbrev iFunctor : Psh Ctx ⥤ Psh Ctx := idElimBase.iUvPoly.functor

section Equiv

variable (idElimBase : M.IdElimBase) {Γ : Ctx} {X : Psh Ctx}


section
variable (a : y(Γ) ⟶ M.Tm)
/-
In the following lemmas we build the following diagram of pullbacks,
where `pullback` is the pullback of `i₂ ≫ k₂` along `a` given by `HasPullback`.
   ---------------->  X
  |                   Λ
  |                   |
  |                   | x
  |                   |
pullback ----> y(Γ.a≫tp.Id(...)) ------> i ------> Tm
  |                  |                   |         |
  |                  |                   | i₂      V
  |                  |                   |         Ty
  |                  V                   V
  |-----------> y(Γ.a≫tp) ----------->   k ------> Tm
  |                  |                   |    k₁   |
  |                  |                   |k₂       |tp
  |                  |                   |         |
  |                  V                   V         V
  ----------------> y(Γ) ------------>   Tm -----> Ty
                              a               tp
-/

def toK : y(M.ext (a ≫ M.tp)) ⟶ idElimBase.k :=
  idElimBase.isKernelPair.lift (M.var _) (ym(M.disp _) ≫ a) (by simp)

lemma ext_a_tp_isPullback : IsPullback (toK M idElimBase a) ym(M.disp _)
    idElimBase.k2 a :=
  IsPullback.of_right' (M.disp_pullback _) idElimBase.isKernelPair

def toExtATp : pullback a (iUvPoly M idElimBase).p ⟶ y(M.ext (a ≫ M.tp)) :=
  (ext_a_tp_isPullback M idElimBase a).lift
    (pullback.snd a (idElimBase.i2 ≫ idElimBase.k2) ≫ idElimBase.i2)
    (pullback.fst a (idElimBase.i2 ≫ idElimBase.k2)) (by simp [pullback.condition])

theorem pullback_isPullback :
    IsPullback (pullback.snd a (iUvPoly M idElimBase).p) (toExtATp M idElimBase a)
    idElimBase.i2 (toK M idElimBase a) :=
  IsPullback.of_bot' (IsPullback.of_hasPullback a (idElimBase.i2 ≫ idElimBase.k2)).flip
    (ext_a_tp_isPullback M idElimBase a)

def toI : y(idElimBase.motiveCtx a) ⟶ idElimBase.i :=
  idElimBase.i_isPullback.lift (M.var _) (ym(M.disp _) ≫ toK M idElimBase a)
  (by rw [(M.disp_pullback _).w]; simp [IdIntro.mkId, toK])

theorem motiveCtx_isPullback :
    IsPullback (toI M idElimBase a) ym(M.disp _) idElimBase.i2 (toK M idElimBase a) :=
  IsPullback.of_right' (M.disp_pullback _) idElimBase.i_isPullback

def pullbackIsoExt :
    pullback a (iUvPoly M idElimBase).p ≅ y(idElimBase.motiveCtx a) :=
  IsPullback.isoIsPullback _ _ (pullback_isPullback M idElimBase a)
    (motiveCtx_isPullback M idElimBase a)

def equivMk (x : y(idElimBase.motiveCtx a) ⟶ X) :
    y(Γ) ⟶ idElimBase.iFunctor.obj X :=
  UvPoly.Equiv.mk idElimBase.iUvPoly X a
    ((pullbackIsoExt M idElimBase a).hom ≫ x)

end

def equivFst (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    y(Γ) ⟶ M.Tm :=
  UvPoly.Equiv.fst idElimBase.iUvPoly X pair

def equivSnd (pair : y(Γ) ⟶ idElimBase.iFunctor.obj X) :
    y(idElimBase.motiveCtx (equivFst M idElimBase pair)) ⟶ X :=
  (pullbackIsoExt _ _ _).inv ≫ UvPoly.Equiv.snd idElimBase.iUvPoly X pair

end Equiv

/-- Consider the comparison map `comparison : Tm ⟶ i` in the slice over `Tm`.
Then the contravariant action `UVPoly.verticalNatTrans` of taking `UvPoly` on a slice
results in a natural transformation `P_iOver ⟶ P_(𝟙 Tm)`
between the polynomial endofunctors `iUvPoly` and `tmUvPoly` respectively.
  comparison
Tm ----> i
 \      /
 𝟙\    /i2 ≫ k2
   \  /
    VV
    Tm
-/
def verticalNatTrans : idElimBase.iFunctor ⟶ M.tmUvPoly.functor :=
    UvPoly.verticalNatTrans M.tmUvPoly idElimBase.iUvPoly
  idElimBase.comparison (by simp [iUvPoly, comparison, tmUvPoly])

end IdElimBase

/-- The full structure interpreting the natural model semantics for identity types
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
structure Id extends IdElimBase M where
  weakPullback : WeakPullback
    (toIdElimBase.verticalNatTrans.app M.Tm)
    (toIdElimBase.iFunctor.map M.tp)
    (M.tmUvPoly.functor.map M.tp)
    (toIdElimBase.verticalNatTrans.app M.Ty)

namespace Id

variable {M} (i : Id M)

variable {Γ : Ctx} (a : y(Γ) ⟶ M.Tm)
  (C : y(i.motiveCtx a) ⟶ M.Ty) (r : y(Γ) ⟶ M.Tm)
  (r_tp : r ≫ M.tp = ym(i.reflSubst a) ≫ C)

/-- The variable `r` witnesses the motive for the case `refl`,
This gives a map `(a,r) : Γ ⟶ P_𝟙Tm Tm ≅ Tm × Tm` where
```
    fst ≫ r
Tm <-- pullback ----> Tm
  <      |            ‖
   \     |fst         ‖ 𝟙_Tm
  r \    |            ‖
     \   V            ‖
      \  Γ  --------> Tm
              a
```
-/
def reflCase : y(Γ) ⟶ M.tmUvPoly.functor.obj M.Tm :=
  UvPoly.Equiv.mk M.tmUvPoly M.Tm a (pullback.fst _ _ ≫ r)
-- TODO: consider showing UvPoly on identity `(P_𝟙_Y X)` is isomorphic to product `Y × X`

/-- The variable `C` is the motive for elimination,
This gives a map `(a, C) : Γ ⟶ iFunctor Ty`
```
    C
Ty <-- y(motiveCtx) ----> i
  <---       |            |
      \      |            | i2 ≫ k2
     r \     |            |
        \    V            V
          -- Γ  --------> Tm
                  a
```
-/
def motive : y(Γ) ⟶ i.iFunctor.obj M.Ty :=
  i.equivMk M a C

def j : y(Γ) ⟶ i.iFunctor.obj M.Tm :=
  i.weakPullback.lift y(Γ) (reflCase a r) (motive i a C) (by
    simp [reflCase, motive]
    rw [UvPoly.Equiv.mk_comp_right]
    sorry
  )

lemma equivFst_eq : i.equivFst M (i.j a C r) = a := sorry

/-- The elimination rule for identity types.
  `Γ ⊢ A` is the type with a term `Γ ⊢ a : A`.
  `Γ (y : A) (h : Id(A,a,y)) ⊢ C` is the motive for the elimination.
  Then we obtain a section of the motive
  `Γ (y : A) (h : Id(A,a,y)) ⊢ mkJ : A`
-/
def mkJ : y(i.motiveCtx a) ⟶ M.Tm :=
  eqToHom (by rw [equivFst_eq]) ≫ i.equivSnd M (i.j a C r)

/-- Typing for elimination rule `J` -/
lemma mkJ_tp : mkJ i a C r ≫ M.tp = C := sorry

/-- β rule for identity types. Substituting `J` with `refl` gives the user-supplied value `r` -/
lemma reflSubst_mkJ : ym(i.reflSubst a) ≫ mkJ i a C r = r := sorry

variable (b : y(Γ) ⟶ M.Tm) (b_tp : b ≫ M.tp = a ≫ M.tp)
  (h : y(Γ) ⟶ M.Tm) (h_tp : h ≫ M.tp = i.isKernelPair.lift b a (by aesop) ≫ i.Id)

def endPtSubst : Γ ⟶ i.motiveCtx a :=
  M.substCons (M.substCons (𝟙 _) _ b (by aesop)) _ h (by
    simp only [h_tp, IdIntro.mkId, ← Category.assoc]
    congr 1
    apply i.isKernelPair.hom_ext
    · simp
    · simp)

/-- The elimination rule for identity types, now with the parameters as explicit terms.
  `Γ ⊢ A` is the type with a term `Γ ⊢ a : A`.
  `Γ (y : A) (p : Id(A,a,y)) ⊢ C` is the motive for the elimination.
  `Γ ⊢ b : A` is a second term in `A` and `Γ ⊢ h : Id(A,a,b)` is a path from `a` to `b`.
  Then `Γ ⊢ mkJ' : C [b/y,h/p]` is a term of the motive with `b` and `h` substituted
-/
def mkJ' : y(Γ) ⟶ M.Tm :=
  ym(i.endPtSubst a b b_tp h h_tp) ≫ mkJ i a C r

/-- Typing for elimination rule `J` -/
lemma mkJ'_tp : mkJ' i a C r b b_tp h h_tp ≫ M.tp = ym(i.endPtSubst a b b_tp h h_tp) ≫ C := by
  rw [mkJ', Category.assoc, mkJ_tp]

/-- β rule for identity types. Substituting `J` with `refl` gives the user-supplied value `r` -/
lemma mkJ'_refl : mkJ' i a C r a rfl (i.mkRefl a) (by aesop) = r :=
  calc ym(i.endPtSubst a a rfl (i.mkRefl a) _) ≫ mkJ i a C r
    _ = ym(i.reflSubst a) ≫ mkJ i a C r := rfl
    _ = r := by rw [reflSubst_mkJ]

end Id

end NaturalModelBase
