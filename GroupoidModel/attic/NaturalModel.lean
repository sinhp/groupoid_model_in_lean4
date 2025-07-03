import SEq.Tactic.DepRewrite
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
import Poly.UvPoly.UPFan
import GroupoidModel.ForPoly
import GroupoidModel.ForMathlib.Tactic.CategoryTheory.FunctorMap
import GroupoidModel.ForMathlib.CategoryTheory.Yoneda
import GroupoidModel.ForMathlib.CategoryTheory.RepPullbackCone

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

/--
```
Δ ⊢ σ : Γ.A
------------
Δ ⊢ ↑∘σ : Γ
```
-/
def substFst {Δ Γ : Ctx} {A : y(Γ) ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : Δ ⟶ Γ :=
  σ ≫ M.disp _

/--
```
Δ ⊢ σ : Γ.A
-------------------
Δ ⊢ v₀[σ] : A[↑∘σ]
```
-/
def substSnd {Δ Γ : Ctx} {A : y(Γ) ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : y(Δ) ⟶ M.Tm :=
  ym(σ) ≫ M.var _

theorem substSnd_tp {Δ Γ : Ctx} {A : y(Γ) ⟶ M.Ty} (σ : Δ ⟶ M.ext A) :
    M.substSnd σ ≫ M.tp = ym(M.substFst σ) ≫ A := by
  simp [substSnd, substFst]; rw [(M.disp_pullback _).w]

def wk {X : Psh Ctx} {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (f : y(Γ) ⟶ X) : y(M.ext A) ⟶ X :=
  ym(M.disp A) ≫ f

@[reassoc (attr := simp)]
theorem wk_tp {N : NaturalModelBase Ctx} {Γ : Ctx} {B : y(Γ) ⟶ N.Ty} (A : y(Γ) ⟶ M.Ty)
    (f : y(Γ) ⟶ N.Tm) (f_tp : f ≫ N.tp = B) :
    M.wk A f ≫ N.tp = M.wk A B := by
  simp [wk, f_tp]

@[reassoc (attr := simp)]
theorem var_tp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) : M.var A ≫ M.tp = M.wk A A := by
  simp [wk, (M.disp_pullback A).w]

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
  M.substCons (M.disp _ ≫ σ) A (M.var _) (by simp [wk])

@[functor_map (attr := reassoc)]
theorem substWk_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) :
    M.substWk σ A ≫ M.disp A = M.disp (ym(σ) ≫ A) ≫ σ := by
  simp [substWk]

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

@[reassoc (attr := simp)]
theorem sec_wk {Γ : Ctx} {X : Psh Ctx} (A : y(Γ) ⟶ M.Ty) (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A)
    (x : y(Γ) ⟶ X) : ym(M.sec A a a_tp) ≫ M.wk A x = x := by
  simp [sec, wk]

/-! ## Polynomial functor on `tp`

Specializations of results from the `Poly` package to natural models. -/

variable (M : NaturalModelBase Ctx)

@[simps] def uvPolyTp : UvPoly M.Tm M.Ty := ⟨M.tp, inferInstance⟩
def Ptp : Psh Ctx ⥤ Psh Ctx := M.uvPolyTp.functor

/--
```
yΓ ⟶ P_tp(X)
=======================
Γ ⊢ A type  y(Γ.A) ⟶ X
```
-/
@[simps!]
def Ptp_equiv {Γ : Ctx} {X : Psh Ctx} :
    (y(Γ) ⟶ M.Ptp.obj X) ≃ (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X) :=
  (UvPoly.equiv _ _ _).trans
    (Equiv.sigmaCongrRight fun _ =>
      (M.pullbackIsoExt _).homCongr (Iso.refl _))

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
  ((M.uvPolyTp.equiv y(Γ) X) AB).fst

/--
A map `(AB : y(Γ) ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : y(Γ) ⟶ M.Ty` and `B : y(M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.snd` is the `B` in this pair.
-/
def snd (AB : y(Γ) ⟶ M.Ptp.obj X) : y(M.ext (fst M AB)) ⟶ X :=
  (M.pullbackIsoExt _).inv ≫ ((M.uvPolyTp.equiv y(Γ) X) AB).snd

/--
A map `(AB : y(Γ) ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : y(Γ) ⟶ M.Ty` and `B : y(M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-/
def mk (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) : y(Γ) ⟶ M.Ptp.obj X :=
  (M.Ptp_equiv).symm ⟨ A , B ⟩

section
variable {Δ : Ctx} {σ : Δ ⟶ Γ} {AB : y(Γ) ⟶ M.Ptp.obj X}

theorem fst_naturality_left : fst M (ym(σ) ≫ AB) = ym(σ) ≫ fst M AB := by
  rfl

theorem snd_naturality_left : snd M (ym(σ) ≫ AB) = ym(M.substWk σ _) ≫ snd M AB := by
  sorry

end

end PtpEquiv

theorem Ptp_equiv_naturality_right {Γ : Ctx} {X Y : Psh Ctx}
    (x : y(Γ) ⟶ M.Ptp.obj X) (α : X ⟶ Y) :
    M.Ptp_equiv (x ≫ M.Ptp.map α) =
      let S := M.Ptp_equiv x
      ⟨S.1, S.2 ≫ α⟩ := by
  -- See https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Natural.20equivalences.20and.20kernel.20performance/with/513971849
  sorry

@[reassoc]
theorem Ptp_equiv_symm_naturality_right {Γ : Ctx} {X Y : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (x : y(M.ext A) ⟶ X) (α : X ⟶ Y) :
    M.Ptp_equiv.symm ⟨A, x⟩ ≫ M.Ptp.map α = M.Ptp_equiv.symm ⟨A, x ≫ α⟩ := by
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

/-- Universal property of `compDom`, decomposition (part 2).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `snd_tp`.
The map `dependent : y(M.ext (fst N ab ≫ M.tp)) ⟶ M.Ty`
is the `B : A ⟶ Type` in `(a : A) × (b : B a)`.
Here `A` is implicit, derived by the typing of `fst`, or `(a : A)`.
-/
def dependent (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
  y(M.ext (fst N ab ≫ M.tp)) ⟶ N.Ty := sorry

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `snd_tp`.
The map `snd : y(Γ) ⟶ M.Tm`
is the `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : y(Γ) ⟶ N.Tm := sorry

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `snd_tp`.
The equation `snd_tp` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_tp (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : snd N ab ≫ N.tp =
    ym(M.sec _ (fst N ab) rfl) ≫ dependent N ab := sorry

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : y(Γ) ⟶ M.Tm) (B : y(M.ext (α ≫ M.tp)) ⟶ N.Ty) (β : y(Γ) ⟶ N.Tm)
    (h : β ≫ N.tp = ym(M.sec _ α rfl) ≫ B) : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp :=
  sorry

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
    fst N ab ≫ M.tp = PtpEquiv.fst M (ab ≫ (M.uvPolyTp.comp _).p) := sorry

/-- Computation of `comp` (part 2).

`dependent_eq` is (part 2) of the computation that
      (α, B, β, h)
     Γ ⟶ compDom
      \        |
       \       | comp
(α ≫ tp, B)    |
         \     V
           >  P_tp Ty
Namely the second projection `B` agrees.
-/
theorem dependent_eq (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : dependent N ab =
    ym(eqToHom (by rw [fst_tp])) ≫ PtpEquiv.snd M (ab ≫ (M.uvPolyTp.comp _).p) := by
  sorry

def fst_naturality (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
    fst N (ym(σ) ≫ ab) = ym(σ) ≫ fst N ab := sorry

def dependent_naturality (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) : dependent N (ym(σ) ≫ ab)
    = ym(eqToHom (by simp [fst_naturality]) ≫ M.substWk σ _) ≫ dependent N ab := sorry

def snd_naturality (ab : y(Γ) ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
    snd N (ym(σ) ≫ ab) = ym(σ) ≫ snd N ab := sorry

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

namespace IsPullback

variable {E B} (intr : E ⟶ M.Tm) (typ : E ⟶ B) (form : B ⟶ M.Ty)

variable (intr_tp : intr ≫ M.tp = typ ≫ form)
    (liftExt : Π {Γ : Ctx} (b : y(Γ) ⟶ B),
      (f : y(M.ext (b ≫ form)) ⟶ E)
      ×' f ≫ intr = M.var (b ≫ form)
      ∧ f ≫ typ = ym(M.disp (b ≫ form)) ≫ b)

def lift (s : RepPullbackCone M.tp form) : y(s.pt) ⟶ E :=
  ym(M.sec (s.snd ≫ form) s.fst s.condition) ≫ (liftExt s.snd).1

theorem fac_left (s : RepPullbackCone M.tp form) :
    lift M intr typ form liftExt s ≫ intr = s.fst := by
  rw [lift, Category.assoc, (liftExt s.snd).2.1, sec_var]

theorem fac_right (s : RepPullbackCone M.tp form) :
    lift M intr typ form liftExt s ≫ typ = s.snd := by
  rw [lift, Category.assoc, (liftExt s.snd).2.2, ← Category.assoc,
    ← Functor.map_comp, sec_disp, CategoryTheory.Functor.map_id, Category.id_comp]

-- theorem lift_uniq
--     (uniqExt : Π {Γ : Ctx} (b : y(Γ) ⟶ B) (f1 f2 : y(M.ext (b ≫ form)) ⟶ E),
--       f1 ≫ intr = f2 ≫ intr ∧ f1 ≫ typ = f2 ≫ typ → f1 = f2)
--     (s : RepPullbackCone M.tp form) (m : y(s.pt) ⟶ E)
--     (hl : m ≫ intr = s.fst) (hr : m ≫ typ = s.snd) : m = lift M intr typ form liftExt s :=
--   have : ym(M.disp (s.snd ≫ form)) ≫ m =
--       ym(M.disp (s.snd ≫ form)) ≫ lift M intr typ form liftExt s := by
--     apply uniqExt
--     constructor
--     · rw [Functor.assoc]
--       sorry
--     · sorry
--   calc m
--     _ = ym(M.sec (s.snd ≫ form) s.fst s.condition ≫ M.disp (s.snd ≫ form)) ≫ m := by simp
--     _ = ym(M.sec (s.snd ≫ form) s.fst s.condition) ≫ (liftExt s.snd).1 := by
--       sorry
--       -- rw [Functor.map_comp, Category.assoc, this]

include intr_tp liftExt in
/-- To show that the square

  E ----------> M.Tm
  |               |
  |               |
  |               |
  |               |
  V               V
  B ----------> M.Ty

  is a pullback, it suffices to construct a unique lift from
  every context extension.
 y(ext) --------> E ----------> M.Tm
  |               |              |
  |               |              |
  |               |              |
  |               |              |
  V               V              V
 y(Γ) ----------> B ----------> M.Ty
-/
theorem of_existsUnique_liftExt_hom_ext
  (hom_ext : Π {Γ : Ctx} (f1 f2 : y(Γ) ⟶ E),
    f1 ≫ intr = f2 ≫ intr ∧ f1 ≫ typ = f2 ≫ typ → f1 = f2) :
  IsPullback intr typ M.tp form :=
  RepPullbackCone.is_pullback intr_tp (lift M intr typ form liftExt)
    (fac_left _ _ _ _ _)
    (fac_right _ _ _ _ _)
    (by
      intro s m hl hr
      apply hom_ext _ _ ⟨ ?_ , ?_ ⟩
      · rw [hl, fac_left]
      · rw [hr, fac_right])

end IsPullback

end NaturalModelBase
