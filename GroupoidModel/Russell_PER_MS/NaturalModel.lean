import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
import Poly.UvPoly.UPFan
import GroupoidModel.ForPoly
import SEq.Tactic.DepRewrite
import Poly.Widget.CommDiag

universe v u

noncomputable section

open CategoryTheory Limits Opposite

-- TODO: have the pretty-printer show these
notation:max "y(" Γ ")" => yoneda.obj Γ
notation:max "ym(" f ")" => yoneda.map f

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

@[reassoc (attr := simp)]
theorem substCons_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (t : y(Δ) ⟶ M.Tm)
    (tTp : t ≫ M.tp = ym(σ) ≫ A) :
    M.substCons σ A t tTp ≫ M.disp A = σ := by
  apply Yoneda.fullyFaithful.map_injective
  simp [substCons]

@[reassoc (attr := simp)]
theorem ym_substCons_ym_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (t : y(Δ) ⟶ M.Tm)
    (tTp : t ≫ M.tp = ym(σ) ≫ A) :
    ym(M.substCons σ A t tTp) ≫ ym(M.disp A) = ym(σ) := by
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

/-- `sec` is the section of `disp (α ≫ M.tp)` corresponding to `α`.

  ===== Γ ----------- α -----------¬
 ‖      ↓ sec                      V
 ‖   M.ext (α ≫ M.tp) -----------> M.Tm
 ‖      |                           |
 ‖      |                           |
 ‖    disp _                       M.tp
 ‖      |                           |
 ‖      V                           V
  ===== Γ ------- α ≫ M.tp ------> M.Ty -/
def sec {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) : Γ ⟶ M.ext (α ≫ M.tp) :=
  M.substCons (𝟙 Γ) (α ≫ M.tp) α (by simp)

@[reassoc (attr := simp)]
theorem sec_disp {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) : M.sec α ≫ M.disp (α ≫ M.tp) = 𝟙 _ := by
  simp [sec]

@[reassoc (attr := simp)]
theorem ym_sec_ym_disp {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) :
    ym(M.sec α) ≫ ym(M.disp (α ≫ M.tp)) = 𝟙 _ := by
  simp [sec]

@[reassoc (attr := simp)]
theorem sec_var {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) : ym(M.sec α) ≫ M.var (α ≫ M.tp) = α := by
  simp [sec]

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

@[reassoc]
theorem substWk_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) :
    M.substWk σ A ≫ M.disp A = M.disp (ym(σ) ≫ A) ≫ σ := by
  simp [substWk]

@[reassoc (attr := simp)]
theorem substWk_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) :
    ym(M.substWk σ A) ≫ M.var A = M.var (ym(σ) ≫ A) := by
  simp [substWk]

/--
```
Γ ⊢ A type  Γ.A ⊢ x ⟶ X  Γ ⊢ a : A
-----------------------------------
Γ ⊢ x[id.a] ⟶ X
```
-/
def inst {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (x : y(M.ext A) ⟶ X)
    (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) : y(Γ) ⟶ X :=
  ym(M.substCons (𝟙 _) A a (by simpa using a_tp)) ≫ x

@[reassoc (attr := simp)]
theorem inst_tp {N : NaturalModelBase Ctx} {Γ : Ctx}  (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ N.Ty)
    (t : y(M.ext A) ⟶ N.Tm) (t_tp : t ≫ N.tp = B)
    (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.inst A t a a_tp ≫ N.tp = M.inst A B a a_tp :=
  by simp [inst, t_tp]

@[simp]
theorem inst_wk {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (x : y(Γ) ⟶ X) (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.inst A (M.wk A x) a a_tp = x := by
  unfold inst wk
  slice_lhs 1 2 => rw [← yoneda.map_comp]; simp
  simp

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

/-! NOTE(WN): I am worried that the lemmas below leak implementation details of `UvPoly.equiv`:
`UvPoly.fstProj`, `UvPoly.lift`, etc.
`Poly` should provide enough API for us to black-box `UvPoly.equiv`
(in particular there should be a `compDomEquiv` that only mentions `UvPoly.equiv`). -/

@[simp]
theorem Ptp_equiv_apply_fst {Γ : Ctx} {X : Psh Ctx} (AB : y(Γ) ⟶ M.Ptp.obj X) :
    (M.Ptp_equiv AB).1 = AB ≫ M.uvPolyTp.fstProj _ :=
  rfl

theorem Ptp_equiv_symm_apply {Γ : Ctx} {X : Psh Ctx} (p : (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X)) :
    M.Ptp_equiv.symm p = M.uvPolyTp.lift p.1 ((pullbackIsoExt _ _).hom ≫ p.2) :=
  rfl

@[simp]
theorem Ptp_equiv_symm_apply_comp_fstProj
    {Γ : Ctx} {X : Psh Ctx} (p : (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X)):
    M.Ptp_equiv.symm p ≫ M.uvPolyTp.fstProj _ = p.1 := by
  sorry

/-! ## Polynomial composition `M.tp ▸ N.tp` -/

-- `private` lemma for the equivalence below.
private lemma lift_ev {Γ : Ctx} {AB : y(Γ) ⟶ M.Ptp.obj M.Ty} {α : y(Γ) ⟶ M.Tm}
    (hA : AB ≫ M.uvPolyTp.fstProj M.Ty = α ≫ M.tp) :
    pullback.lift AB α hA ≫ (UvPoly.PartialProduct.fan M.uvPolyTp M.Ty).snd =
      ym(M.sec α) ≫
        (M.disp_pullback _).lift (M.var _) ym(M.disp _)
          (by dsimp; rw [hA, (M.disp_pullback _).w]) ≫
        (M.Ptp_equiv AB).2 :=
  sorry

/-- A specialization of the universal property of `UvPoly.compDom` to `M.uvPolyTp`,
  using the chosen pullback `M.ext` instead of `pullback`. -/
def uvPolyTpCompDomEquiv (Γ : Ctx) :
    (y(Γ) ⟶ M.uvPolyTp.compDom M.uvPolyTp)
    ≃ (α : y(Γ) ⟶ M.Tm)
    × (B : y(M.ext (α ≫ M.tp)) ⟶ M.Ty)
    × (β : y(Γ) ⟶ M.Tm)
    ×' β ≫ M.tp = ym(M.sec α) ≫ B :=
  calc
    _ ≃ _ := UvPoly.compDomEquiv
    _ ≃ _ := {
      toFun := fun ⟨ AB, α, β, hA, hB ⟩ =>
        ⟨ α,
          (M.disp_pullback _).lift (M.var _) ym(M.disp _)
            (by dsimp; rw [hA, (M.disp_pullback _).w, uvPolyTp_p]) ≫
          (M.Ptp_equiv AB).2,
          β,
          hB.trans (M.lift_ev hA)
        ⟩
      invFun := fun ⟨ α, B, β, h ⟩ =>
        ⟨ M.Ptp_equiv.symm ⟨ α ≫ M.tp, B ⟩, α, β,
          by simp [uvPolyTp_p, Ptp_equiv_symm_apply_comp_fstProj],
          by
            refine h.trans ?_
            rw! [M.lift_ev, Equiv.apply_symm_apply]
            simp
        ⟩
      left_inv := fun ⟨ AB, α, β, hA, hB ⟩ => by
        congr!
        erw [Equiv.symm_apply_eq]
        refine Eq.trans ?_ (Sigma.eta _)
        ext : 1
        . dsimp
          erw [← hA, M.Ptp_equiv_apply_fst]
        . dsimp
          rw! (castMode := .all) [hA]
          simp; rfl
      right_inv := fun ⟨ α, B, β, h ⟩ => by
        congr!
        rw! [Equiv.apply_symm_apply]
        simp
    }

/-! ## Pi and Sigma types -/

structure NaturalModelPi where
  Pi : M.Ptp.obj M.Ty ⟶ M.Ty
  lam : M.Ptp.obj M.Tm ⟶ M.Tm
  Pi_pullback : IsPullback lam (M.Ptp.map M.tp) M.tp Pi

structure NaturalModelSigma where
  Sig : M.Ptp.obj M.Ty ⟶ M.Ty
  pair : UvPoly.compDom (uvPolyTp M) (uvPolyTp M) ⟶ M.Tm
  Sig_pullback : IsPullback pair ((uvPolyTp M).comp (uvPolyTp M)).p M.tp Sig

end NaturalModelBase
