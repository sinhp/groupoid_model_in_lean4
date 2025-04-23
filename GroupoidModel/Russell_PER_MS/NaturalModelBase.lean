import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
import Poly.UvPoly.UPFan
import GroupoidModel.ForPoly

universe v u

noncomputable section

open CategoryTheory Limits Opposite

notation:max "y(" Γ ")" => yoneda.obj Γ
notation:max "ym(" f ")" => yoneda.map f

/-- A representable map with choice of representability witnesses. -/
-- FIXME: should just be called `RepresentableNatTrans`.
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

variable {Ctx : Type u} [SmallCategory Ctx]  (M : NaturalModelBase Ctx)

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

theorem wk_tp {N : NaturalModelBase Ctx} {Γ : Ctx} {B : y(Γ) ⟶ N.Ty} (A : y(Γ) ⟶ M.Ty)
    (f : y(Γ) ⟶ N.Tm) (f_tp : f ≫ N.tp = B) :
    M.wk A f ≫ N.tp = M.wk A B := by
  simp [wk, f_tp]

@[simp]
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

@[reassoc (attr := simp)]
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

@[simp]
def inst_tp {N : NaturalModelBase Ctx} {Γ : Ctx}  (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ N.Ty)
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

/-! ## Polynomial functor on `tp` -/

variable (M : NaturalModelBase Ctx)

@[simps] def uvPolyTp : UvPoly M.Tm M.Ty := ⟨M.tp, inferInstance⟩
def Ptp : Psh Ctx ⥤ Psh Ctx := M.uvPolyTp.functor

-- TODO: establish a profunctor iso to replace `P_equiv` here.

/--
```
Γ ⊢ A type  y(Γ.A) ⟶ X
=======================
yΓ ⟶ P_tp(X)
```
-/
def Ptp_equiv {Γ : Ctx} {X : Psh Ctx} :
    (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X) ≃ (y(Γ) ⟶ M.Ptp.obj X) :=
  Equiv.symm <| (M.uvPolyTp.equiv y(Γ) X).trans <|
    Equiv.sigmaCongrRight fun A =>
      Iso.toEquiv <| (yoneda.obj X).mapIso <| Iso.op <|
        (M.disp_pullback A).isoPullback.trans (pullbackSymmetry M.tp A)

@[reassoc]
theorem Ptp_equiv_naturality {Γ : Ctx} {X Y : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (x : y(M.ext A) ⟶ X) (α : X ⟶ Y) :
    M.Ptp_equiv ⟨A, x⟩ ≫ M.Ptp.map α = M.Ptp_equiv ⟨A, x ≫ α⟩ := by
  simp [Ptp_equiv]
  sorry

theorem Ptp_equiv_symm_naturality {Γ : Ctx} {X Y : Psh Ctx}
    (x : y(Γ) ⟶ M.Ptp.obj X) (α : X ⟶ Y) :
    let S := M.Ptp_equiv.symm x
    M.Ptp_equiv.symm (x ≫ M.Ptp.map α) = ⟨S.1, S.2 ≫ α⟩ := by
  sorry

theorem Ptp_ext {Γ : Ctx} {X : Psh Ctx} {x y : y(Γ) ⟶ M.Ptp.obj X} :
    x = y ↔ (M.Ptp_equiv.symm x).fst = (M.Ptp_equiv.symm y).fst ∧
      HEq (M.Ptp_equiv.symm x).snd (M.Ptp_equiv.symm y).snd := by
  sorry

section
variable {Γ : Ctx} {α : y(Γ) ⟶ M.Tm} {A : y(Γ) ⟶ M.Ty}
  (h : α ≫ M.tp = A)

/-- See `sec` -/
def sec' : y(Γ) ⟶ y(M.ext A) :=
  (M.disp_pullback A).lift α (𝟙 _) (by simp [h])

@[simp] theorem sec'_var :
    M.sec' h ≫ M.var A = α :=
  (M.disp_pullback A).lift_fst _ _ _

@[simp] def sec'_disp : M.sec' h ≫ ym(M.disp A) = 𝟙 y(Γ) := by
  simp [sec']

end

/-- `sec` is the universal lift in the following diagram,
  which is a section of `Groupoidal.forget`

  ===== Γ -------α--------------¬
 ‖      ↓ sec                   V
 ‖   M.ext A ⋯ -------------> M.Tm
 ‖      |                        |
 ‖      |                        |
 ‖   forget                    M.tp
 ‖      |                        |
 ‖      V                        V
  ===== Γ ---- α ≫ M.tp -----> M.Ty
-/
def sec {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) :
    y(Γ) ⟶ y(M.ext (α ≫ M.tp)) :=
  M.sec' rfl

@[simp] theorem sec_var {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) :
    M.sec α ≫ M.var (α ≫ M.tp) = α :=
  sec'_var _ _

@[simp] theorem sec_disp {Γ : Ctx} (α : y(Γ) ⟶ M.Tm) :
    M.sec α ≫ ym(M.disp (α ≫ M.tp)) = 𝟙 _ :=
  sec'_disp _ _

-- FIXME The use of `IsPullback.flip` suggests an inconsistency in convention.
def pullbackIsoExt {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) :
  pullback A M.uvPolyTp.p ≅ yoneda.obj (M.ext A) :=
  (IsPullback.isoPullback (IsPullback.flip (M.disp_pullback A))).symm

/-- This is a specialization of `UvPoly.equiv`
  the universal property of `UvPoly` to `M.uvPolyTp`.
  We use the chosen pullback `M.ext A`
  instead of `pullback` from the `HasPullback` instance -/
def uvPolyTpEquiv {Γ : Ctx} {X : Psh Ctx} :
    (y(Γ) ⟶ M.uvPolyTp.functor.obj X)
    ≃ (A : y(Γ) ⟶ M.Ty) × (y(M.ext A) ⟶ X) :=
  (UvPoly.equiv _ _ _).trans
  (Equiv.sigmaCongrRight (fun _ =>
    Iso.homCongr (pullbackIsoExt _ _) (Iso.refl _)))

@[simp] theorem uvPolyTpEquiv_fst {Γ : Ctx} {X : Psh Ctx}
    (AB : y(Γ) ⟶ M.uvPolyTp.functor.obj X) :
    (M.uvPolyTpEquiv AB).1 = AB ≫ M.uvPolyTp.fstProj _ :=
  rfl

@[simp] theorem uvPolyTpEquiv_symm_snd {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    eqToHom (by simp) ≫ (M.uvPolyTpEquiv (M.uvPolyTpEquiv.symm ⟨A, B⟩)).snd = B := by
  apply eq_of_heq
  rw [eqToHom_comp_heq_iff]
  have h1 : M.uvPolyTpEquiv (M.uvPolyTpEquiv.symm ⟨A, B⟩) = ⟨A, B⟩ := by simp
  exact (Sigma.mk.inj_iff.mp ((Sigma.eta _).trans h1)).2
theorem uvPolyTpEquiv_symm {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X) :
    M.uvPolyTpEquiv.symm ⟨ A, B ⟩ =
    M.uvPolyTp.lift A ((pullbackIsoExt _ _).hom ≫ B) :=
  rfl

@[simp] theorem uvPolyTpEquiv_symm_proj
    {Γ : Ctx} {X : Psh Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ X):
    M.uvPolyTpEquiv.symm ⟨A, B⟩ ≫ M.uvPolyTp.fstProj _ = A := by
  simp [uvPolyTpEquiv_symm]

theorem lift_ev {Γ : Ctx} {AB : y(Γ) ⟶ M.uvPolyTp.functor.obj M.Ty}
    {α : y(Γ) ⟶ M.Tm} (hA : AB ≫ M.uvPolyTp.fstProj M.Ty = α ≫ M.tp)
    : pullback.lift AB α hA ≫ (UvPoly.PartialProduct.fan M.uvPolyTp M.Ty).snd
    = M.sec α ≫ eqToHom (by rw [← hA]; rfl) ≫ (M.uvPolyTpEquiv AB).2 :=
  sorry

/-- A specialization of the universal property of `UvPoly.compDom` to `M.uvPolyTp`,
  using the chosen pullback `M.ext` instead of `pullback`. -/
def uvPolyTpCompDomEquiv (Γ : Ctx) :
    (y(Γ) ⟶ M.uvPolyTp.compDom M.uvPolyTp)
    ≃ (α : y(Γ) ⟶ M.Tm)
    × (B : y(M.ext (α ≫ M.tp)) ⟶ M.Ty)
    × (β : y(Γ) ⟶ M.Tm)
    ×' β ≫ M.tp = M.sec α ≫ B :=
  calc
    _ ≃ _ := UvPoly.compDomEquiv
    _ ≃ _ := {
      toFun x := match x with
      | ⟨ AB, α, β, hA, hB ⟩ => ⟨ α,
        ⟨ eqToHom (by dsimp only [uvPolyTp] at hA; rw [← hA]; rfl)
        ≫ (M.uvPolyTpEquiv AB).2 , β , hB.trans (M.lift_ev hA) ⟩⟩
      invFun x := match x with
      | ⟨ α, B, β, h ⟩ => ⟨ M.uvPolyTpEquiv.symm ⟨ α ≫ M.tp, B ⟩, α, β, by
        fconstructor
        · simp [uvPolyTp_p, uvPolyTpEquiv_symm_proj]
        · refine h.trans ?_
          rw [M.lift_ev]
          congr 1
          rw [uvPolyTpEquiv_symm_snd] ⟩
      left_inv x := match x with
      | ⟨ AB, α, β, hA, hB ⟩ => by
        congr!
        dsimp only [uvPolyTpEquiv_fst]
        rw [Equiv.symm_apply_eq]
        refine Eq.trans ?_ (Sigma.eta _)
        ext
        · rw [M.uvPolyTpEquiv_fst, NatTrans.congr_app hA]
          simp
        · simp
      right_inv x := match x with
      | ⟨ α, B, β, h ⟩ => by
        congr!
        rw [uvPolyTpEquiv_symm_snd] }

end NaturalModelBase
