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

variable {Ctx : Type u} [Category.{v, u} Ctx] (M : NaturalModelBase Ctx)

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

variable [SmallCategory Ctx] (M : NaturalModelBase Ctx)

def uvPolyTp : UvPoly M.Tm M.Ty := ⟨M.tp, inferInstance⟩
def uvPolyTpT : UvPoly.Total (Psh Ctx) := ⟨_, _, M.uvPolyTp⟩
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

end NaturalModelBase
