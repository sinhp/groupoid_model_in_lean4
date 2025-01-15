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

@[simp]
theorem substCons_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ M.Ty) (t : y(Δ) ⟶ M.Tm)
    (tTp : t ≫ M.tp = ym(σ) ≫ A) :
    M.substCons σ A t tTp ≫ M.disp A = σ := by
  apply Yoneda.fullyFaithful.map_injective
  simp [substCons]

@[simp]
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

show_panel_widgets [local ProofWidgets.GoalTypePanel]

/-- The bifunctor of 'types `A` with an `X`-object in context `Γ.A`'
`(Γ, X) ↦ (A : y(Γ.unop) ⟶ Ty) × (y(ext Γ.unop A) ⟶ X)`
associated to a natural model. -/
@[simps!]
def extFunctor : Ctxᵒᵖ ⥤ Psh Ctx ⥤ Type u :=
  curry.obj {
    obj := fun (Γ, X) => (A : y(Γ.unop) ⟶ M.Ty) × (y(M.ext A) ⟶ X)
    map := @fun (Δ, X) (Γ, Y) (σ, f) ⟨A, e⟩ =>
      let Aσ := ym(σ.unop) ≫ A -- TODO: use subst or whatever here
      ⟨Aσ,
      -- TODO: add functionality for widget to draw selected pullback squares
      (M.disp_pullback A).lift
        (M.var Aσ)
        ym(M.disp Aσ ≫ σ.unop)
        (by simp [(M.disp_pullback Aσ).w]) ≫
        e ≫ f⟩
    map_id := fun (Γ, _) => by
      refine funext fun be => ?_
      apply Sigma_hom_ext
      . simp
      . dsimp
        intro h
        generalize_proofs pb
        generalize ym(𝟙 (unop Γ)) ≫ be.fst = x at *
        cases h
        slice_lhs 1 1 => rw [show IsPullback.lift .. = 𝟙 _ by apply pb.hom_ext <;> simp]
        simp
    map_comp := fun (σ, _) (τ, _) => by
      refine funext fun ⟨b, e⟩ => ?_
      apply Sigma_hom_ext
      . simp
      . dsimp
        intro h
        generalize_proofs pb
        generalize ym(τ.unop ≫ σ.unop) ≫ b = x at *
        cases h
        simp only [← Category.assoc]
        congr 3
        apply pb.hom_ext <;> simp
  }

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
