/-! DEPRECATED in favor of `UHomSeqPis` -/
#exit

import GroupoidModel.Russell_PER_MS.NaturalModelBase

universe u

noncomputable section

open CategoryTheory Limits Opposite

class NaturalModelPi (Ctx : Type u) [SmallCategory.{u} Ctx] extends NaturalModelBase Ctx where
  Pi : toNaturalModelBase.Ptp.obj Ty ⟶ Ty
  lam : toNaturalModelBase.Ptp.obj Tm ⟶ Tm
  Pi_pullback : IsPullback lam (toNaturalModelBase.Ptp.map tp) tp Pi

namespace NaturalModelPi

variable {Ctx : Type u} [SmallCategory.{u} Ctx] (M : NaturalModelPi Ctx)

def mkPi {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ M.Ty) : y(Γ) ⟶ M.Ty :=
  M.Ptp_equiv ⟨A, B⟩ ≫ M.Pi

def mkLam {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (t : y(M.ext A) ⟶ M.Tm) : y(Γ) ⟶ M.Tm :=
  M.Ptp_equiv ⟨A, t⟩ ≫ M.lam

@[simp]
theorem mkLam_tp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ M.Ty)
    (t : y(M.ext A) ⟶ M.Tm) (t_tp : t ≫ M.tp = B) :
    M.mkLam A t ≫ M.tp = M.mkPi A B := by
  simp [mkLam, mkPi, NaturalModelPi.Pi_pullback.w]
  rw [← Category.assoc, M.Ptp_equiv_naturality, t_tp]

/--
```
Γ ⊢ A type  Γ.A ⊢ B type  Γ ⊢ f : ΠA.B
--------------------------------------
Γ.A ⊢ f[↑] v₀ : B
```
-/
def mkPApp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ M.Ty)
    (f : y(Γ) ⟶ M.Tm) (f_tp : f ≫ M.tp = M.mkPi A B) : y(M.ext A) ⟶ M.Tm := by
  let total : y(Γ) ⟶ M.Ptp.obj M.Tm :=
    NaturalModelPi.Pi_pullback.isLimit.lift <|
      PullbackCone.mk f (M.Ptp_equiv ⟨A, B⟩) f_tp
  convert (M.Ptp_equiv.symm total).snd
  have eq : total ≫ M.Ptp.map M.tp = M.Ptp_equiv ⟨A, B⟩ :=
    NaturalModelPi.Pi_pullback.isLimit.fac _ (some .right)
  simpa [M.Ptp_equiv_symm_naturality] using (M.Ptp_ext.mp eq).left.symm

  -- mkP_equiv.symm.injective
  -- have : total' ≫ (P tp).map tp = mkP A B :=
  --   NaturalModelPi.Pi_pullback.isLimit.fac _ (some .right)
  -- let total := mkP_equiv.1 total'
  -- have := mkP_equiv.symm.injective <|
  --   show mkP total.1 (total.2 ≫ tp) = mkP A B by
  --     rw [← mkP_app]; simp [mkP, total, this]
  -- have aeq : total.1 = A := congrArg Sigma.fst this
  -- refine ⟨aeq ▸ total, ?_⟩
  -- clear_value total'; cases this; rfl

@[simp]
theorem mkPApp_tp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ M.Ty)
    (f : y(Γ) ⟶ M.Tm) (f_tp : f ≫ M.tp = M.mkPi A B) :
    M.mkPApp A B f f_tp ≫ M.tp = B := by
  let total : y(Γ) ⟶ M.Ptp.obj M.Tm :=
    M.Pi_pullback.isLimit.lift <|
      PullbackCone.mk f (M.Ptp_equiv ⟨A, B⟩) f_tp
  -- have eq : total ≫ M.P.map tp = P_equiv ⟨A, B⟩ :=
  --   NaturalModelPi.Pi_pullback.isLimit.fac _ (some .right)
  -- unfold mkPApp
  sorry

def mkApp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ M.Ty)
    (f : y(Γ) ⟶ M.Tm) (f_tp : f ≫ M.tp = M.mkPi A B)
    (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) : y(Γ) ⟶ M.Tm :=
  M.inst A (M.mkPApp A B f f_tp) a a_tp

@[simp]
theorem mkApp_tp {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ M.Ty)
    (f : y(Γ) ⟶ M.Tm) (f_tp : f ≫ M.tp = M.mkPi A B)
    (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.mkApp A B f f_tp a a_tp ≫ M.tp = M.inst A B a a_tp :=
  sorry

-- semantic beta reduction
@[simp]
theorem mkApp_mkLam {Γ : Ctx} (A : y(Γ) ⟶ M.Ty) (B : y(M.ext A) ⟶ M.Ty)
    (t : y(M.ext A) ⟶ M.Tm) (t_tp : t ≫ M.tp = B)
    (lam_tp : M.mkLam A t ≫ M.tp = M.mkPi A B)
    (a : y(Γ) ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    -- TODO: rethink this; idk if we really want to have `inst`
    -- be a simp-NF; might be preferrable to just use `_ ≫ σ`
    M.mkApp A B (M.mkLam A t) lam_tp a a_tp = M.inst A t a a_tp := by
  sorry

end NaturalModelPi
