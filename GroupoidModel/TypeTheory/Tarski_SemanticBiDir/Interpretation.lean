import GroupoidModel.NaturalModel

/-! Helper definitions for interpretation in a natural model. -/

noncomputable section
open CategoryTheory NaturalModel Limits

/- Category of contexts `Ctx` with a natural model `M`. -/
universe u
variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx] [M : NaturalModel Ctx]

/-! Interpretation of substitutions. -/

/--
```
Δ ⊢ σ : Γ  Γ ⊢ A type  Δ ⊢ t : A[σ]
-----------------------------------
Δ ⊢ σ.t : Γ.A
``` -/
def substCons {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ Ty)
    (t : y(Δ) ⟶ Tm) (t_tp : t ≫ tp = yoneda.map σ ≫ A) :
    Δ ⟶ ext Γ A :=
  let i : y(ext Γ A) ≅ pullback tp A := (disp_pullback A).isoPullback
  Yoneda.fullyFaithful.1 <| pullback.lift t (yoneda.map σ) t_tp ≫ i.inv

@[simp]
theorem substCons_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ Ty) (t : y(Δ) ⟶ Tm)
    (tTp : t ≫ tp = yoneda.map σ ≫ A) :
    substCons σ A t tTp ≫ disp Γ A = σ := by
  apply Yoneda.fullyFaithful.map_injective
  simp [substCons]

@[simp]
theorem substCons_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : y(Γ) ⟶ Ty) (t : y(Δ) ⟶ Tm)
    (aTp : t ≫ tp = yoneda.map σ ≫ A) :
    yoneda.map (substCons σ A t aTp) ≫ var Γ A = t := by
  simp [substCons]

/--
```
Δ ⊢ σ : Γ.A
--------------
Δ ⊢ ↑_A∘σ : Γ
``` -/
def substFst {Δ Γ: Ctx} {A : y(Γ) ⟶ Ty} (σ : Δ ⟶ ext Γ A) : Δ ⟶ Γ :=
  σ ≫ disp _ _

/--
```
Δ ⊢ σ : Γ.A
---------------------
Δ ⊢ v₀[σ] : A[↑_A∘σ]
``` -/
def substSnd {Δ Γ : Ctx} {A : y(Γ) ⟶ Ty} (σ : Δ ⟶ ext Γ A) : y(Δ) ⟶ Tm :=
  yoneda.map σ ≫ var _ _

theorem substSnd_tp {Δ Γ : Ctx} {A : y(Γ) ⟶ Ty} (σ : Δ ⟶ ext Γ A) :
    substSnd σ ≫ tp = yoneda.map (substFst σ) ≫ A := by
  simp [substSnd, substFst]; rw [(disp_pullback _).w]

/-- Weaken an entity-in-context
```
Γ.A ⊢ X[f]
--------------
Γ ⊢ X[f[↑_A]]
``` -/
def wk {X : Psh Ctx} {Γ : Ctx} (A : y(Γ) ⟶ Ty) (f : y(Γ) ⟶ X) : y(ext Γ A) ⟶ X :=
  yoneda.map (disp Γ A) ≫ f

/--
```
Γ ⊢ A type  Γ.A ⊢ σ : X  Γ ⊢ a : A
----------------------------------
Γ ⊢ σ[id.a] : X
``` -/
def inst {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ Ty) (σ : y(ext Γ A) ⟶ X)
    (a : y(Γ) ⟶ Tm) (a_tp : a ≫ tp = A) : y(Γ) ⟶ X :=
  yoneda.map (substCons (𝟙 _) A a (by simpa using a_tp)) ≫ σ

@[simp]
def inst_tp {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty)
    (t : y(ext Γ A) ⟶ Tm) (t_tp : t ≫ tp = B)
    (a : y(Γ) ⟶ Tm) (a_tp : a ≫ tp = A) :
    inst A t a a_tp ≫ tp = inst A B a a_tp :=
   by simp [inst, t_tp]

@[simp]
theorem inst_wk {Γ : Ctx} {X : Psh Ctx}
    (A : y(Γ) ⟶ Ty) (σ : y(Γ) ⟶ X) (a : y(Γ) ⟶ Tm) (a_tp : a ≫ tp = A) :
    inst A (wk A σ) a a_tp = σ := by
  unfold inst wk
  slice_lhs 1 2 => rw [← yoneda.map_comp]; simp
  simp

-- woohoo, no inst_wk' lemma!

-- @[simp]
-- theorem inst'_var₀ {Γ : CCtx Ctx} (A : Γ.ty) (t : Γ.typed A) :
--     Γ.inst' A (Γ.wk A A) (var₀ A) t = t.cast (Γ.inst_wk A _ _).symm := by
--   apply Subtype.eq
--   simp [inst', inst, var₀, var₀_aux]

/-! Interpretation of Π/Σ. -/

/--
```
Γ ⊢ A type  Γ.A ⊢ X
===================
yΓ ⟶ P_tp(X)
``` -/
def P_equiv {Γ : Ctx} {X : Psh Ctx} :
    (A : y(Γ) ⟶ Ty) × (y(ext Γ A) ⟶ X) ≃ (y(Γ) ⟶ (P tp).obj X) :=
  Equiv.symm <| ((uvPoly tp).equiv y(Γ) X).trans <|
    Equiv.sigmaCongrRight fun A =>
      Iso.toEquiv <| (yoneda.obj X).mapIso <| Iso.op <|
        (disp_pullback A).isoPullback.trans (pullbackSymmetry tp A)

theorem P_equiv_naturality {Γ : Ctx} {X Y : Psh Ctx}
    (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ X) (F : X ⟶ Y) :
    P_equiv ⟨A, B⟩ ≫ (P tp).map F = P_equiv ⟨A, B ≫ F⟩ := by
  simp [P_equiv]
  sorry

theorem P_equiv_symm_naturality {Γ : Ctx} {X Y : Psh Ctx}
    (f : y(Γ) ⟶ (P tp).obj X) (F : X ⟶ Y) :
    let S := P_equiv.symm f
    P_equiv.symm (f ≫ (P tp).map F) = ⟨S.1, S.2 ≫ F⟩ := by
  sorry

theorem P_ext {Γ : Ctx} {X : Psh Ctx} {f g : y(Γ) ⟶ (P tp).obj X} :
    f = g ↔ (P_equiv.symm f).fst = (P_equiv.symm g).fst ∧
      HEq (P_equiv.symm f).snd (P_equiv.symm g).snd := by
  sorry

def mkPi {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty) : y(Γ) ⟶ Ty :=
  P_equiv ⟨A, B⟩ ≫ NaturalModelPi.Pi

def mkLam {Γ : Ctx} (A : y(Γ) ⟶ Ty) (t : y(ext Γ A) ⟶ Tm) : y(Γ) ⟶ Tm :=
  P_equiv ⟨A, t⟩ ≫ NaturalModelPi.lam

@[simp]
theorem mkLam_tp {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty)
    (t : y(ext Γ A) ⟶ Tm) (t_tp : t ≫ tp = B) :
    mkLam A t ≫ tp = mkPi A B := by
  simp [mkLam, mkPi, NaturalModelPi.Pi_pullback.w]
  rw [← Category.assoc, P_equiv_naturality, t_tp]

/--
```
Γ ⊢ A type  Γ.A ⊢ B type  Γ ⊢ f : ΠA.B
--------------------------------------
Γ.A ⊢ f[↑_A] v₀ : B
``` -/
def mkPApp {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty)
    (f : y(Γ) ⟶ Tm) (f_tp : f ≫ tp = mkPi A B) : y(ext Γ A) ⟶ Tm := by
  let total : y(Γ) ⟶ (P tp).obj Tm :=
    NaturalModelPi.Pi_pullback.isLimit.lift <|
      PullbackCone.mk f (P_equiv ⟨A, B⟩) f_tp
  convert (P_equiv.symm total).snd
  have eq : total ≫ (P tp).map tp = P_equiv ⟨A, B⟩ :=
    NaturalModelPi.Pi_pullback.isLimit.fac _ (some .right)
  simpa [P_equiv_symm_naturality] using (P_ext.mp eq).left.symm

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
theorem mkPApp_tp {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty)
    (f : y(Γ) ⟶ Tm) (f_tp : f ≫ tp = mkPi A B) : mkPApp A B f f_tp ≫ tp = B := by
  let total : y(Γ) ⟶ (P tp).obj Tm :=
    NaturalModelPi.Pi_pullback.isLimit.lift <|
      PullbackCone.mk f (P_equiv ⟨A, B⟩) f_tp
  have eq : total ≫ (P tp).map tp = P_equiv ⟨A, B⟩ :=
    NaturalModelPi.Pi_pullback.isLimit.fac _ (some .right)
  unfold mkPApp
  sorry

def mkApp {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty)
    (f : y(Γ) ⟶ Tm) (f_tp : f ≫ tp = mkPi A B)
    (a : y(Γ) ⟶ Tm) (a_tp : a ≫ tp = A) : y(Γ) ⟶ Tm :=
  inst A (mkPApp A B f f_tp) a a_tp

@[simp]
theorem mkApp_tp {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty)
    (f : y(Γ) ⟶ Tm) (f_tp : f ≫ tp = mkPi A B)
    (a : y(Γ) ⟶ Tm) (a_tp : a ≫ tp = A) :
    mkApp A B f f_tp a a_tp ≫ tp = sorry :=
  sorry

-- semantic beta reduction
set_option autoImplicit true in
@[simp]
theorem mkApp_mkLam {Γ : Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ Ty)
    (t : y(ext Γ A) ⟶ Tm) (t_tp : t ≫ tp = B)
    (lam_tp : mkLam A t ≫ tp = mkPi A B)
    (a : y(Γ) ⟶ Tm) (a_tp : a ≫ tp = A) :
    -- TODO: rethink this; idk if we really want to have `inst`
    -- be a simp-NF; i think it'd be preferrable to use `σ ≫ _`
    mkApp A B (mkLam A t) lam_tp a a_tp = inst A t a a_tp := by
  sorry

/-! Interpretation of universes. -/

/-- `Γ ⊢ U type` -/
def wU {Γ} : y(Γ) ⟶ M.Ty := yoneda.map (terminal.from Γ) ≫ U

@[simp]
theorem comp_wU {Δ Γ : Ctx} (f : y(Δ) ⟶ y(Γ)) : f ≫ wU = wU := by
  aesop (add norm wU)

/-! # OLD STUFF BELOW -/

/-! Context stacks and entities-in-context. -/

/-- `CtxStack Γ` witnesses a sequence of `n` context extension operations
that built the semantic context `Γ`. -/
inductive CtxStack : Ctx → Type u where
  | nil : CtxStack (⊤_ Ctx)
  | cons {Γ} (A : y(Γ) ⟶ Ty) : CtxStack Γ → CtxStack (M.ext Γ A)

variable (Ctx) in
/-- A "contextual" context (as in Cartmell's contextual categories),
i.e., one of the form `1.Aₙ₋₁.….A₀`,
together with the list `[Aₙ₋₁, …, A₀]`. -/
-- The utility of `CCtx` is in being a semantic context that can be destructured.
def CCtx : Type u := Σ Γ : Ctx, CtxStack Γ

namespace CCtx

abbrev ty (Γ : CCtx Ctx) := y(Γ.1) ⟶ Ty
abbrev tm (Γ : CCtx Ctx) := y(Γ.1) ⟶ Tm

-- TODO(WN): generalize away from "contextual" contexts by defining
-- def Typed (Γ : Ctx) (A : y(Γ) ⟶ Ty) := { x : y(Γ) ⟶ Tm // x ≫ tp = A }
-- without mentioning stacks.
-- Most of the `mkBlah` utilities will go through except for variables.
-- Or don't use `typed` at all.

def typed (Γ : CCtx Ctx) (A : Γ.ty) := { x : Γ.tm // x ≫ tp = A }

def nil : CCtx Ctx := ⟨_, .nil⟩
def cons (Γ : CCtx Ctx) (A : Γ.ty) : CCtx Ctx := ⟨_, .cons A Γ.2⟩

@[simp] theorem cons_fst (Γ : CCtx Ctx) (A : Γ.ty) :
    (Γ.cons A).1 = ext Γ.1 A := rfl

/-- Weaken an entity-in-context `Γ.A ⊢ X` to `Γ ⊢ X[↑_A]`. -/
def wk {X : Psh Ctx} (Γ : CCtx Ctx) (A : Γ.ty)
    (f : y(Γ.1) ⟶ X) : y((Γ.cons A).1) ⟶ X :=
  yoneda.map (disp Γ.1 A) ≫ f

/-- The `i`-th var `1.Aₙ₋₁.….A₀ ⊢ vᵢ : Aᵢ` if `i < n`,
otherwise `none`. -/
protected def var (Γ : CCtx Ctx) (i : ℕ) : Option Γ.tm :=
  match Γ, i with
  | ⟨_, .nil⟩,      _   => .none
  | ⟨_, .cons _ _⟩, 0   => pure <| var ..
  | ⟨_, .cons _ Γ⟩, n+1 => CCtx.wk ⟨_, Γ⟩ _ <$> CCtx.var ⟨_, Γ⟩ n

def var₀_aux {Γ : CCtx Ctx} (A : Γ.ty) : (Γ.cons A).tm :=
  var Γ.1 A

def var₀_aux_tp {Γ : CCtx Ctx} (A : Γ.ty) :
    Γ.var₀_aux A ≫ tp = wk Γ A A :=
  sorry

def var₀ {Γ : CCtx Ctx} (A : Γ.ty) : (Γ.cons A).typed (wk Γ A A) :=
  ⟨var₀_aux A, var₀_aux_tp A⟩

/--
```
Γ ⊢ A type  Γ.A ⊢ σ : X  Γ ⊢ a : A
----------------------------------
Γ ⊢ σ[id.a] : X
``` -/
def inst {Γ : CCtx Ctx} {X : Psh Ctx}
    (A : Γ.ty) (σ : y((Γ.cons A).1) ⟶ X) (a : Γ.typed A) : y(Γ.1) ⟶ X :=
  yoneda.map (substCons (𝟙 _) A a.1 (by simpa using a.2)) ≫ σ

@[simp]
theorem inst_wk {Γ : CCtx Ctx} {X : Psh Ctx}
    (A : Γ.ty) (σ : y(Γ.1) ⟶ X) (a : Γ.typed A) :
    Γ.inst A (Γ.wk A σ) a = σ := by
  unfold inst wk
  slice_lhs 1 2 => rw [← yoneda.map_comp]; simp
  simp

-- TODO: organize all the substitution-related inst/subst/wk utilities.
-- They come in two version: raw and for `typed`/`Typed`.
def inst' {Γ : CCtx Ctx} (A : Γ.ty) (B : (Γ.cons A).ty)
    (t : (Γ.cons A).typed B) (a : Γ.typed A) :
    Γ.typed (Γ.inst A B a) :=
  ⟨Γ.inst A t.1 a, by simp [inst, t.2]⟩

def wk' (Γ : CCtx Ctx) (A B : Γ.ty)
    (a : Γ.typed A) : (Γ.cons B).typed (Γ.wk B A) :=
  ⟨Γ.wk B a.1, by simp [wk, a.2]⟩

@[simp]
theorem cast_fst {Γ : CCtx Ctx} (A B : Γ.ty) (eq : A = B) (a : Γ.typed A) :
    (eq ▸ a).1 = a.1 :=
  by cases eq; rfl

def typed.cast {Γ : CCtx Ctx} {A B : Γ.ty} (a : Γ.typed A) (eq : A = B) : Γ.typed B :=
  ⟨a.1, a.2.trans eq⟩

@[simp]
theorem typed.cast_cast {Γ : CCtx Ctx} (A B C : Γ.ty) (eq : A = B) (eq' : B = C) (a : Γ.typed A) :
    (a.cast eq).cast eq' = a.cast (eq.trans eq') :=
  rfl

@[simp]
theorem typed.cast_fst {Γ : CCtx Ctx} {A B : Γ.ty} (a : Γ.typed A) (eq : A = B) :
    (a.cast eq).1 = a.1 :=
  rfl

@[simp]
theorem typed.cast_rfl {Γ : CCtx Ctx} {A : Γ.ty} (a : Γ.typed A) :
    a.cast rfl = a :=
  rfl

@[simp]
theorem inst'_wk' {Γ : CCtx Ctx} (A : Γ.ty) (B : Γ.ty)
    (t : Γ.typed A) (a : Γ.typed B) :
    -- TODO: and here we got ourselves into DTT hell :D
    -- Idk about this whole `typed` indexed family business.
    -- It'd be nicer to have some `yΓ ⟶ Tm` arrows floating around
    -- that are all comparable,
    -- plus simp lemmas that tell us what their types are.
    Γ.inst' B (Γ.wk B A) (Γ.wk' A B t) a = t.cast (Γ.inst_wk B _ a).symm := by
  unfold inst' wk'
  apply Subtype.eq
  simp

@[simp]
theorem inst'_var₀ {Γ : CCtx Ctx} (A : Γ.ty) (t : Γ.typed A) :
    Γ.inst' A (Γ.wk A A) (var₀ A) t = t.cast (Γ.inst_wk A _ _).symm := by
  apply Subtype.eq
  simp [inst', inst, var₀, var₀_aux]

def substSnd {Δ Γ : CCtx Ctx} {A : Γ.ty} {Aσ : y(Δ.1) ⟶ Ty}
    (σ : Δ.1 ⟶ ext Γ.1 A) (eq : Aσ = yoneda.map (substFst σ) ≫ A) :
    Δ.typed Aσ :=
  sorry

def mkP_equiv {Γ : Ctx} {X : Psh Ctx} :
    (y(Γ) ⟶ (P tp).obj X) ≃ (A : y(Γ) ⟶ Ty) × (y(ext Γ A) ⟶ X) :=
  ((uvPoly tp).equiv' y(Γ) X).trans <|
  Equiv.sigmaCongrRight fun A =>
  ((yoneda.obj X).mapIso (disp_pullback A).isoPullback.op).toEquiv

def mkP {Γ : Ctx} {X : Psh Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext Γ A) ⟶ X) :
    y(Γ) ⟶ (P tp).obj X := mkP_equiv.symm ⟨A, B⟩

def mkPi {Γ : CCtx Ctx} (A : Γ.ty) (B : (Γ.cons A).ty) : Γ.ty :=
  mkP A B ≫ NaturalModelPi.Pi

theorem mkP_app {Γ : Ctx} {X Y : Psh Ctx} (A : y(Γ) ⟶ Ty)
    (F : X ⟶ Y) (B : y(ext Γ A) ⟶ X) :
    mkP A B ≫ (P tp).map F = mkP A (B ≫ F) := by
  sorry -- left naturality of UvPoly.equiv + left naturality of sigmaCongrRight

def mkLam {Γ : CCtx Ctx} (A : Γ.ty) (B : (Γ.cons A).ty) (t : (Γ.cons A).typed B) :
    Γ.typed (mkPi A B) :=
  ⟨mkP A t.1 ≫ NaturalModelPi.lam, by
    simp [mkPi, NaturalModelPi.Pi_pullback.w]
    rw [← Category.assoc, mkP_app, t.2]⟩

/--
```
Γ ⊢ A type  Γ.A ⊢ B type  Γ ⊢ f : ΠA.B
--------------------------------------
Γ.A ⊢ f[↑_A] v₀ : B
``` -/
def mkPApp {Γ : CCtx Ctx} (A : Γ.ty) (B : (Γ.cons A).ty)
    (f : Γ.typed (mkPi A B)) : (Γ.cons A).typed B := by
  let total' : y(Γ.1) ⟶ (P tp).obj Tm :=
    NaturalModelPi.Pi_pullback.isLimit.lift <|
    PullbackCone.mk f.1 (mkP A B) f.2
  have : total' ≫ (P tp).map tp = mkP A B :=
    NaturalModelPi.Pi_pullback.isLimit.fac _ (some .right)
  let total := mkP_equiv.1 total'
  have := mkP_equiv.symm.injective <|
    show mkP total.1 (total.2 ≫ tp) = mkP A B by
      rw [← mkP_app]; simp [mkP, total, this]
  have aeq : total.1 = A := congrArg Sigma.fst this
  refine ⟨aeq ▸ total.2, ?_⟩
  clear_value total'; cases this; rfl

def mkApp {Γ : CCtx Ctx} (A : Γ.ty) (B : (Γ.cons A).ty)
    (f : Γ.typed (mkPi A B)) (a : Γ.typed A) : Γ.typed (Γ.inst A B a) := by
  refine ⟨Γ.inst A (mkPApp A B f).1 a, ?_⟩
  simp [CCtx.inst]
  congr! 1; exact (mkPApp A B f).2

-- semantic beta reduction
@[simp]
theorem mkApp_mkLam {Γ : CCtx Ctx} (A : Γ.ty) (B : (Γ.cons A).ty)
    (t : (Γ.cons A).typed B) (a : Γ.typed A) :
    -- TODO: rethink this; idk if we really want to have `inst`
    -- be a simp-NF; maybe preferrable to use `σ ≫ _`
    mkApp A B (mkLam A B t) a = Γ.inst' A B t a := by
  unfold mkApp mkPApp mkLam
  sorry

def mkEl {Γ : CCtx Ctx} (A : Γ.typed wU) : Γ.ty :=
  yoneda.map (substCons (terminal.from _) _ A.1 A.2) ≫ El

def mkSmallPi {Γ : CCtx Ctx} (A : Γ.typed wU) (B : (Γ.cons (mkEl A)).typed wU) : Γ.typed wU := by
  refine CCtx.substSnd (Γ := .nil)
    (Yoneda.fullyFaithful.preimage (?_ ≫ NaturalModelSmallPi.SmallPi (Ctx := Ctx)))
    (by simp [wU, CCtx.nil]; congr; ext)
  refine ((uvPoly _).equiv' _ _).2 ⟨?_, ?_⟩
  · exact yoneda.map (substCons (terminal.from _) _ A.1 A.2)
  · refine ?_ ≫ yoneda.map (substCons (terminal.from _) _ B.1 B.2)
    dsimp [uvPoly]
    refine (disp_pullback (Ctx := Ctx) _).isLimit.lift <|
      PullbackCone.mk (pullback.fst .. ≫ var _ _) (pullback.snd ..) ?_
    rw [mkEl, Category.assoc, (disp_pullback _).w, ← Category.assoc,
      pullback.condition, Category.assoc]

end CCtx
