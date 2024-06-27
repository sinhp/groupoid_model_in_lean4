import GroupoidModel.NaturalModel

set_option autoImplicit true

namespace Bla

mutual
inductive TyExpr where
  | univ
  | el (A : Expr)
  | pi (ty A : TyExpr)

inductive Expr where
  | bvar (n : Nat)
  | app (f a : Expr)
  | lam (ty : TyExpr) (val : Expr)
  -- | small_pi (ty A : Expr)
end

def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

theorem liftVar_lt (h : i < k) : liftVar n i k = i := if_pos h
theorem liftVar_le (h : k ≤ i) : liftVar n i k = n + i := if_neg (Nat.not_lt.2 h)

theorem liftVar_base : liftVar n i = n + i := liftVar_le (Nat.zero_le _)
@[simp] theorem liftVar_base' : liftVar n i = i + n := Nat.add_comm .. ▸ liftVar_le (Nat.zero_le _)

@[simp] theorem liftVar_zero : liftVar n 0 (k+1) = 0 := by simp [liftVar]
@[simp] theorem liftVar_succ : liftVar n (i+1) (k+1) = liftVar n i k + 1 := by
  simp [liftVar, Nat.succ_lt_succ_iff]; split <;> simp [Nat.add_assoc]

theorem liftVar_lt_add (self : i < k) : liftVar n i j < k + n := by
  simp [liftVar]
  split <;> rename_i h
  · exact Nat.lt_of_lt_of_le self (Nat.le_add_right ..)
  · rw [Nat.add_comm]; exact Nat.add_lt_add_right self _

variable (n : Nat) in
mutual
def TyExpr.liftN : TyExpr → (k :_:= 0) → TyExpr
  | .univ, _ => .univ
  | .el A, k => .el (A.liftN k)
  | .pi ty body, k => .pi (ty.liftN k) (body.liftN (k+1))
def Expr.liftN : Expr → (k :_:= 0) → Expr
  | .bvar i, k => .bvar (liftVar n i k)
  | .app fn arg, k => .app (fn.liftN k) (arg.liftN k)
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k+1))
  -- | .pi ty body, k => .pi (ty.liftN k) (body.liftN (k+1))
end

abbrev TyExpr.lift := TyExpr.liftN 1
abbrev Expr.lift := Expr.liftN 1

mutual
inductive HasType : List TyExpr → Expr → TyExpr → Type
  | var {A Γ} : HasType (A :: Γ) (.bvar 0) A.lift
  | weak {e A Γ} : HasType Γ e A → HasType (A :: Γ) e.lift A.lift
  | lam {A B e Γ} : IsType Γ A → HasType (A :: Γ) e B → HasType Γ (.lam A e) (.pi A B)

inductive IsType : List TyExpr → TyExpr → Type
  | el {A Γ} : HasType Γ A .univ → IsType Γ (.el A)
  | pi {A B Γ} : IsType Γ A → IsType (A :: Γ) B → IsType Γ (.pi A B)
  | univ {Γ} : IsType Γ .univ
end

example : HasType [] (Expr.lam .univ (.bvar 0)) (TyExpr.pi .univ .univ) :=
  .lam .univ .var

universe u v
open CategoryTheory NaturalModel IsPresentable
open Functor Limits Opposite Representable
noncomputable section

theorem psh_naturality {C : Type u₁} [Category C] {F G : C ⥤ Type w}
  (self : NatTrans F G) ⦃X Y : C⦄ (f : X ⟶ Y) (a : F.obj X) :
  self.app Y (F.map f a) = G.map f (self.app X a) := congrFun (self.naturality f) a

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]
variable {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) [NaturalModel tp]

def wU : y(Γ) ⟶ Ty := yoneda.map (terminal.from Γ) ≫ U tp

inductive CtxStack [IsPresentable tp] : Ctx → Type u where
  | nil : CtxStack (⊤_ Ctx)
  | cons {Γ} (A : y(Γ) ⟶ Ty) : CtxStack Γ → CtxStack (ext tp Γ A)

def Context [IsPresentable tp] : Type u := Σ Γ, CtxStack tp Γ
section
variable {tp}

abbrev Context.ty (Γ : Context tp) := y(Γ.1) ⟶ Ty
abbrev Context.tm (Γ : Context tp) := y(Γ.1) ⟶ Tm

def Context.typed (Γ : Context tp) (A : Γ.ty) := { x : Γ.tm // x ≫ tp = A }

def Context.nil : Context tp := ⟨_, .nil⟩

def Context.cons (Γ : Context tp) (A : Γ.ty) : Context tp := ⟨_, .cons A Γ.2⟩

@[simp] theorem Context.cons_fst (Γ : Context tp) (A : Γ.ty) :
    (Γ.cons A).1 = ext tp Γ.1 A := rfl

def Context.weak (Γ : Context tp) (A : Γ.ty)
  {P : Psh Ctx} (f : y(Γ.1) ⟶ P) : y((cons Γ A).1) ⟶ P :=
  yoneda.map (disp Γ.1 A) ≫ f

protected def Context.var (Γ : Context tp) (i : ℕ) : Part Γ.tm :=
  match Γ, i with
  | ⟨_, .nil⟩, _ => .none
  | ⟨_, .cons _ _⟩, 0 => pure <| var ..
  | ⟨_, .cons _ Γ⟩, n+1 => Context.weak ⟨_, Γ⟩ _ <$> Context.var ⟨_, Γ⟩ n

def substCons {Γ Δ : Ctx} (σ : Γ ⟶ Δ)
    (e : y(Γ) ⟶ Tm) (A : y(Δ) ⟶ Ty) (eTy : e ≫ tp = yoneda.map σ ≫ A) :
    Γ ⟶ ext tp Δ A := by
  refine Yoneda.fullyFaithful.1 <| (disp_pullback (tp := tp) A).isLimit.lift <|
    PullbackCone.mk e (yoneda.map σ) ?_
  ext; simp [← eTy, psh_naturality]

def mkEl {Γ : Context tp} (A : Γ.typed (wU tp)) : Γ.ty :=
  yoneda.map (substCons (terminal.from _) A.1 _ (by simpa [wU] using A.2)) ≫ El

def mkP_equiv {Γ : Ctx} {X : Psh Ctx} :
    (y(Γ) ⟶ (P tp).obj X) ≃ (A : y(Γ) ⟶ Ty) × (y(ext tp Γ A) ⟶ X) :=
  ((uvPoly tp).equiv y(Γ) X).trans <|
  Equiv.sigmaCongrRight fun A =>
  ((yoneda.obj X).mapIso (disp_pullback (tp := tp) A).isoPullback.op).toEquiv

def mkP {Γ : Ctx} {X : Psh Ctx} (A : y(Γ) ⟶ Ty) (B : y(ext tp Γ A) ⟶ X) :
    y(Γ) ⟶ (P tp).obj X := mkP_equiv.2 ⟨A, B⟩

theorem mkP_app {Γ : Ctx} {X Y : Psh Ctx} (A : y(Γ) ⟶ Ty)
    (F : X ⟶ Y) (B : y(ext tp Γ A) ⟶ X) :
    mkP A B ≫ (P tp).map F = mkP A (B ≫ F) := by
  sorry

def mkPi {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty) : Γ.ty :=
  mkP A B ≫ NaturalModelPi.Pi

def mkLam' {Γ : Context tp} (A : Γ.ty) (e : (Γ.cons A).tm) : Γ.tm :=
  mkP A e ≫ NaturalModelPi.lam

def Context.subst {Γ : Context tp} {X : Psh Ctx}
    (A : Γ.ty) (B : y((Γ.cons A).1) ⟶ X) (a : Γ.typed A) : y(Γ.1) ⟶ X :=
  yoneda.map (substCons (tp := tp) (𝟙 _) a.1 A (by simpa using a.2)) ≫ B

def mkLam {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty) (e : (Γ.cons A).typed B) :
    Γ.typed (mkPi A B) := by
  refine ⟨mkLam' A e.1, ?_⟩
  simp [mkLam', mkPi, (NaturalModelPi.Pi_pullback (tp := tp)).w]
  rw [← Category.assoc, mkP_app, e.2]

def mkPApp {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty)
    (f : Γ.typed (mkPi A B)) : (Γ.cons A).typed B := by
  let total' : y(Γ.1) ⟶ (P tp).obj Tm :=
    (NaturalModelPi.Pi_pullback (tp := tp)).isLimit.lift <|
    PullbackCone.mk f.1 (mkP A B) f.2
  have : total' ≫ (P tp).map tp = mkP A B := sorry
  let total := mkP_equiv.1 total'
  have := mkP_equiv.symm.injective <|
    show mkP total.1 (total.2 ≫ tp) = mkP A B by
      rw [← mkP_app]; simp [mkP, total, this]
  have aeq : total.1 = A := congrArg Sigma.fst this
  refine ⟨aeq ▸ total.2, ?_⟩
  clear_value total'; cases this; rfl

def mkApp {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty)
    (f : Γ.typed (mkPi A B)) (a : Γ.typed A) : Γ.typed (Γ.subst A B a) := by
  refine ⟨Γ.subst A (mkPApp A B f).1 a, ?_⟩
  simp [Context.subst, psh_naturality]
  congr! 1; exact (mkPApp A B f).2

end


mutual

def ofCtx : List TyExpr → Part (Context tp)
  | [] => pure .nil
  | A :: Γ => do let Γ ← ofCtx Γ; Γ.cons (← ofType Γ A)

def ofType (Γ : Context tp) : TyExpr → Part Γ.ty
  | .univ => pure (wU tp)
  | .pi A B => do
    let A ← ofType Γ A
    let B ← ofType (Γ.cons A) B
    pure (mkPi A B)
  | .el e => do
    let v ← ofTerm Γ e
    Part.assert _ fun h => pure <| mkEl ⟨v, h⟩

def ofTerm (Γ : Context tp) : Expr → Part Γ.tm
  | .bvar i => Context.var _ i
  -- | .univ => .none
  -- | .pi .. => .none -- TODO: small pi
  | .lam A e => do
    let A ← ofType Γ A
    let e ← ofTerm (Γ.cons A) e
    pure (mkLam A _ ⟨e, rfl⟩).1
  | .app f a => do
    let f ← ofTerm Γ f
    let a ← ofTerm Γ a
    Part.assert (∃ B, f ≫ tp = mkPi (a ≫ tp) B) fun h =>
    pure (mkApp _ h.choose ⟨f, h.choose_spec⟩ ⟨a, rfl⟩).1

end
