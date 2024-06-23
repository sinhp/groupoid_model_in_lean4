import GroupoidModel.NaturalModel

set_option autoImplicit true

namespace Bla

inductive Expr where
  | bvar (n : Nat)
  | univ
  | app (f a : Expr)
  | lam (ty val : Expr)
  | pi (ty A : Expr)

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
def Expr.liftN : Expr → (k :_:= 0) → Expr
  | bvar i, k => bvar (liftVar n i k)
  | .univ, _ => .univ
  | .app fn arg, k => .app (fn.liftN k) (arg.liftN k)
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k+1))
  | .pi ty body, k => .pi (ty.liftN k) (body.liftN (k+1))

abbrev Expr.lift := Expr.liftN 1

mutual
inductive HasType : List Expr → Expr → Expr → Type
  | var {A Γ} : HasType (A :: Γ) (.bvar 0) A.lift
  | weak {e A Γ} : HasType Γ e A → HasType (A :: Γ) e.lift A.lift
  | lam {A B e Γ} : IsType Γ A → HasType (A :: Γ) e B → HasType Γ (.lam A e) (.pi A B)

inductive IsType : List Expr → Expr → Type
  | small {A Γ} : HasType Γ A .univ → IsType Γ A
  | pi {A B Γ} : IsType Γ A → IsType (A :: Γ) B → IsType Γ (.pi A B)
  | univ {Γ} : IsType Γ .univ
end

example : HasType [] (Expr.lam .univ (.bvar 0)) (Expr.pi .univ .univ) :=
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

def wU : Ty.obj (op Γ) := Ty.map (terminal.from Γ).op (U tp)

inductive CtxStack [IsPresentable tp] : Ctx → Type u where
  | nil : CtxStack (⊤_ Ctx)
  | cons {Γ} (A : Ty.obj (op Γ)) : CtxStack Γ → CtxStack (ext tp Γ A)

def Context [IsPresentable tp] : Type u := Σ Γ, CtxStack tp Γ
section
variable {tp}

abbrev Context.ty (Γ : Context tp) := Ty.obj (op Γ.1)
abbrev Context.tm (Γ : Context tp) := Tm.obj (op Γ.1)

def Context.typeOf {Γ : Context tp} (e : Γ.tm) : Γ.ty := tp.app (op Γ.1) e

def Context.typed (Γ : Context tp) (A : Γ.ty) := { x : Γ.tm // Γ.typeOf x = A }

def Context.nil : Context tp := ⟨_, .nil⟩

def Context.cons (Γ : Context tp) (A : Γ.ty) : Context tp := ⟨_, .cons A Γ.2⟩

@[simp] theorem Context.cons_fst (Γ : Context tp) (A : Γ.ty) :
    (Γ.cons A).1 = ext tp Γ.1 A := rfl

def Context.weak (Γ : Context tp) (A : Γ.ty)
  {P : Psh Ctx} : P.obj (op Γ.1) → P.obj (op (cons Γ A).1) :=
  P.map (X := op Γ.1) (op (disp Γ.1 A))

protected def Context.var (Γ : Context tp) (i : ℕ) : Part Γ.tm :=
  match Γ, i with
  | ⟨_, .nil⟩, _ => .none
  | ⟨_, .cons _ _⟩, 0 => pure <| var ..
  | ⟨_, .cons _ Γ⟩, n+1 => Context.weak ⟨_, Γ⟩ _ <$> Context.var ⟨_, Γ⟩ n

def substCons {Γ Δ : Ctx} (σ : Γ ⟶ Δ)
    (e : Tm.obj (op Γ)) (A : Ty.obj (op Δ)) (eTy : tp.app (op Γ) e = Ty.map σ.op A) :
    Γ ⟶ ext tp Δ A := by
  refine Yoneda.fullyFaithful.1 <| (disp_pullback (tp := tp) A).isLimit.lift <|
    PullbackCone.mk (yonedaEquiv.2 e) (yoneda.map σ) ?_
  ext; simp [← eTy, psh_naturality]

def mkEl {Γ : Context tp} (A : Γ.typed (wU tp)) : Γ.ty :=
  (El (tp := tp)).app _ <| substCons (terminal.from _) A.1 _ (by simpa [wU] using A.2)

def mkP_equiv {Γ : Ctx} {X : Psh Ctx} :
    ((P tp).obj X).obj (op Γ) ≃ (A : Ty.obj (op Γ)) × X.obj (op (ext tp Γ A)) :=
  yonedaEquiv.symm.trans <| ((uvPoly tp).equiv (yoneda.obj Γ) X).trans <|
  (Equiv.sigmaCongrLeft yonedaEquiv.symm).symm.trans <|
  Equiv.sigmaCongrRight fun A =>
    (yoneda.obj X).mapIso (disp_pullback (tp := tp) A).isoPullback.op.symm
      |>.toEquiv.symm.trans yonedaEquiv

def mkP {Γ : Ctx} {X : Psh Ctx} (A : Ty.obj (op Γ)) (B : X.obj (op (ext tp Γ A))) :
    ((P tp).obj X).obj (op Γ) := mkP_equiv.2 ⟨A, B⟩

theorem mkP_app {Γ : Ctx} {X Y : Psh Ctx} (A : Ty.obj (op Γ))
    (F : X ⟶ Y) (B : X.obj (op (ext tp Γ A))) :
    ((P tp).map F).app (op Γ) (mkP A B) = mkP A (F.app _ B) := by
  sorry

def mkPi {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty) : Γ.ty :=
  NaturalModelPi.Pi.app _ (mkP A B)

def mkLam' {Γ : Context tp} (A : Γ.ty) (e : (Γ.cons A).tm) : Γ.tm :=
  NaturalModelPi.lam.app _ (mkP A e)

def Context.subst {Γ : Context tp} {X : Psh Ctx}
    (A : Γ.ty) (B : X.obj (op (Γ.cons A).1)) (a : Γ.typed A) : X.obj (op Γ.1) :=
  X.map (substCons (tp := tp) (𝟙 _) a.1 A (by simpa using a.2)).op B

def mkLam {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty) (e : (Γ.cons A).typed B) :
    Γ.typed (mkPi A B) := by
  refine ⟨mkLam' A e.1, ?_⟩
  simp [Context.typeOf, mkLam', mkPi]
  have := congrArg (·.app (op Γ.1) (mkP A e.1)) (NaturalModelPi.Pi_pullback (tp := tp)).w
  simp at this; rw [this, mkP_app]; congr! 2; exact e.2

def mkPApp {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty)
    (f : Γ.typed (mkPi A B)) : (Γ.cons A).typed B := by
  let total' := yonedaEquiv.1 <|
    (NaturalModelPi.Pi_pullback (tp := tp)).isLimit.lift <|
    PullbackCone.mk (yonedaEquiv.symm f.1) (yonedaEquiv.symm (mkP A B)) <|
      yonedaEquiv.injective (by simpa [yonedaEquiv_apply] using f.2)
  have : ((P tp).map tp).app { unop := Γ.fst } total' = mkP A B := sorry
  let total := mkP_equiv.1 total'
  have := mkP_equiv.symm.injective <|
    show mkP total.fst (tp.app (op (ext tp Γ.fst total.fst)) total.snd) = mkP A B by
      rw [← mkP_app]; simp [mkP, total, this]
  have aeq : total.1 = A := congrArg Sigma.fst this
  refine ⟨aeq ▸ total.2, ?_⟩
  clear_value total'; cases this; rfl

def mkApp {Γ : Context tp} (A : Γ.ty) (B : (Γ.cons A).ty)
    (f : Γ.typed (mkPi A B)) (a : Γ.typed A) : Γ.typed (Γ.subst A B a) := by
  refine ⟨Γ.subst A (mkPApp A B f).1 a, ?_⟩
  simp [Context.typeOf, Context.subst, psh_naturality]
  congr! 1; exact (mkPApp A B f).2

end


mutual

def ofCtx : List Expr → Part (Context tp)
  | [] => pure .nil
  | A :: Γ => do let Γ ← ofCtx Γ; Γ.cons (← ofType Γ A)

def ofType (Γ : Context tp) : Expr → Part Γ.ty
  | .univ => pure (wU tp)
  | .pi A B => do
    let A ← ofType Γ A
    let B ← ofType (Γ.cons A) B
    pure (mkPi A B)
  | e => do
    let v ← ofTerm Γ e
    Part.assert _ fun h => pure <| mkEl ⟨v, h⟩

def ofTerm (Γ : Context tp) : Expr → Part Γ.tm
  | .bvar i => Context.var _ i
  | .univ => .none
  | .pi .. => .none -- TODO: small pi
  | .lam A e => do
    let A ← ofType Γ A
    let e ← ofTerm (Γ.cons A) e
    pure (mkLam A _ ⟨e, rfl⟩).1
  | .app f a => do
    let f ← ofTerm Γ f
    let a ← ofTerm Γ a
    Part.assert (∃ B, Γ.typeOf f = mkPi (Γ.typeOf a) B) fun h =>
    pure (mkApp _ h.choose ⟨f, h.choose_spec⟩ ⟨a, rfl⟩).1

end
