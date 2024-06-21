import GroupoidModel.NaturalModel

namespace Bla

inductive Expr where
  | var (n : Nat)
  | univ
  | lam (ty : Expr) (val : Expr)
  | pi (ty : Expr) (val : Expr)

#check Expr.lam .univ (.var 0)

def lift : Expr → Expr
  | .var n => .var (n+1)
  | x => x

mutual
inductive HasType : List Expr → Expr → Expr → Type
  | var {A Γ} : HasType (A :: Γ) (.var 0) (lift A)
  | weak {e A Γ} : HasType Γ e A → HasType (A :: Γ) (lift e) (lift A)
  | lam {A B e Γ} : IsType Γ A → HasType (A :: Γ) e B → HasType Γ (.lam A e) (.pi A B)

inductive IsType : List Expr → Expr → Type
  | small {A Γ} : HasType Γ A .univ → IsType Γ A
  | univ {Γ} : IsType Γ .univ
end

example : HasType [] (Expr.lam .univ (.var 0)) (Expr.pi .univ .univ) :=
  .lam .univ .var

universe u v
open CategoryTheory NaturalModel
open Functor Limits Opposite Representable
noncomputable section

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]
variable {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) [NaturalModel tp]

mutual

def ofCtx : List Expr → Ctx
  | [] => ⊤_ Ctx
  | A :: Γ => IsPresentable.ext tp (ofCtx Γ) (ofType (ofCtx Γ) A)

def ofType : ∀ Γ, Expr → Ty.obj (op Γ) := sorry

end
