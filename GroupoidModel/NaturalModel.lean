/-
Natural Models:
see https://arxiv.org/pdf/1406.3219
for the definition of a natural model
and how to model the type formers Σ,Π,Id.
A recent talk is here:
https://awodey.github.io/talks/ATT.pdf
-/

import Mathlib

import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Over

--import Poly
import Poly.LCCC.Basic
import Poly.LCCC.Presheaf
import Poly.Exponentiable
import Poly.Polynomial


universe u v

namespace CategoryTheory

open Functor Limits Opposite Representable

noncomputable section

/-
We will need at least the following:
  - the category Ctx (to be interpreted as small groupoids)
  - the display maps of contexts, arising from iterated context extensions
  - the presheaf category 𝓔 = Psh(Ctx) in which the model lives
  - the presheaf Ty : Ctxᵒᵖ → Set of types in context
  - the presheaf Tm : Ctxᵒᵖ → Set of terms in context
  - the typing natural transformation tp : Tm ⟶ Ty
  - the proof that tp is (re)presentable
  - the polynomial endofunctor Pₜ : 𝓔 ⥤ 𝓔
  - the rules for Π-types as an operation on Pₜ(tp)
  - the rules for Σ-types as an operation on Pₜ(tp)
  - the rules for Id-types as an operation on tp : Tm ⟶ Ty
  - the universe Set of (small) discrete groupoids,
      along with its discrete (op-)fibration Set* ⟶ Set
  It would probably also be useful to have:
  - the proof that presentable natural transformations are "tiny" maps
    (the pushforward has a right adjoint)
  - the proof that Pₜ is therefore cocontinuous, since tp is tiny
  - need to add a general formulation for (groupoid) quotient types
  -/

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure UvPoly' {C : Type*} [Category C] [HasFiniteWidePullbacks C] (E B : C) :=
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)

namespace UvPoly

variable {𝒞} [Category 𝒞] [HasPullbacks 𝒞]

/-- Universal property of the polynomial functor. -/
def _root_.UvPoly.equiv' {E B : 𝒞} (P : UvPoly E B) (Γ X : 𝒞) :
    (Γ ⟶ P.functor.obj X) ≃ Σ b : Γ ⟶ B, pullback P.p b ⟶ X :=
  (UvPoly.equiv P Γ X).trans <|
  Equiv.sigmaCongrRight fun _ =>
  ((yoneda.obj X).mapIso (pullbackSymmetry ..).op).toEquiv


-- def functor : ∀ {E B : 𝒞} (P : UvPoly' E B), 𝒞 ⥤ 𝒞 := sorry

-- def natural {E B E' B' : 𝒞} (P : UvPoly' E B) (P' : UvPoly' E' B')
--     (e : E ⟶ E') (b : B ⟶ B') (pb : IsPullback P.p e b P'.p) : P.functor ⟶ P'.functor := sorry

-- def _root_.UvPoly.star {E F B : 𝒞} (P : UvPoly E B) (Q : UvPoly F B) (g : E ⟶ F) (h : P.p = g ≫ Q.p) :
--     Q.functor ⟶ P.functor := sorry --UvPoly.natural (P := ⟨_, _, Q⟩) (Q := ⟨_, _, P⟩) ⟨by dsimp, by dsimp, _⟩

def _root_.UvPoly.comp {𝒞} [Category 𝒞] [HasFiniteWidePullbacks 𝒞] [HasTerminal 𝒞]
    {E B D C : 𝒞} (P1 : UvPoly E B) (P2 : UvPoly D C) : UvPoly (P2.functor.obj E) (P1.functor.obj C) :=
   let f : E ⟶ B := P1.p
   let g : D ⟶ C := P2.p
   {
     p := sorry
     exp := sorry
   }

end UvPoly

/-!
# Natural Models
-/

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]

notation:max "y(" Γ ")" => yoneda.obj Γ

namespace NaturalModel

variable (Ctx) in
class NaturalModelBase where
  Tm : Psh Ctx
  Ty : Psh Ctx
  tp : Tm ⟶ Ty
  ext (Γ : Ctx) (A : y(Γ) ⟶ Ty) : Ctx
  disp (Γ : Ctx) (A : y(Γ) ⟶ Ty) : ext Γ A ⟶ Γ
  var (Γ : Ctx) (A : y(Γ) ⟶ Ty) : y(ext Γ A) ⟶ Tm
  disp_pullback {Γ : Ctx} (A : y(Γ) ⟶ Ty) :
    IsPullback (var Γ A) (yoneda.map (disp Γ A)) tp A

export NaturalModelBase (Tm Ty tp ext disp var disp_pullback)
variable [M : NaturalModelBase Ctx]

instance : HasFiniteWidePullbacks (Psh Ctx) := hasFiniteWidePullbacks_of_hasFiniteLimits _

instance : LCC (Psh Ctx) := @LCCC.mkOfOverCC _ _ _ ⟨CategoryOfElements.presheafOverCCC⟩

instance {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : CartesianExponentiable tp where
  functor := LCC.pushforward tp
  adj := LCC.adj _

def uvPoly {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : UvPoly Tm Ty := ⟨tp, inferInstance⟩
def uvPolyT {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : UvPoly.Total (Psh Ctx) := ⟨_, _, uvPoly tp⟩

def P {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : Psh Ctx ⥤ Psh Ctx := (uvPoly tp).functor

def P_naturality {E B E' B' : Psh Ctx}
    {f : E ⟶ B} {f' : E' ⟶ B'} (α : uvPolyT f ⟶ uvPolyT f') : P f ⟶ P f' :=
  UvPoly.naturality (P := uvPolyT f) (Q := uvPolyT f') α

def proj {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) : (P tp).obj Ty ⟶ Ty := (uvPoly tp).proj _

-- def PolyTwoCellBack {Tm Ty : Psh Ctx} (tp : Tm ⟶ Ty) := sorry

-- def NaturalitySquare { F G : Psh Ctx } { α : F ⥤ G } { h : C → D } { C D : Ctx }
--   : α_D ∘ (F h) = (G h) ∘ α_C := sorry

-- def UniformWeakPullback (f : A → B) (g : C → D) (c : A → C) (d : B → D)
--   : d ∘ f = g ∘ c and (f, c) : A → B ×_D C has a section j : B ×_D C → A with
--   (f, c) ∘ j = id.

-- def WeakElimRule {Tm Ty I : Psh Ctx} (tp : Tm ⟶ Ty)(q : I ⟶ Ty)(δ : Tm ⟶ I)
--   : UniformWeakPullback NaturalitySquare ...

-- def DeltaOver {C : Type*} [ category C ] ( f : A → B ) := ⟨𝟙 A, 𝟙 A⟩ : A → A ×_B A as an arrow in C/B .

variable (Ctx) in
class NaturalModelPi where
  Pi : (P tp).obj Ty ⟶ M.Ty
  lam : (P tp).obj Tm ⟶ M.Tm
  Pi_pullback : IsPullback lam ((P tp).map tp) tp Pi

variable (Ctx) in
class NaturalModelSigma where
  Sig : (P tp).obj Ty ⟶ M.Ty
  pair : (P tp).obj Tm ⟶ M.Tm
  Sig_pullback : IsPullback pair ((uvPoly tp).comp (uvPoly tp)).p tp Sig

def δ : M.Tm ⟶ pullback tp tp := pullback.lift (𝟙 _) (𝟙 _) rfl
variable (Ctx) in
class NaturalModelEq where
  Eq : pullback tp tp ⟶ M.Ty
  refl : Tm ⟶ M.Tm
  Eq_pullback : IsPullback refl δ tp Eq

variable (Ctx) in
class NaturalModelIdBase where
  Id : pullback tp tp ⟶ M.Ty
  i : Tm ⟶ M.Tm
  Id_commute : δ ≫ Id = i ≫ tp

section
variable [NaturalModelIdBase Ctx]
open NaturalModelIdBase

def I : Psh Ctx := pullback Id tp
def q : I ⟶ M.Ty := pullback.fst ≫ pullback.fst ≫ tp
def ρ : M.Tm ⟶ I := pullback.lift δ i Id_commute

def ρs : P q ⟶ P M.tp :=
  UvPoly.star (P := uvPoly tp) (Q := uvPoly q) ρ (by simp [ρ, uvPoly, q, δ])

def pb2 : Psh Ctx := pullback (ρs.app Ty) ((P tp).map tp)
def ε : (P q).obj M.Tm ⟶ pb2 :=
  pullback.lift ((P q).map tp) (ρs.app Tm) (by aesop_cat)

-- FIXME: NaturalModelId doesn't compile without this being opaque
variable (Ctx) in
irreducible_def NaturalModelIdData :=
  { J : pb2 ⟶ (P q).obj M.Tm // J ≫ ε = 𝟙 _ }
end

variable (Ctx) in
class NaturalModelId extends NaturalModelIdBase Ctx where
  data : NaturalModelIdData Ctx

def NaturalModelId.J [NaturalModelId Ctx] :
    pb2 ⟶ (P q).obj M.Tm := by
  have := NaturalModelId.data (Ctx := Ctx)
  rw [NaturalModelIdData] at this
  exact this.1

theorem NaturalModelId.J_section [NaturalModelId Ctx] : J (Ctx := Ctx) ≫ ε = 𝟙 _ := by
  dsimp [J]
  generalize cast .. = x
  exact x.2

variable (Ctx) in
class NaturalModelU where
  U : y(⊤_ Ctx) ⟶ Ty
  El : y(ext (⊤_ Ctx) U) ⟶ Ty
  -- El_mono : Mono El
export NaturalModelU (U El)

open NaturalModelU in
def toPiArgs [NaturalModelU Ctx] [NaturalModelPi Ctx] :
    (P (yoneda.map (disp (ext (⊤_ Ctx) U) El))).obj y(ext (⊤_ Ctx) U) ⟶ (P tp).obj Ty :=
  (P _).map El ≫ (P_naturality ⟨_, _, (disp_pullback El).flip⟩).app _

open NaturalModelU NaturalModelPi in
variable (Ctx) in
class NaturalModelSmallPi [NaturalModelU Ctx] [NaturalModelPi Ctx] where
  SmallPi : (P (yoneda.map (disp (ext (⊤_ Ctx) U) El))).obj y(ext (⊤_ Ctx) U) ⟶ y(ext (⊤_ Ctx) U)
  SmallPi_eq : SmallPi ≫ El = toPiArgs ≫ Pi

section NaturalModelSmallPi

def NaturalModelSmallPi.lambda [NaturalModelU Ctx] [NaturalModelPi Ctx] :
    (P (yoneda.map (disp (ext (⊤_ Ctx) U) El))).obj Tm ⟶ Tm :=
  sorry

theorem NaturalModelSmallPi.pullback [NaturalModelU Ctx] [NaturalModelPi Ctx] :
    IsPullback lambda
      ((P (yoneda.map (disp (ext (⊤_ Ctx) U) El))).map tp) tp
      ((P_naturality ⟨_, _, (disp_pullback El).flip⟩).app _ ≫ NaturalModelPi.Pi) := sorry

end NaturalModelSmallPi


/-
we will also want to say that the universe U is closed under Sigma, Pi, and Id,
so that we can say that U is univalent.
-/
/-
it would probably also be useful to have another universe U1 with U : U1,
and maybe some type formers for U1 as well .
-/

end NaturalModel

open NaturalModel in
variable (Ctx) in
class NaturalModel extends
  NaturalModelBase Ctx, NaturalModelPi Ctx, NaturalModelSigma Ctx,
  NaturalModelId Ctx, NaturalModelU Ctx, NaturalModelSmallPi Ctx
