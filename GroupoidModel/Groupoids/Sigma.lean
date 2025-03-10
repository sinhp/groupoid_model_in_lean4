import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther
namespace CategoryTheory.Yoneda

variable {C : Type u₁} [Category.{v₁} C]

open Opposite

/-- Construct a natural transformation between
  two presheaves via yoneda
-/
def natTrans (X Y : Cᵒᵖ ⥤ Type v₁)
    (p : ∀ {Z : C}, (yoneda.obj Z ⟶ X) → (yoneda.obj Z ⟶ Y))
    (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : yoneda.obj Z ⟶ X),
      p (yoneda.map f ≫ g) = yoneda.map f ≫ p g)
    : X ⟶ Y where
  app Z := yonedaEquiv ∘ p ∘ yonedaEquiv.symm
  naturality := sorry

end CategoryTheory.Yoneda
end ForOther


-- NOTE content for this doc starts here
namespace GroupoidModel

open NaturalModelBase Opposite

def baseSig : base.Ptp.obj base.Ty ⟶ base.Ty := sorry
  -- by apply?
-- where
  -- app Γ := have h := (uvPolyTpEquiv base (unop Γ) base.Ty)
  --   fun pair => sorry

def baseSigma : NaturalModelSigma base where
  Sig := sorry
  pair := sorry
  Sig_pullback := sorry

def smallUSigma : NaturalModelSigma smallU := sorry

def uHomSeqSigmas' (i : ℕ) (ilen : i < 4) :
  NaturalModelSigma (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUSigma
  | 1 => smallUSigma
  | 2 => smallUSigma
  | 3 => baseSigma
  | (n+4) => by omega

def uHomSeqSigmas : UHomSeqSigmas Ctx := {
  uHomSeq with
  Sigmas' := uHomSeqSigmas' }

end GroupoidModel

end
