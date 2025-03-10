import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

end ForOther


-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck

/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors -/
def sigma {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{v₁,u₁})
    : Γ ⥤ Grpd.{v₁,u₁} :=
  sorry

/-- The formation rule for Σ-types for the ambient natural model `base` -/
def baseSigmaSig : base.Ptp.obj base.{u}.Ty ⟶ base.Ty where
  app Γ := fun pair =>
    let ⟨A,B⟩ := baseUvPolyTpEquiv pair
    yonedaEquiv (yonedaCatEquiv.symm (sigma A B))
  naturality := sorry

def baseSigma : NaturalModelSigma base where
  Sig := baseSigmaSig
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
