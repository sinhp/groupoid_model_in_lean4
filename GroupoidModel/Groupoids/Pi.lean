import GroupoidModel.Groupoids.Sigma
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
def pi {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{v₁,u₁})
    : Γ ⥤ Grpd.{v₁,u₁} :=
  sorry

/-- The formation rule for Π-types for the ambient natural model `base` -/
def basePi.Pi : base.Ptp.obj base.{u}.Ty ⟶ base.Ty where
  app Γ := fun pair =>
    let ⟨A,B⟩ := baseUvPolyTpEquiv pair
    yonedaEquiv (yonedaCatEquiv.symm (pi A B))
  naturality := sorry

def basePi : NaturalModelPi base where
  Pi := basePi.Pi
  lam := sorry
  Pi_pullback := sorry

def smallUPi : NaturalModelPi smallU := sorry

def uHomSeqPis' (i : ℕ) (ilen : i < 4) :
  NaturalModelPi (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUPi
  | 1 => smallUPi
  | 2 => smallUPi
  | 3 => basePi
  | (n+4) => by omega

def uHomSeqPis : UHomSeqPiSigma Ctx := { uHomSeq with
  nmPi := uHomSeqPis'
  nmSigma := uHomSeqSigmas' }

end GroupoidModel

end
