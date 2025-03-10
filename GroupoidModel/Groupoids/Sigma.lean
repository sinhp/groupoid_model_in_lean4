import GroupoidModel.Groupoids.NaturalModelBase
import GroupoidModel.Russell_PER_MS.NaturalModelSigma

universe v u v₁ u₁ v₂ u₂

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck

/-- The polynomial functor on `tp` taken at `yonedaCat.obj C`
  `P_tp(yonedaCat C)` takes a groupoid `Γ`
  to a pair of functors `A` and `B`

      B
   C ⇇ Groupoidal A   ⥤   PGrpd
            ⇊               ⇊
            Γ          ⥤   Grpd
                       A
As a special case, if `C` is taken to be `Grpd`,
then this is how `P_tp(Ty)` classifies dependent pairs.
-/
def baseUvPolyTpEquiv {Γ : Ctx.{u}} {C : Cat.{u,u+1}} :
    (base.Ptp.obj (yonedaCat.obj C)).obj (op Γ)
    ≃ (A : Ctx.toGrpd.obj Γ ⥤ Grpd.{u,u}) × (Groupoidal A ⥤ C) :=
  yonedaEquiv.symm.trans (
  (uvPolyTpEquiv _ _ _).trans (
  Equiv.sigmaCongr
    yonedaCatEquiv
    (fun _ => yonedaCatEquiv)))

end GroupoidModel

end ForOther


-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory NaturalModelBase Opposite Grothendieck

def sigma {Γ : Grpd.{v,u}} (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : Groupoidal A ⥤ Grpd.{v₁,u₁})
    : Γ ⥤ Grpd.{v₁,u₁} :=
  sorry

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
