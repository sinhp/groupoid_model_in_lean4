import GroupoidModel.Russell_PER_MS.NaturalModelBase

-- TODO(WN): reorg this module
universe v u

noncomputable section
open CategoryTheory Limits NaturalModelBase

namespace NaturalModelBase
variable {Ctx : Type u}
  [SmallCategory Ctx] (M : NaturalModelBase Ctx)

structure NaturalModelPi where
  Pi : M.Ptp.obj M.Ty ⟶ M.Ty
  lam : M.Ptp.obj M.Tm ⟶ M.Tm
  Pi_pullback : IsPullback lam (M.Ptp.map M.tp) M.tp Pi

structure NaturalModelSigma where
  Sig : M.Ptp.obj M.Ty ⟶ M.Ty
  pair : UvPoly.compDom (uvPolyTp M) (uvPolyTp M) ⟶ M.Tm
  Sig_pullback : IsPullback pair ((uvPolyTp M).comp (uvPolyTp M)).p M.tp Sig




end NaturalModelBase
end
