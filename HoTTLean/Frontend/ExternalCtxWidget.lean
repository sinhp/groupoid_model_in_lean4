import Qq
import HoTTLean.Frontend.Macros
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.Panel.Basic

namespace SynthLean

open Qq
open Lean Server Meta
open ProofWidgets Jsx

@[server_rpc_method]
def ExternalCtxWidget.rpc (p : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let some g := p.termGoal? | return .text ""
    g.ctx.val.runMetaM {} do
      let some elabData := elabExt.getState (← getEnv) | return .text ""
      withLCtx elabData.lctx elabData.linsts do
        let g ← mkFreshExprMVar (some q(SynthLean.Expr $elabData.χ))
        let ctx := { env := ← getEnv, mctx := ← getMCtx, lctx := ← getLCtx, opts := ← getOptions }
        let msg := .withContext ctx <| .ofGoal g.mvarId!
        return <details «open»={true}>
          <summary>External expected type</summary>
          <InteractiveMessage msg={← WithRpcRef.mk msg} />
        </details>

@[widget_module]
def ExternalCtxWidget : Component PanelWidgetProps :=
  mk_rpc_widget% ExternalCtxWidget.rpc

show_panel_widgets [ExternalCtxWidget]

end SynthLean
