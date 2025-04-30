import Mathlib.CategoryTheory.Yoneda

/-! Notation for the Yoneda embedding. -/

namespace CategoryTheory

notation:max "y(" Γ ")" => yoneda.obj Γ
notation:max "ym(" f ")" => yoneda.map f

open Lean PrettyPrinter in
@[app_unexpander Prefunctor.obj]
def Prefunctor.obj.unexpand : Unexpander
  | `($_ $F $X) =>
    if let .node _ _ #[.ident _ _ `yoneda _, _, .ident _ _ `toPrefunctor _] := F.raw then
      `(y($X))
    else
      throw ()
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander Prefunctor.map]
def Prefunctor.map.unexpand : Unexpander
  | `($_ $F $X) =>
    if let .node _ _ #[.ident _ _ `yoneda _, _, .ident _ _ `toPrefunctor _] := F.raw then
      `(ym($X))
    else
      throw ()
  | _ => throw ()

end CategoryTheory
