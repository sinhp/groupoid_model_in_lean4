import Mathlib.CategoryTheory.Yoneda

/-! Notation for the Yoneda embedding. -/

namespace CategoryTheory

notation:max "y(" Γ ")" => yoneda.obj Γ
notation:max "ym(" f ")" => yoneda.map f

open Lean PrettyPrinter in
@[app_unexpander Functor.obj]
def Functor.obj.unexpand : Unexpander
  | `($_ $F $X) =>
    if let .ident _ _ `yoneda _ := F.raw then
      `(y($X))
    else
      throw ()
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander Functor.map]
def Functor.map.unexpand : Unexpander
  | `($_ $F $X) =>
    if let .ident _ _ `yoneda _ := F.raw then
      `(ym($X))
    else
      throw ()
  | _ => throw ()

end CategoryTheory
