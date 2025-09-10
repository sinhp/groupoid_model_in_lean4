import Lean

namespace TypecheckerM
open Lean

structure Caches where
  checkTp : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq) Expr := {}
  checkTm : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq × ExprStructEq) Expr := {}
  synthTm : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  equateTp : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq × ExprStructEq) Expr := {}
  equateTm : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq × ExprStructEq × ExprStructEq) Expr := {}
  equateNeutTm : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq) Expr := {}
  evalTp : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalTm : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalValTp : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalValTm : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalNeutTm : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalClosTp : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  forceClosTp : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalClos₂Tp : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  forceClos₂Tp : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalClosTm : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  forceClosTm : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalEl : Std.HashMap (ExprStructEq) (Expr × Expr) := {}
  evalApp : Std.HashMap (ExprStructEq × ExprStructEq) (Expr × Expr) := {}
  evalFst : Std.HashMap (ExprStructEq) (Expr × Expr) := {}
  evalSnd : Std.HashMap (ExprStructEq) (Expr × Expr) := {}
  evalIdRec : Std.HashMap (ExprStructEq × ExprStructEq × ExprStructEq × ExprStructEq) (Expr × Expr) := {}

inductive TypecheckerM.CacheEntry
  | checkTp (vΓ l T : ExprStructEq)
  | checkTm (vΓ l T t : ExprStructEq)
  | synthTm (vΓ l t : ExprStructEq)
  deriving BEq, Hashable

end TypecheckerM

abbrev TypecheckerM := StateRefT TypecheckerM.Caches Lean.MetaM

def eventually {α : Type} {m : Type → Type} [Monad m] (f : α → m Unit) (x : m α) : m α := do
  let a ← x
  f a
  return a

def TypecheckerM.run {α : Type} (x : TypecheckerM α) : Lean.MetaM α :=
  x.run' {}
