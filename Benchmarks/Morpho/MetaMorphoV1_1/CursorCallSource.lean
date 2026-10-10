import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! Resume a source caller after a helper returns a value and its memory cursor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def cursorResultFrame (frame : Frame) (result : Ident) (value : Value)
    (cursor : UInt256) : Frame :=
  { frame with
    locals := ((frame.locals.insert slotsAndCursorName
      (.tuple [value, uint256Value cursor])).insert result value).insert cursorName
        (uint256Value cursor) }

theorem cursorResultFrame_cursor (frame : Frame) (result : Ident) (value : Value)
    (cursor : UInt256) :
    (cursorResultFrame frame result value cursor).locals.get? cursorName =
      some (uint256Value cursor) := store_get_self _ _ _

theorem cursorResultFrame_value (frame : Frame) (result : Ident) (value : Value)
    (cursor : UInt256) (hne : (cursorName == result) = false) :
    (cursorResultFrame frame result value cursor).locals.get? result = some value := by
  rw [cursorResultFrame, store_get_ne _ _ hne, store_get_self]

theorem cursorResultFrame_preserves (frame : Frame) (result name : Ident) (value : Value)
    (cursor : UInt256) (hc : (cursorName == name) = false) (hr : (result == name) = false)
    (hs : (slotsAndCursorName == name) = false) :
    (cursorResultFrame frame result value cursor).locals.get? name = frame.locals.get? name := by
  rw [cursorResultFrame, store_get_ne _ _ hc, store_get_ne _ _ hr, store_get_ne _ _ hs]

theorem cursorCallPrefix {frame : Frame} {evm evm' : State} {name result : Ident}
    {args : List Expr} {value : Value} {cursor : UInt256} {tail : List Stmt}
    {outcome : ExecResult} (hne : (result == slotsAndCursorName) = false)
    (hcall : ExecStmt config frame evm
      (.internalCall name (args ++ [.var cursorName]) slotsAndCursorName)
      (.ok (resumeAfterInternalCall frame slotsAndCursorName
        (some [value, uint256Value cursor])) evm'))
    (htail : ExecBlock config (cursorResultFrame frame result value cursor) evm' tail outcome) :
    ExecBlock config frame evm (cursorCall name args result ++ tail) outcome := by
  apply ExecBlock.consNormal hcall
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
    simp only [evalExpr?, resumeAfterInternalCall, collapseReturns,
      store_get_ne _ _ hne, store_get_self, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  · simp only [evalExpr?, resumeAfterInternalCall, collapseReturns,
      store_get_self, EvalResult.ofOption, bind, EvalResult.bind]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
