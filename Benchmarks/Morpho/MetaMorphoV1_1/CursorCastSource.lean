import Benchmarks.Morpho.MetaMorphoV1_1.Uint128AllocationSource

/-! Continuations for a uint128 cast that returns its value and updated memory cursor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def cursorCastFrame (frame : Frame) (result : Ident) (x ptr : UInt256) : Frame :=
  { frame with
    locals := ((frame.locals.insert slotsAndCursorName
      (.tuple [uint256Value x, uint256Value (nextCursor ptr ⟨64⟩)])).insert result
        (uint256Value x)).insert cursorName (uint256Value (nextCursor ptr ⟨64⟩)) }

theorem cursorCastFrame_cursor (frame : Frame) (result : Ident) (x ptr : UInt256) :
    (cursorCastFrame frame result x ptr).locals.get? cursorName =
      some (uint256Value (nextCursor ptr ⟨64⟩)) :=
  store_get_self _ _ _

theorem cursorCastFrame_value (frame : Frame) (result : Ident) (x ptr : UInt256)
    (hne : (cursorName == result) = false) :
    (cursorCastFrame frame result x ptr).locals.get? result = some (uint256Value x) := by
  rw [cursorCastFrame, store_get_ne _ _ hne, store_get_self]

theorem cursorCastFrame_preserves (frame : Frame) (result name : Ident) (x ptr : UInt256)
    (hc : (cursorName == name) = false) (hr : (result == name) = false)
    (hs : (slotsAndCursorName == name) = false) :
    (cursorCastFrame frame result x ptr).locals.get? name = frame.locals.get? name := by
  rw [cursorCastFrame, store_get_ne _ _ hc, store_get_ne _ _ hr, store_get_ne _ _ hs]

theorem cursorCastSourcePrefix {frame : Frame} {evm : State} {expr : Expr}
    {x ptr : UInt256} (result : Ident) (tail : List Stmt)
    (hcontract : frame.contract = contract) (hname : (result == slotsAndCursorName) = false)
    (hx : evalExpr? config frame evm expr = .ok (uint256Value x))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (halloc : allocationFits ptr ⟨64⟩) (hfit : x.toNat < 2 ^ 128) :
    ABlock config evm frame
      (cursorCall allocatedToUint128Function.name [expr] result ++ tail)
      (cursorCastFrame frame result x ptr) tail := by
  rcases frame with ⟨c, locals, imms⟩
  cases hcontract
  constructor
  intro value htail
  apply ExecBlock.consNormal (allocatedToUint128Call evm locals imms x ptr slotsAndCursorName
    expr (.var cursorName) halloc hfit hx
    (by simp only [evalExpr?, hp, EvalResult.ofOption]))
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
    simp only [evalExpr?, store_get_ne _ _ hname, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind]
    rfl
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind]
    rfl

theorem cursorCastSourceReverts {frame : Frame} {evm : State} {expr : Expr}
    {x ptr : UInt256} (result : Ident) (tail : List Stmt)
    (hcontract : frame.contract = contract)
    (hx : evalExpr? config frame evm expr = .ok (uint256Value x))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hbad : ¬ allocationFits ptr ⟨64⟩ ∨ 2 ^ 128 ≤ x.toNat) :
    ExecBlock config frame evm
      (cursorCall allocatedToUint128Function.name [expr] result ++ tail) .reverted := by
  rcases frame with ⟨c, locals, imms⟩
  cases hcontract
  exact ExecBlock.consRevert (allocatedToUint128CallReverts evm locals imms x ptr
    slotsAndCursorName expr (.var cursorName) hbad hx
    (by simp only [evalExpr?, hp, EvalResult.ofOption]))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
