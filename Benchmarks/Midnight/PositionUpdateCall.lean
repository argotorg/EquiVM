import Benchmarks.Midnight.PositionUpdateSource

/-! Internal position-update calls from arbitrary caller frames and argument expressions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem positionUpdateCallFrame {frame : Frame} (m : MarketData) (id user : UInt256)
    (hc : frame.contract = contract) :
    { frame with locals := positionViewArguments m id user } =
      positionViewCallFrame frame.immutables m id user := by
  cases frame
  dsimp only at hc
  cases hc
  rfl

theorem callPositionUpdate {frame callee : Frame} {evm evm' : State} {m : MarketData}
    {id user : UInt256} {args : List Expr} {name : Ident} {values : Option (List Value)}
    (hc : frame.contract = contract)
    (he : evalExprs? config frame evm args =
      .ok [Model.marketValue m.value, wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)])
    (hx : ExecFuncBody config (positionViewCallFrame frame.immutables m id user) evm
      positionUpdateFunction.body (.returned callee evm' values)) :
    ExecStmt config frame evm (.internalCall "_updatePosition" args name)
      (.ok (resumeAfterInternalCall frame name values) evm') := by
  apply internalCallFunctionReturn (callee := positionUpdateFunction)
    (locals := positionViewArguments m id user) he
  · rw [hc]; rfl
  · rfl
  · rwa [positionUpdateCallFrame m id user hc]

theorem callPositionUpdateRevert {frame : Frame} {evm : State} {m : MarketData}
    {id user : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? config frame evm args =
      .ok [Model.marketValue m.value, wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)])
    (hx : ExecFuncBody config (positionViewCallFrame frame.immutables m id user) evm
      positionUpdateFunction.body .reverted) :
    ExecStmt config frame evm (.internalCall "_updatePosition" args name) .reverted := by
  apply internalCallFunctionRevert (callee := positionUpdateFunction)
    (locals := positionViewArguments m id user) he
  · rw [hc]; rfl
  · rfl
  · rwa [positionUpdateCallFrame m id user hc]

theorem callPositionUpdateStatic {frame : Frame} {evm : State} {m : MarketData}
    {id user : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? config frame evm args =
      .ok [Model.marketValue m.value, wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)])
    (hx : ExecFuncBody config (positionViewCallFrame frame.immutables m id user) evm
      positionUpdateFunction.body .staticViolation) :
    ExecStmt config frame evm (.internalCall "_updatePosition" args name) .staticViolation := by
  apply ExecStmt.internalCallStatic (callee := positionUpdateFunction.toCallable)
    (locals := positionViewArguments m id user) he
  · rw [hc]; rfl
  · rfl
  · change ExecFuncBody config { frame with locals := positionViewArguments m id user } evm
      positionUpdateFunction.body .staticViolation
    rwa [positionUpdateCallFrame m id user hc]

end Benchmarks.Midnight
