import Benchmarks.Midnight.WithdrawCollateralSource
import Benchmarks.Midnight.HealthSource

/-! Calling the health predicate and requiring its Boolean result during withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawHealthFrame (frame : Frame) (value : Bool) : Frame :=
  { frame with locals := frame.locals.insert "__c3" (.bool value) }

theorem WithdrawSourceFrame.healthFrame {frame : Frame} {m : MarketData}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver) (value : Bool) :
    WithdrawSourceFrame (withdrawHealthFrame frame value) m id user index assets token receiver :=
  hf.insert "__c3" (.bool value) (by decide)

theorem withdrawHealthRevert {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hbody : ExecFuncBody config (healthCallFrame frame.immutables m id user) evm
      healthFunction.body .reverted) :
    ExecBlock config frame evm (withdrawCollateralTransition.body.drop 11) .reverted := by
  apply ExecBlock.consRevert
  apply internalCallFunctionRevert (callee := healthFunction) (locals := healthArguments m id user)
    (withdrawCollateralHealthArgs hf) (by rw [hf.contract]; rfl) rfl
  simpa only [healthCallFrame, hf.contract] using hbody

theorem withdrawHealthReturn {frame frame' : Frame} {m : MarketData} {evm evm' : EVM.State}
    {id user index assets : UInt256} {token receiver : AccountAddress} {value : Bool}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hbody : ExecFuncBody config (healthCallFrame frame.immutables m id user) evm
      healthFunction.body (.returned frame' evm' (some [.bool value]))) :
    ExecStmt config frame evm (withdrawCollateralTransition.body[11]!)
      (.ok (withdrawHealthFrame frame value) evm') := by
  apply internalCallFunctionReturn (callee := healthFunction) (locals := healthArguments m id user)
    (value := some [.bool value])
    (withdrawCollateralHealthArgs hf) (by rw [hf.contract]; rfl) rfl
  simpa only [healthCallFrame, hf.contract] using hbody

theorem withdrawHealthGuard {frame : Frame} {evm : EVM.State} (value : Bool) :
    evalExpr? config (withdrawHealthFrame frame value) evm (.var "__c3") = .ok (.bool value) := by
  simp only [evalExpr?, withdrawHealthFrame, store_get_self, EvalResult.ofOption]

end Benchmarks.Midnight
