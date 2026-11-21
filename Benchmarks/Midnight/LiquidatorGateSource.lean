import Benchmarks.Midnight.LiquidateSourceFrame

/-! Source evaluation of the optional liquidator-gate call and its Boolean guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidatorGateGuard : Expr :=
  .binary .ne (.field (.var "market") "liquidatorGate") (.cast (.intLit 0) (.elem .address))

def liquidatorGateStatement : Stmt := liquidateTransition.body[8]!

def liquidatorGateAllowedFrame (frame : Frame) (word : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "allowed" (wordToElem .bool word) }

theorem evalMarketLiquidatorGate {cfg : Config} {frame : Frame} {evm : State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.field (.var "market") "liquidatorGate") =
      .ok (.address m.liquidatorGate) := by
  simp only [evalExpr?, hm, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem liquidatorGateGuard_eval {frame : Frame} {evm : State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? config frame evm liquidatorGateGuard =
      .ok (.bool (decide (m.liquidatorGate ≠ 0))) := by
  rw [liquidatorGateGuard, evalExpr_binary_nonshort (by decide) (by decide),
    evalMarketLiquidatorGate hm]
  simp only [evalExpr?, castValue?, EvalResult.ofOption, bind, pure, EvalResult.bind]
  change EvalResult.ok (Value.bool (!(Value.address m.liquidatorGate == .address 0))) = _
  simp only [Reasoning.VyperDispatch.value_address_beq, decide_not]

theorem liquidatorGateSkipped {frame : Frame} {evm : State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hz : m.liquidatorGate = 0) :
    ExecStmt config frame evm liquidatorGateStatement (.ok frame evm) := by
  exact ExecStmt.iteFalse ((liquidatorGateGuard_eval hm).trans (by rw [hz]; rfl)) ExecBlock.nil

theorem liquidatorGateFailed {frame : Frame} {evm : State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hn : m.liquidatorGate ≠ 0)
    (hcall : ExecStmt config frame evm
      (.externalCall (.field (.var "market") "liquidatorGate") "canLiquidate" (.intLit 0)
        [.env .caller] "allowed" false) .reverted) :
    ExecStmt config frame evm liquidatorGateStatement .reverted := by
  exact ExecStmt.iteTrue ((liquidatorGateGuard_eval hm).trans (by rw [decide_eq_true hn]))
    (ExecBlock.consRevert hcall)

theorem liquidatorGateDenied {frame : Frame} {evm evm' : State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hn : m.liquidatorGate ≠ 0)
    (hcall : ExecStmt config frame evm
      (.externalCall (.field (.var "market") "liquidatorGate") "canLiquidate" (.intLit 0)
        [.env .caller] "allowed" false) (.ok (liquidatorGateAllowedFrame frame ⟨0⟩) evm')) :
    ExecStmt config frame evm liquidatorGateStatement .reverted := by
  refine ExecStmt.iteTrue ((liquidatorGateGuard_eval hm).trans (by rw [decide_eq_true hn]))
    (ExecBlock.consNormal hcall (ExecBlock.consRevert (ExecStmt.requireFalse ?_)))
  simp only [evalExpr?, liquidatorGateAllowedFrame, store_get_self, EvalResult.ofOption]
  rfl

theorem liquidatorGateAllowed {frame : Frame} {evm evm' : State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hn : m.liquidatorGate ≠ 0)
    (hcall : ExecStmt config frame evm
      (.externalCall (.field (.var "market") "liquidatorGate") "canLiquidate" (.intLit 0)
        [.env .caller] "allowed" false) (.ok (liquidatorGateAllowedFrame frame ⟨1⟩) evm')) :
    ExecStmt config frame evm liquidatorGateStatement
      (.ok (liquidatorGateAllowedFrame frame ⟨1⟩) evm') := by
  refine ExecStmt.iteTrue ((liquidatorGateGuard_eval hm).trans (by rw [decide_eq_true hn]))
    (ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil))
  simp only [evalExpr?, liquidatorGateAllowedFrame, store_get_self, EvalResult.ofOption]
  rfl

end Benchmarks.Midnight
