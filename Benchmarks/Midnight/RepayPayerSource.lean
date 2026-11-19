import Benchmarks.Midnight.RepayBalanceSource

/-! Choosing repayment's payer and emitting its event. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def repayPayer (I : ExecutionEnv) (callback : AccountAddress) : AccountAddress :=
  if callback = 0 then I.source else callback

def repayHasCallback (callback : AccountAddress) : UInt256 :=
  if callback = 0 then ⟨0⟩ else ⟨1⟩

def repayPayerFrame (frame : Frame) (I : ExecutionEnv) (callback : AccountAddress) : Frame :=
  { frame with locals := frame.locals.insert "payer" (.address (repayPayer I callback)) }

def repayCallbackCondition : Expr :=
  .binary .ne (.var "callback") (.cast (.intLit 0) (.elem .address))

theorem repayCallbackCondition_eval {frame : Frame} {evm : State} {callback : AccountAddress}
    (hc : frame.locals.get? "callback" = some (.address callback)) :
    evalExpr? config frame evm repayCallbackCondition = .ok (.bool (decide (callback ≠ 0))) := by
  have hcast : castValue? (.int 0) (.elem .address) = some (.address 0) := rfl
  simp only [repayCallbackCondition, evalExpr?, hc, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hcast, evalBinaryOp?]
  by_cases hz : callback = 0 <;> simp [hz]

theorem repayPayerSource {frame : Frame} {m : MarketData} {evm : State}
    {id user units : UInt256} {callback : AccountAddress} {data : ByteArray} {result : ExecResult}
    (hf : RepaySourceFrame frame m id user units callback data)
    (ht : ExecBlock config (repayPayerFrame frame evm.executionEnv callback) evm
      (repayTransition.body.drop 10) result) :
    ExecBlock config frame evm (repayTransition.body.drop 9) result := by
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ht
  rw [evalExpr?]
  change (evalExpr? config frame evm repayCallbackCondition >>= _) = _
  rw [repayCallbackCondition_eval hf.callback]
  by_cases hz : callback = 0
  · simp [hz, EvalResult.bind, bind, evalExpr?, envValue, repayPayer, pure]
  · simp only [decide_eq_true hz, hz, EvalResult.bind, bind, evalExpr?, hf.callback,
      EvalResult.ofOption, repayPayer, if_false]

theorem repayPayerFrame_spec {frame : Frame} {m : MarketData} {id user units : UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data) (I : ExecutionEnv) :
    RepaySourceFrame (repayPayerFrame frame I callback) m id user units callback data :=
  hf.insert "payer" _ (by decide)

theorem repayEmitSource {frame : Frame} {m : MarketData} {evm : State}
    {id user units : UInt256} {callback : AccountAddress} {data : ByteArray} {payer : AccountAddress}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hp : frame.locals.get? "payer" = some (.address payer)) (hperm : evm.executionEnv.perm = true) :
    ABlock config evm frame (repayTransition.body.drop 10) frame (repayTransition.body.drop 11) := by
  refine ⟨fun ht ↦ ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address evm.executionEnv.source, wordBytes32Value id, .int units.toNat,
      .address (AccountAddress.ofNat user.toNat), .address payer]) hperm ?_) ht⟩
  simp only [evalExprs?, evalExpr?, hf.idValue, hf.units, hf.userValue, hp,
    envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
