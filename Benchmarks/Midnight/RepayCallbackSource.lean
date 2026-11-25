import Benchmarks.Midnight.RepayPayerSource
import Benchmarks.Midnight.RepayCallbackABI
import Benchmarks.Midnight.FlashLoanCallbackSource

variable {fork : Ethereum.Fork}

/-! Source execution of repayment's optional callback and acknowledgement check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def repayCallbackStmt : Stmt := .externalCall (.var "callback") "onRepay" (.intLit 0)
  [.var "id", .var "market", .var "units", .var "onBehalf", .var "data"] "__c3" true

def repayMagicGuard : Expr :=
  .binary .eq (.var "__c3") (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE flashLoanMagic))

def repayCallbackFrame (frame : Frame) (value : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c3" (wordBytes32Value value) }

theorem repayCallback_shape : repayTransition.body.drop 11 =
    .ite repayCallbackCondition [repayCallbackStmt, .require repayMagicGuard] [] ::
      repayTransition.body.drop 12 := by decide +kernel

theorem repayCallbackFrame_spec {frame : Frame} {m : MarketData} {id user units : UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data) (value : UInt256) :
    RepaySourceFrame (repayCallbackFrame frame value) m id user units callback data :=
  hf.insert "__c3" _ (by decide)

theorem repayCallbackArgs {frame : Frame} {evm : State} {m : MarketData} {id user units : UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data) :
    evalExprs? config frame evm
      [.var "id", .var "market", .var "units", .var "onBehalf", .var "data"] =
      .ok (repayCallbackArguments m id units (AccountAddress.ofNat user.toNat) data) := by
  simp only [evalExprs?, evalExpr?, hf.idValue, hf.market, hf.units, hf.userValue, hf.data,
    EvalResult.ofOption, bind, pure, EvalResult.bind, repayCallbackArguments]

theorem repayMagicGuard_eval (frame : Frame) (evm : State) (value : UInt256) :
    evalExpr? config (repayCallbackFrame frame value) evm repayMagicGuard =
      .ok (.bool (decide (value = flashLoanMagic))) := by
  simp only [repayMagicGuard, evalExpr?, repayCallbackFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true, if_true,
    EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?, wordBytes32Value_beq]

theorem repayCallbackFailure {frame : Frame} {evm evm' : State} {m : MarketData}
    {id user units : UInt256} {callback : AccountAddress} {data out : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hcall : typedCallViaEVM fork config evm callback "onRepay" 0
      (repayCallbackArguments m id units (AccountAddress.ofNat user.toNat) data)
      (false, evm', out) true) :
    ExecStmt fork config frame evm repayCallbackStmt .reverted := by
  exact ExecStmt.externalCallFailure (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (repayCallbackArgs hf)
    (by simpa only [address_of_val] using hcall)

theorem repayCallbackShort {frame : Frame} {evm evm' : State} {m : MarketData}
    {id user units : UInt256} {callback : AccountAddress} {data out : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hcall : typedCallViaEVM fork config evm callback "onRepay" 0
      (repayCallbackArguments m id units (AccountAddress.ofNat user.toNat) data)
      (true, evm', out) true) (hshort : out.size < 32) :
    ExecStmt fork config frame evm repayCallbackStmt .reverted := by
  exact ExecStmt.externalCallReturnDecodeRevert (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (repayCallbackArgs hf)
    (by simpa only [address_of_val] using hcall) (decodeRepayCallback_short hshort)

theorem repayCallbackSuccess {frame : Frame} {evm evm' : State} {m : MarketData}
    {id user units : UInt256} {callback : AccountAddress} {data out : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hcall : typedCallViaEVM fork config evm callback "onRepay" 0
      (repayCallbackArguments m id units (AccountAddress.ofNat user.toNat) data)
      (true, evm', out) true) (h32 : 32 ≤ out.size) :
    ExecStmt fork config frame evm repayCallbackStmt
      (.ok (repayCallbackFrame frame (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (repayCallbackArgs hf)
    (by simpa only [address_of_val] using hcall) (decodeRepayCallback h32)

end Benchmarks.Midnight
