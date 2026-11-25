import Benchmarks.Midnight.LiquidatePayer
import Benchmarks.Midnight.LiquidateCallbackABI
import Benchmarks.Midnight.FlashLoanCallbackSource

variable {fork : Ethereum.Fork}

/-! Source execution of liquidation's optional callback and acknowledgement check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateCallbackExprs : List Expr :=
  [.env .caller, .var "id", .var "market", .var "collateralIndex", .var "seizedAssets",
    .var "repaidUnits", .var "borrower", .var "receiver", .var "data", .var "badDebt"]

def liquidateCallbackStmt : Stmt := .externalCall (.var "callback") "onLiquidate" (.intLit 0)
  liquidateCallbackExprs "__c32" true

def liquidateMagicGuard : Expr :=
  .binary .eq (.var "__c32") (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE flashLoanMagic))

def liquidateCallbackFrame (frame : Frame) (value : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c32" (wordBytes32Value value) }

theorem liquidateCallback_shape : liquidateTransition.body[22]! =
    .ite repayCallbackCondition [liquidateCallbackStmt, .require liquidateMagicGuard] [] :=
  by decide +kernel

theorem liquidateCallbackFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (value : UInt256) :
    LiquidateSourceFrame (liquidateCallbackFrame frame value) m id index seized repaid borrower
      mode receiver callback data := hf.insert "__c32" _ (by decide)

theorem liquidateCallbackFrame_get (frame : Frame) (value : UInt256) (name : Ident)
    (hn : name ≠ "__c32") :
    (liquidateCallbackFrame frame value).locals.get? name = frame.locals.get? name := by
  exact store_get_ne _ _ (by simp [Ne.symm hn])

theorem liquidateCallbackArgs {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode badDebt : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hb : frame.locals.get? "badDebt" = some (.int badDebt.toNat)) :
    evalExprs? config frame evm liquidateCallbackExprs = .ok
      (liquidateCallbackArguments evm.executionEnv.source m id index seized repaid
        (AccountAddress.ofNat borrower.toNat) receiver data badDebt) := by
  simp only [liquidateCallbackExprs, evalExprs?, evalExpr?, hf.idValue, hf.market, hf.index,
    hf.seized, hf.repaid, hf.borrowerValue, hf.receiver, hf.data, hb,
    envValue, EvalResult.ofOption, bind, pure, EvalResult.bind, liquidateCallbackArguments]

theorem liquidateMagicGuard_eval (frame : Frame) (evm : State) (value : UInt256) :
    evalExpr? config (liquidateCallbackFrame frame value) evm liquidateMagicGuard =
      .ok (.bool (decide (value = flashLoanMagic))) := by
  simp only [liquidateMagicGuard, evalExpr?, liquidateCallbackFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true, if_true,
    EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?, wordBytes32Value_beq]

theorem liquidateCallbackFailure {frame : Frame} {evm evm' : State} {m : MarketData}
    {id index seized repaid borrower mode badDebt : UInt256} {receiver callback : AccountAddress}
    {data out : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hb : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hcall : typedCallViaEVM fork config evm callback "onLiquidate" 0
      (liquidateCallbackArguments evm.executionEnv.source m id index seized repaid
        (AccountAddress.ofNat borrower.toNat) receiver data badDebt) (false, evm', out) true) :
    ExecStmt fork config frame evm liquidateCallbackStmt .reverted := by
  exact ExecStmt.externalCallFailure (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (liquidateCallbackArgs hf hb)
    (by simpa only [address_of_val] using hcall)

theorem liquidateCallbackShort {frame : Frame} {evm evm' : State} {m : MarketData}
    {id index seized repaid borrower mode badDebt : UInt256} {receiver callback : AccountAddress}
    {data out : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hb : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hcall : typedCallViaEVM fork config evm callback "onLiquidate" 0
      (liquidateCallbackArguments evm.executionEnv.source m id index seized repaid
        (AccountAddress.ofNat borrower.toNat) receiver data badDebt) (true, evm', out) true)
    (hshort : out.size < 32) :
    ExecStmt fork config frame evm liquidateCallbackStmt .reverted := by
  exact ExecStmt.externalCallReturnDecodeRevert (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (liquidateCallbackArgs hf hb)
    (by simpa only [address_of_val] using hcall) (decodeLiquidateCallback_short hshort)

theorem liquidateCallbackSuccess {frame : Frame} {evm evm' : State} {m : MarketData}
    {id index seized repaid borrower mode badDebt : UInt256} {receiver callback : AccountAddress}
    {data out : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hb : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hcall : typedCallViaEVM fork config evm callback "onLiquidate" 0
      (liquidateCallbackArguments evm.executionEnv.source m id index seized repaid
        (AccountAddress.ofNat borrower.toNat) receiver data badDebt) (true, evm', out) true)
    (h32 : 32 ≤ out.size) :
    ExecStmt fork config frame evm liquidateCallbackStmt
      (.ok (liquidateCallbackFrame frame (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (liquidateCallbackArgs hf hb)
    (by simpa only [address_of_val] using hcall) (decodeLiquidateCallback h32)

end Benchmarks.Midnight
