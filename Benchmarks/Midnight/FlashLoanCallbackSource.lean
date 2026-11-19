import Benchmarks.Midnight.FlashLoanCallbackABI
import Benchmarks.Midnight.FlashLoanSource

/-! Source execution of the callback and its required bytes32 acknowledgement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def flashLoanCallbackStmt : Stmt :=
  .externalCall (.var "callback") "onFlashLoan" (.intLit 0)
    [.env .caller, .var "tokens", .var "assets", .var "data"] "__c1" true

def flashLoanMagicGuard : Expr :=
  .binary .eq (.var "__c1") (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE flashLoanMagic))

def flashLoanCallbackFrame (frame : Frame) (value : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c1" (wordBytes32Value value) }

theorem flashLoanCallback_shape :
    flashLoanTransition.body.drop 6 = flashLoanCallbackStmt :: .require flashLoanMagicGuard ::
      flashLoanTransition.body.drop 8 := by decide +kernel

theorem flashLoanCallbackFrame_spec {frame : Frame} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data) (value : UInt256) :
    FlashLoanSourceFrame (flashLoanCallbackFrame frame value) tokens assets callback data :=
  hf.insert "__c1" _ (by simp)

theorem flashLoanCallbackArgs {frame : Frame} {evm : State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data) :
    evalExprs? config frame evm [.env .caller, .var "tokens", .var "assets", .var "data"] =
      .ok (flashLoanCallbackArguments evm.executionEnv.source tokens assets data) := by
  simp only [evalExprs?, evalExpr?, hf.tokens, hf.assets, hf.data, envValue, EvalResult.ofOption,
    bind, pure, EvalResult.bind, flashLoanCallbackArguments]

theorem wordBytes32Value_beq (a b : UInt256) :
    (wordBytes32Value a == wordBytes32Value b) = decide (a = b) := by
  by_cases h : a = b
  · subst b
    rw [decide_eq_true rfl]
    exact beq_self_eq_true _
  · rw [decide_eq_false h]
    apply beq_eq_false_iff_ne.mpr
    intro he
    apply h
    have hw := congrArg Stele.valueToWord he
    simpa only [wordBytes32Value, abiBytes32Width, valueToWord_bytes32_word, Option.some.injEq] using hw

theorem flashLoanMagicGuard_eval (frame : Frame) (evm : State) (value : UInt256) :
    evalExpr? config (flashLoanCallbackFrame frame value) evm flashLoanMagicGuard =
      .ok (.bool (decide (value = flashLoanMagic))) := by
  simp only [flashLoanMagicGuard, evalExpr?, flashLoanCallbackFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true, if_true,
    EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?, wordBytes32Value_beq]

theorem flashLoanCallbackFailure {frame : Frame} {evm evm' : State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data out : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hcall : typedCallViaEVM config evm callback "onFlashLoan" 0
      (flashLoanCallbackArguments evm.executionEnv.source tokens assets data) (false, evm', out) true) :
    ExecStmt config frame evm flashLoanCallbackStmt .reverted := by
  exact ExecStmt.externalCallFailure (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (flashLoanCallbackArgs hf) (by simpa only [address_of_val] using hcall)

theorem flashLoanCallbackShort {frame : Frame} {evm evm' : State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data out : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hcall : typedCallViaEVM config evm callback "onFlashLoan" 0
      (flashLoanCallbackArguments evm.executionEnv.source tokens assets data) (true, evm', out) true)
    (hshort : out.size < 32) :
    ExecStmt config frame evm flashLoanCallbackStmt .reverted := by
  exact ExecStmt.externalCallReturnDecodeRevert (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (flashLoanCallbackArgs hf) (by simpa only [address_of_val] using hcall)
    (decodeFlashLoanCallback_short hshort)

theorem flashLoanCallbackSuccess {frame : Frame} {evm evm' : State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data out : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hcall : typedCallViaEVM config evm callback "onFlashLoan" 0
      (flashLoanCallbackArguments evm.executionEnv.source tokens assets data) (true, evm', out) true)
    (h32 : 32 ≤ out.size) :
    ExecStmt config frame evm flashLoanCallbackStmt
      (.ok (flashLoanCallbackFrame frame (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, hf.callback, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (flashLoanCallbackArgs hf) (by simpa only [address_of_val] using hcall)
    (decodeFlashLoanCallback h32)

end Benchmarks.Midnight
