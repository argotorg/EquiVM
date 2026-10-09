import Benchmarks.Safe.PaymentSource
import Benchmarks.Safe.ExecuteCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safePaymentMul {p : PaymentInput} {evm : EVM.State} {price : UInt256} {expr : Expr}
    (he : evalExpr? config (p.totalFrame evm.executionEnv) evm expr = .ok (uint256Value price))
    (hfit : p.gasTotal.toNat * price.toNat < UInt256.size) :
    ExecStmt config (p.totalFrame evm.executionEnv) evm
      (.internalCall "_mul" [.var "gasTotal", expr] "payment")
      (.ok (p.paidFrame evm.executionEnv price) evm) := by
  apply safeInternalMul rfl ?_ he hfit
  exact evalLocalValue (by simp [PaymentInput.totalFrame, Std.HashMap.getElem?_insert])

theorem safePaymentGasPrice (p : PaymentInput) (evm : EVM.State) :
    evalExpr? config (p.totalFrame evm.executionEnv) evm (.var "gasPrice") =
      .ok (uint256Value p.gasPrice) := evalLocalValue (by
  simp [PaymentInput.totalFrame, PaymentInput.receiverFrame, PaymentInput.frame,
    PaymentInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])

theorem safePaymentMulOverflow (p : PaymentInput) (evm : EVM.State)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hover : UInt256.size ≤ p.gasTotal.toNat *
      (if p.gasToken = EVM.address 0 then p.nativePrice evm.executionEnv else p.gasPrice).toNat) :
    ExecFuncBody config p.frame evm handlePaymentFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safePaymentPrefix hsum
  refine .consRevert ?_
  by_cases ht : p.gasToken = EVM.address 0
  · apply ExecStmt.iteTrue (by simpa only [ht, decide_true] using safePaymentTokenCondition p evm)
    apply ExecBlock.consRevert
    apply safeInternalMulOverflow (a := p.gasTotal) (b := p.nativePrice evm.executionEnv)
      rfl ?_ (safePaymentPrice p evm) (by simpa only [ht, ite_true] using hover)
    exact evalLocalValue (by simp [PaymentInput.totalFrame, Std.HashMap.getElem?_insert])
  · apply ExecStmt.iteFalse
      (by simpa only [ht, decide_false] using safePaymentTokenCondition p evm)
    apply ExecBlock.consRevert
    apply safeInternalMulOverflow (a := p.gasTotal) (b := p.gasPrice)
      rfl ?_ (safePaymentGasPrice p evm) (by simpa only [ht, ite_false] using hover)
    exact evalLocalValue (by simp [PaymentInput.totalFrame, Std.HashMap.getElem?_insert])

theorem safePaymentTokenCall {p : PaymentInput} {evm evm' : EVM.State} {f' : Frame} {z : Bool}
    (hc : ExecFuncBody config (p.tokenInput evm.executionEnv).frame evm transferTokenFunction.body
      (.returned f' evm' (some [.bool z]))) :
    ExecStmt config (p.paidFrame evm.executionEnv p.gasPrice) evm
      (.internalCall "transferToken" [.var "gasToken", .var "receiver", .var "payment"]
        "transferred") (.ok (p.tokenFinal evm.executionEnv z) evm') := by
  have ht := safeInternalTransferToken (p := p.tokenInput evm.executionEnv)
    (caller := p.paidFrame evm.executionEnv p.gasPrice) (retVar := "transferred")
    (token := .var "gasToken") (receiver := .var "receiver") (amount := .var "payment")
    rfl rfl (evalLocalValue (by
      simp [PaymentInput.paidFrame, PaymentInput.totalFrame, PaymentInput.receiverFrame,
        PaymentInput.frame, PaymentInput.args, PaymentInput.tokenInput,
        Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]))
    (evalLocalValue (by
      simp [PaymentInput.paidFrame, PaymentInput.totalFrame, PaymentInput.receiverFrame,
        PaymentInput.tokenInput, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]))
    (evalLocalValue (by
      simp [PaymentInput.paidFrame, PaymentInput.tokenInput, Std.HashMap.getElem?_insert])) hc
  exact ht

theorem safePaymentTokenSource {p : PaymentInput} {evm evm' : EVM.State} {f' : Frame} {z : Bool}
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * p.gasPrice.toNat < UInt256.size)
    (htoken : p.gasToken ≠ EVM.address 0)
    (hc : ExecFuncBody config (p.tokenInput evm.executionEnv).frame evm transferTokenFunction.body
      (.returned f' evm' (some [.bool z]))) :
    ExecFuncBody config p.frame evm handlePaymentFunction.body
      (if z then .returned (p.tokenFinal evm.executionEnv z) evm'
        (some [uint256Value (UInt256.mul p.gasTotal p.gasPrice)]) else .reverted) := by
  have hcond : evalExpr? config (p.totalFrame evm.executionEnv) evm
      (eqE (.var "gasToken") zeroAddr) = .ok (.bool false) := by
    simpa only [htoken, decide_false] using safePaymentTokenCondition p evm
  have hmul := safePaymentMul (safePaymentGasPrice p evm) hprod
  have hcall := safePaymentTokenCall hc
  have he : evalExpr? config (p.tokenFinal evm.executionEnv z) evm' (.var "transferred") =
      .ok (.bool z) := evalLocalValue (by
    simp [PaymentInput.tokenFinal, Std.HashMap.getElem?_insert])
  cases z
  · apply ExecFuncBody.execBlockRevert
    apply safePaymentPrefix hsum
    exact .consRevert (.iteFalse hcond
      (.consNormal hmul (.consNormal hcall (.consRevert (.requireFalse he)))))
  · apply ExecFuncBody.execBlockRet
    apply safePaymentPrefix hsum
    refine .consNormal (.iteFalse hcond
      (.consNormal hmul (.consNormal hcall (.consNormal (.requireTrue he) .nil))))
      (.consReturn (.return (evalExprs?_singleton ?_)))
    exact evalLocalValue (by simp [PaymentInput.tokenFinal, PaymentInput.paidFrame,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])

theorem safePaymentNativeCall {p : PaymentInput} {evm evm' : EVM.State} {z : Bool}
    {out : ByteArray}
    (hc : callViaEVM evm (EVM.address (p.receiver evm.executionEnv))
      (Int.ofNat (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv)).toNat)
      ByteArray.empty (z, evm', out)) :
    ExecStmt config (p.paidFrame evm.executionEnv (p.nativePrice evm.executionEnv)) evm
      (.lowLevelCall (.var "receiver") (.var "payment") emptyBytes "refundSuccess" "refundData")
      (.ok (p.nativeFinal evm.executionEnv z out) evm') := by
  have hr : evalExpr? config (p.paidFrame evm.executionEnv (p.nativePrice evm.executionEnv)) evm
      (.var "receiver") = .ok (.address (p.receiver evm.executionEnv)) := evalLocalValue (by
    simp [PaymentInput.paidFrame, PaymentInput.totalFrame, PaymentInput.receiverFrame,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  have hp : evalExpr? config (p.paidFrame evm.executionEnv (p.nativePrice evm.executionEnv)) evm
      (.var "payment") =
      .ok (uint256Value (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv))) :=
    evalLocalValue (by simp [PaymentInput.paidFrame, Std.HashMap.getElem?_insert])
  cases z
  · exact .lowLevelCallFailure hr hp (by simp only [emptyBytes, evalExpr?, pure]) hc
  · exact .lowLevelCallSuccess hr hp (by simp only [emptyBytes, evalExpr?, pure]) hc

theorem safePaymentNativeSource {p : PaymentInput} {evm evm' : EVM.State} {z : Bool}
    {out : ByteArray} (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * (p.nativePrice evm.executionEnv).toNat < UInt256.size)
    (htoken : p.gasToken = EVM.address 0)
    (hc : callViaEVM evm (EVM.address (p.receiver evm.executionEnv))
      (Int.ofNat (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv)).toNat)
      ByteArray.empty (z, evm', out)) :
    ExecFuncBody config p.frame evm handlePaymentFunction.body
      (if z then .returned (p.nativeFinal evm.executionEnv z out) evm'
        (some [uint256Value (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv))])
      else .reverted) := by
  have hcond : evalExpr? config (p.totalFrame evm.executionEnv) evm
      (eqE (.var "gasToken") zeroAddr) = .ok (.bool true) := by
    simpa only [htoken, decide_true] using safePaymentTokenCondition p evm
  have hmul := safePaymentMul (safePaymentPrice p evm) hprod
  have hcall := safePaymentNativeCall hc
  have he : evalExpr? config (p.nativeFinal evm.executionEnv z out) evm' (.var "refundSuccess") =
      .ok (.bool z) := evalLocalValue (by
    simp [PaymentInput.nativeFinal, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  cases z
  · apply ExecFuncBody.execBlockRevert
    apply safePaymentPrefix hsum
    exact .consRevert (.iteTrue hcond
      (.consNormal hmul (.consNormal hcall (.consRevert (.requireFalse he)))))
  · apply ExecFuncBody.execBlockRet
    apply safePaymentPrefix hsum
    refine .consNormal (.iteTrue hcond
      (.consNormal hmul (.consNormal hcall (.consNormal (.requireTrue he) .nil))))
      (.consReturn (.return (evalExprs?_singleton ?_)))
    exact evalLocalValue (by simp [PaymentInput.nativeFinal, PaymentInput.paidFrame,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])

theorem safePaymentNativeStatic (p : PaymentInput) (evm : EVM.State)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * (p.nativePrice evm.executionEnv).toNat < UInt256.size)
    (htoken : p.gasToken = EVM.address 0) (hperm : evm.executionEnv.perm = false)
    (hpayment : UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv) ≠ ⟨0⟩) :
    ExecFuncBody config p.frame evm handlePaymentFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply safePaymentPrefix hsum
  apply ExecBlock.consStatic
  apply ExecStmt.iteTrue
    (by simpa only [htoken, decide_true] using safePaymentTokenCondition p evm)
  refine .consNormal (safePaymentMul (safePaymentPrice p evm) hprod) (.consStatic ?_)
  apply ExecStmt.lowLevelCallStatic (target := p.receiver evm.executionEnv)
    (sendVal := Int.ofNat (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv)).toNat)
    (calldata := ByteArray.empty)
  · exact evalLocalValue (by simp [PaymentInput.paidFrame, PaymentInput.totalFrame,
      PaymentInput.receiverFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [PaymentInput.paidFrame, Std.HashMap.getElem?_insert])
  · simp only [emptyBytes, evalExpr?, pure]
  · simpa only [wordOfInt_ofNat_toNat] using hpayment
  · exact hperm

end Benchmarks.Safe
