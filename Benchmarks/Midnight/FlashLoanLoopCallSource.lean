import Benchmarks.Midnight.FlashLoanLoopSource

/-! Internal-call source steps for the two flash-loan transfer loops. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def flashLoanLoopCallFrame (isFrom : Bool) (frame : Frame) : Frame :=
  resumeAfterInternalCall frame (if isFrom then "__c2" else "__c0") none

theorem flashLoanLoopCallFrame_spec (isFrom : Bool) {frame : Frame}
    {tokens assets : List UInt256} {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data) :
    FlashLoanSourceFrame (flashLoanLoopCallFrame isFrom frame) tokens assets callback data :=
  hf.insert _ .unit (by cases isFrom <;> decide)

theorem flashLoanLoopCallFrame_index (isFrom : Bool) {frame : Frame} {i : Nat}
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) :
    (flashLoanLoopCallFrame isFrom frame).locals.get? "i" = some (.int (Int.ofNat i)) := by
  unfold flashLoanLoopCallFrame resumeAfterInternalCall
  rw [store_get_ne _ _ (by cases isFrom <;> decide), hi]

theorem flashLoanLoopCallReturn (isFrom : Bool) {frame calleeFrame : Frame}
    {evm evm' : EVM.State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray} {i : Nat}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i)))
    (ht : i < tokens.length) (ha : i < assets.length)
    (hbody : ExecFuncBody config
      (safeTransferFrame isFrom frame.immutables (AccountAddress.ofNat tokens[i].toNat)
        (if isFrom then callback else evm.executionEnv.source)
        (if isFrom then evm.executionEnv.codeOwner else callback) assets[i]) evm
      (safeTransferFunctionFor isFrom).body (.returned calleeFrame evm' none)) :
    ExecBlock config frame evm (flashLoanLoopBody isFrom)
      (.ok (flashLoanLoopCallFrame isFrom frame) evm') := by
  apply ExecBlock.consNormal ?_ ExecBlock.nil
  apply internalCallFunctionReturn (flashLoanLoopArguments_eval isFrom hf hi ht ha)
    (by rw [hf.contract]; exact safeTransferLookup isFrom) (safeTransferBind isFrom ..)
  simpa only [safeTransferFrame, hf.contract] using hbody

theorem flashLoanLoopCallRevert (isFrom : Bool) {frame : Frame} {evm : EVM.State}
    {tokens assets : List UInt256} {callback : AccountAddress} {data : ByteArray} {i : Nat}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i)))
    (ht : i < tokens.length) (ha : i < assets.length)
    (hbody : ExecFuncBody config
      (safeTransferFrame isFrom frame.immutables (AccountAddress.ofNat tokens[i].toNat)
        (if isFrom then callback else evm.executionEnv.source)
        (if isFrom then evm.executionEnv.codeOwner else callback) assets[i]) evm
      (safeTransferFunctionFor isFrom).body .reverted) :
    ExecBlock config frame evm (flashLoanLoopBody isFrom) .reverted := by
  apply ExecBlock.consRevert
  apply internalCallFunctionRevert (flashLoanLoopArguments_eval isFrom hf hi ht ha)
    (by rw [hf.contract]; exact safeTransferLookup isFrom) (safeTransferBind isFrom ..)
  simpa only [safeTransferFrame, hf.contract] using hbody

end Benchmarks.Midnight
