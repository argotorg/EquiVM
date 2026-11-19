import Benchmarks.Midnight.TakeLock

/-! Source execution of restoring and reading the seller's liquidation lock. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeUnlockCondition : Expr := .unary .not (.var "wasLocked")

def takeUnlockStmt : Stmt := .internalCall "UtilsLib_tExchange"
  [.cast (.keccak256 (.bytesLit "morpho.midnight.liquidationLocked".toByteArray))
    (.elem (.int (.uint ⟨256, by decide⟩))), .var "id", .var "seller", .boolLit false] "__c31"

def takeUnlockFrame (frame : Frame) (evm : State) (id seller : UInt256) : Frame :=
  resumeAfterInternalCall frame "__c31" (some [lockValue evm liquidationLockBase id seller])

theorem takeUnlock_shape : takeTransition.body[71]! =
    .ite takeUnlockCondition [takeUnlockStmt] [] := by decide +kernel

theorem takeUnlockCondition_eval {frame : Frame} {evm : State} {wasLocked : UInt256}
    (hw : frame.locals.get? "wasLocked" = some (wordToElem .bool wasLocked)) :
    evalExpr? config frame evm takeUnlockCondition = .ok (.bool (decide (wasLocked = ⟨0⟩))) := by
  simp only [takeUnlockCondition, evalExpr?, hw, EvalResult.ofOption, EvalResult.bind,
    bind, wordToElemBool, evalUnaryOp?, Bool.not_not]

theorem takeUnlockSource {frame : Frame} {evm : State} {id seller : UInt256}
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hs : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hp : evm.executionEnv.perm = true) :
    ExecStmt config frame evm takeUnlockStmt
      (.ok (takeUnlockFrame frame evm id seller)
        (lockExchangeState evm liquidationLockBase id seller false)) := by
  apply callLockExchange hc hcanon
  · change evalExprs? config frame evm
      [.cast (.keccak256 (.bytesLit "morpho.midnight.liquidationLocked".toByteArray))
        (.elem (.int (.uint ⟨256, by decide⟩))), .var "id", .var "seller", .boolLit false] = _
    rw [evalExprs?, evalLiquidationLockBase]
    simp only [evalExprs?, evalExpr?, hi, hs, EvalResult.ofOption, EvalResult.bind, bind, pure]
    rfl
  · exact hp

def takeLockedFrame (frame : Frame) (evm : State) (id seller : UInt256) : Frame :=
  resumeAfterInternalCall frame "locked" (some [lockValue evm liquidationLockBase id seller])

theorem takeLockedSource {frame : Frame} {evm : State} {id seller : UInt256}
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hs : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat))) :
    ExecStmt config frame evm takeTransition.body[72]!
      (.ok (takeLockedFrame frame evm id seller) evm) := by
  apply internalCallFunctionReturn (callee := liquidationLockedFunction)
    (locals := lockBodyArguments id seller)
    (argVals := [wordBytes32Value id, .address (AccountAddress.ofNat seller.toNat)])
  · simp only [evalExprs?, evalExpr?, hi, hs, EvalResult.ofOption, EvalResult.bind, bind, pure]
  · rw [hc]; rfl
  · rfl
  · simpa only [hc] using liquidationLockedInternalReturns evm frame.immutables id seller hcanon

end Benchmarks.Midnight
