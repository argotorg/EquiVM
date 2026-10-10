import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.PoolLiquidityStorage
import Benchmarks.UniswapV3.Pool.NoDelegateCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure FlashArgs where
  recipient : AccountAddress
  amount0 : UInt256
  amount1 : UInt256
  data : ByteArray

def flashLocals (a : FlashArgs) : Store :=
  ((((∅ : Store).insert "recipient" (.address a.recipient)).insert "amount0"
    (.int (Int.ofNat a.amount0.toNat))).insert "amount1" (.int (Int.ofNat a.amount1.toNat))).insert
      "data" (.bytes a.data)

def flashFrame (v : UniswapV3PoolImmutables) (a : FlashArgs) : Frame :=
  {contract := contract, locals := flashLocals a, immutables := immStore v}

def flashCheckedFrame (v : UniswapV3PoolImmutables) (a : FlashArgs) : Frame :=
  {flashFrame v a with locals := (flashLocals a).insert "__c0" .unit}

def flashReadyFrame (v : UniswapV3PoolImmutables) (a : FlashArgs) (liquidity : UInt256) : Frame :=
  {flashCheckedFrame v a with
    locals := (flashCheckedFrame v a).locals.insert "_liquidity" (.int (Int.ofNat liquidity.toNat))}

theorem evalFlashUnlocked (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs) :
    evalExpr? config (flashFrame v a) evm (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [← wordToElemBool]
  exact evalSlot0Unlocked _ _ _ (by simp [flashLocals])

theorem flashRevertsLocked (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (flashLocals a) flashTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireRevert
  simpa only [hlocked, decide_true, Bool.not_true] using evalFlashUnlocked v evm a

theorem flashAssignLock (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs) :
    ExecStmt config (flashFrame v a) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (flashFrame v a) (storeSlot0Unlocked evm false)) :=
  ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm _ _ false (by simp [flashLocals]))

theorem flashLockPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (flashFrame v a) evm (flashTransition.body.take 3)
      (.ok (flashFrame v a) (storeSlot0Unlocked evm false)) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using evalFlashUnlocked v evm a
  · exact ExecBlock.consNormal (flashAssignLock v evm a) ExecBlock.nil

theorem flashStatic (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (flashLocals a) flashTransition.body .staticViolation
      (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using evalFlashUnlocked v evm a
  · exact ExecBlock.consStatic (execStmt_assign_static (flashAssignLock v evm a) hperm)

theorem flashRevertsDelegate (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hdelegate : evm.executionEnv.codeOwner ≠ v.original) :
    ExecTransitionBody config contract evm (flashLocals a) flashTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 flashTransition.body]
  apply execBlock_append_ok (flashLockPrefix v evm a hwv hunlocked)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (argVals := []) (locals := ∅)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl
    (noDelegateCallReverts v _ (by simpa only [storeSlot0Unlocked_executionEnv] using hdelegate))

theorem flashLoadLiquidityPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) :
    let locked := storeSlot0Unlocked evm false
    ExecBlock config (flashFrame v a) evm (flashTransition.body.take 5)
      (.ok (flashReadyFrame v a (poolLiquidityWord locked.accountMap locked.executionEnv)) locked) := by
  change ExecBlock _ _ _ (flashTransition.body.take 3 ++ (flashTransition.body.drop 3).take 2) _
  apply execBlock_append_ok (flashLockPrefix v evm a hwv hunlocked)
  have hcall : ExecStmt config (flashFrame v a) (storeSlot0Unlocked evm false)
      (.internalCall "checkNotDelegateCall" [] "__c0")
      (.ok (flashCheckedFrame v a) (storeSlot0Unlocked evm false)) :=
    internalCallFunctionReturn (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
      (calleeSolm := noDelegateCallFrame v) (value := none)
      (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl
      (noDelegateCallReturns v _ (by simpa only [storeSlot0Unlocked_executionEnv] using hself))
  refine ExecBlock.consNormal hcall ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl
    (evalLiquidity _ _ _ (by simp [flashCheckedFrame, flashLocals]))) ExecBlock.nil

theorem evalFlashLiquidityGuard (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (a : FlashArgs) (liquidity : UInt256) :
    evalExpr? config (flashReadyFrame v a liquidity) evm (.binary .gt (.var "_liquidity") (.intLit 0)) =
      .ok (.bool (decide (0 < liquidity.toNat))) := by
  exact evalExpr_word_gt (a := liquidity) (b := ⟨0⟩)
    (evalExpr_var_get (by simp [flashReadyFrame])) (by simp only [evalExpr?, pure]; rfl)

theorem flashReadyPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original)
    (hliq : 0 < (poolLiquidityWord (storeSlot0Unlocked evm false).accountMap
      (storeSlot0Unlocked evm false).executionEnv).toNat) :
    let locked := storeSlot0Unlocked evm false
    ExecBlock config (flashFrame v a) evm (flashTransition.body.take 6)
      (.ok (flashReadyFrame v a (poolLiquidityWord locked.accountMap locked.executionEnv)) locked) := by
  change ExecBlock _ _ _ (flashTransition.body.take 5 ++ [.require
    (.binary .gt (.var "_liquidity") (.intLit 0))]) _
  apply execBlock_append_ok (flashLoadLiquidityPrefix v evm a hwv hunlocked hself)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [hliq, decide_true] using
    evalFlashLiquidityGuard v (storeSlot0Unlocked evm false) a
      (poolLiquidityWord (storeSlot0Unlocked evm false).accountMap
        (storeSlot0Unlocked evm false).executionEnv)

theorem flashRevertsLiquidity (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original)
    (hliq : ¬ 0 < (poolLiquidityWord (storeSlot0Unlocked evm false).accountMap
      (storeSlot0Unlocked evm false).executionEnv).toNat) :
    ExecTransitionBody config contract evm (flashLocals a) flashTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 flashTransition.body]
  apply execBlock_append_ok (flashLoadLiquidityPrefix v evm a hwv hunlocked hself)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hliq, decide_false] using
    evalFlashLiquidityGuard v (storeSlot0Unlocked evm false) a
      (poolLiquidityWord (storeSlot0Unlocked evm false).accountMap
        (storeSlot0Unlocked evm false).executionEnv)

end Benchmarks.UniswapV3.Pool
