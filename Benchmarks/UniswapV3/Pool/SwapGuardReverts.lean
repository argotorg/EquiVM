import Benchmarks.UniswapV3.Pool.SwapGuardsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapLockedReverts (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified ≠ 0)
    (hu : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (swapLocals a) swapTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 6 swapTransition.body]
  apply execBlock_append_ok (swapSlot0Source v a evm hwv hself hn)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hu, decide_true, Bool.not_true] using evalSwapUnlocked v a evm

theorem swapLimitReverts (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified ≠ 0)
    (hu : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hl : ¬swapLimitValid a evm) :
    ExecTransitionBody config contract evm (swapLocals a) swapTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 6 swapTransition.body]
  apply execBlock_append_ok (swapSlot0Source v a evm hwv hself hn)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
  · simpa only [hu, decide_false, Bool.not_false] using evalSwapUnlocked v a evm
  · simpa only [hl, decide_false] using evalSwapLimit v a evm

theorem swapStatic (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified ≠ 0)
    (hu : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hl : swapLimitValid a evm) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (swapLocals a) swapTransition.body .staticViolation
      (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 8 swapTransition.body]
  apply execBlock_append_ok (swapGuardsSource v a evm hwv hself hn hu hl)
  exact ExecBlock.consStatic (execStmt_assign_static (swapAssignLock v a evm) hperm)

end Benchmarks.UniswapV3.Pool
