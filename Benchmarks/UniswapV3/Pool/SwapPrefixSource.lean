import Benchmarks.UniswapV3.Pool.SwapModel
import Benchmarks.UniswapV3.Pool.NoDelegateCall
import Benchmarks.UniswapV3.Pool.SourceSignedDivision

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

macro "swap_prefix_get" : tactic =>
  `(tactic| (simp only [swapDelegateFrame, swapInitFrame, poolAmountsFrame, swapFrame,
    swapLocals, resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

theorem swapZerosSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config (swapFrame v a) evm (swapTransition.body.take 3)
      (.ok (swapInitFrame v a) evm) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "amount0")
    (ty := some (.elem (.int (.sint ⟨256, by decide⟩)))) (value := .int 0)
    (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (name := "amount1")
    (ty := some (.elem (.int (.sint ⟨256, by decide⟩)))) (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem swapDelegateCall (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hself : evm.executionEnv.codeOwner = v.original) :
    ExecStmt config (swapInitFrame v a) evm (.internalCall "checkNotDelegateCall" [] "__c0")
      (.ok (swapDelegateFrame v a) evm) :=
  internalCallFunctionReturn (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
    (calleeSolm := noDelegateCallFrame v) (value := none)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl (noDelegateCallReturns v evm hself)

theorem swapDelegateSource (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) :
    ExecBlock config (swapFrame v a) evm (swapTransition.body.take 4)
      (.ok (swapDelegateFrame v a) evm) := by
  change ExecBlock config _ _ (swapTransition.body.take 3 ++
    [.internalCall "checkNotDelegateCall" [] "__c0"]) _
  exact execBlock_append_ok (swapZerosSource v a evm hwv)
    (ExecBlock.consNormal (swapDelegateCall v a evm hself) ExecBlock.nil)

theorem evalSwapSpecifiedNonzero (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) :
    evalExpr? config (swapDelegateFrame v a) evm
      (.binary .ne (.var "amountSpecified") (.intLit 0)) =
      .ok (.bool (decide (a.amountSpecified ≠ 0))) := by
  have he : evalExpr? config (swapDelegateFrame v a) evm (.var "amountSpecified") =
      .ok (.int a.amountSpecified) := evalExpr_var_get (by swap_prefix_get)
  exact evalExpr_int_ne he (by simp only [evalExpr?, pure])

theorem swapSlot0Source (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified ≠ 0) :
    ExecBlock config (swapFrame v a) evm (swapTransition.body.take 6)
      (.ok (swapSlot0Frame v a evm) evm) := by
  change ExecBlock config _ _ (swapTransition.body.take 4 ++
    [swapTransition.body[4]!, swapTransition.body[5]!]) _
  apply execBlock_append_ok (swapDelegateSource v a evm hwv hself)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [ne_eq, hn, not_false_eq_true, decide_true] using evalSwapSpecifiedNonzero v a evm
  · exact ExecBlock.consNormal (ExecStmt.letDecl
      (evalSlot0Struct _ (immStore v) evm (by swap_prefix_get))) ExecBlock.nil

theorem swapDelegateReverts (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner ≠ v.original) :
    ExecTransitionBody config contract evm (swapLocals a) swapTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 swapTransition.body]
  apply execBlock_append_ok (swapZerosSource v a evm hwv)
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := noDelegateCallFunction)
    (argVals := []) (locals := ∅) (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl
    (noDelegateCallReverts v evm hself))

theorem swapSpecifiedReverts (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hself : evm.executionEnv.codeOwner = v.original)
    (hn : a.amountSpecified = 0) :
    ExecTransitionBody config contract evm (swapLocals a) swapTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 swapTransition.body]
  apply execBlock_append_ok (swapDelegateSource v a evm hwv hself)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hn, ne_self_iff_false, decide_false] using evalSwapSpecifiedNonzero v a evm

end Benchmarks.UniswapV3.Pool
