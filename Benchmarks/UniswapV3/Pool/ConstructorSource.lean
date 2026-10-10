import Benchmarks.UniswapV3.Pool.ConstructorFieldsSource
import Benchmarks.UniswapV3.Pool.TickSpacingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem evalConstructorSpacingArgs (original : AccountAddress) (evm : EVM.State)
    (out : ByteArray) :
    evalExprs? config (constructorSpacingFrame original out) evm [.var "_tickSpacing"] =
      .ok [.int (constructorSpacing out)] := by
  have he : evalExpr? config (constructorSpacingFrame original out) evm (.var "_tickSpacing") =
      .ok (.int (constructorSpacing out)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem constructorLiquidityCall (original : AccountAddress) (evm : EVM.State) (out : ByteArray)
    (hn : constructorSpacing out ≠ 0) (hc : spacingCount (constructorSpacing out) ≠ 0) :
    ExecStmt config (constructorSpacingFrame original out) evm (contract.ctor.body[13]!)
      (.ok (constructorLiquidityFrame original out) evm) := by
  exact internalCallFunctionReturn (callee := tickSpacingFunction)
    (locals := tickSpacingLocals (constructorSpacing out))
    (calleeSolm := tickSpacingReadyFrame (constructorSpacingImms original out) (constructorSpacing out))
    (value := some [.int (spacingLiquidity (constructorSpacing out))])
    (evalConstructorSpacingArgs original evm out) tickSpacingLookup
    (tickSpacingBind (constructorSpacing out))
    (tickSpacingReturns (constructorSpacingImms original out) evm (constructorSpacing out) hn hc)

theorem constructorFinalSource (original : AccountAddress) (evm : EVM.State) (out : ByteArray)
    (hn : constructorSpacing out ≠ 0) (hc : spacingCount (constructorSpacing out) ≠ 0) :
    ExecBlock config (constructorSpacingFrame original out) evm (contract.ctor.body.drop 13)
      (.ok (constructorFinalFrame original out) evm) := by
  refine ExecBlock.consNormal (constructorLiquidityCall original evm out hn hc) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (spacingLiquidity (constructorSpacing out)))
    (ty := .int (.uint ⟨256, by decide⟩))
    (evalExpr_var_get Std.HashMap.getElem?_insert_self) rfl ?_) ExecBlock.nil
  have hb := spacingLiquidity_bounds (constructorSpacing out)
  simp only [elemValueFits, decide_eq_true_eq]
  change 0 ≤ spacingLiquidity (constructorSpacing out) ∧
    spacingLiquidity (constructorSpacing out) < 2 ^ 256
  exact ⟨hb.1, by omega⟩

theorem constructorReturns (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm evm.executionEnv.source 0 constructorParameterCalldata
      (true, evm', out) false) (hlen : 160 ≤ out.size)
    (hn : constructorSpacing out ≠ 0) (hc : spacingCount (constructorSpacing out) ≠ 0) :
    ExecFuncBody config constructorInitialFrame evm contract.ctor.body
      (.returned (constructorFinalFrame evm.executionEnv.codeOwner out) evm' none) := by
  apply ExecFuncBody.execBlockOK
  rw [← List.take_append_drop 13 contract.ctor.body]
  exact execBlock_append_ok (constructorBeforeSpacingSource evm evm' out hwv hcode hcall hlen)
    (constructorFinalSource _ evm' out hn hc)

theorem constructorRevertsSpacing (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word evm.executionEnv.source.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm evm.executionEnv.source 0 constructorParameterCalldata
      (true, evm', out) false) (hlen : 160 ≤ out.size)
    (hz : constructorSpacing out = 0 ∨ spacingCount (constructorSpacing out) = 0) :
    ExecFuncBody config constructorInitialFrame evm contract.ctor.body .reverted := by
  have hb : ExecFuncBody config
      (tickSpacingFrame (constructorSpacingImms evm.executionEnv.codeOwner out) (constructorSpacing out))
      evm' tickSpacingFunction.body .reverted := by
    by_cases hn : constructorSpacing out = 0
    · rw [hn]
      exact tickSpacingRevertsZero _ evm'
    · exact tickSpacingRevertsCount _ evm' _ hn (hz.resolve_left hn)
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 13 contract.ctor.body]
  apply execBlock_append_ok (constructorBeforeSpacingSource evm evm' out hwv hcode hcall hlen)
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := tickSpacingFunction)
    (locals := tickSpacingLocals (constructorSpacing out))
    (evalConstructorSpacingArgs _ evm' out) tickSpacingLookup
    (tickSpacingBind (constructorSpacing out)) hb)

end Benchmarks.UniswapV3.Pool
