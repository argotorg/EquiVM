import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositFunction

/-! The public max-deposit body calls the allocated helper and returns its first result. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def maxDepositCallerFrame (locals imms : Store) (data : ByteArray) : Frame :=
  { contract := contract
    locals := locals.insert "__calldata" (.bytes data)
    immutables := imms }

theorem maxDepositBodyReturns (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {final : Frame} {total cursor : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ⟨128⟩) evm
      allocatedMaxDepositFunction.body
      (.returned final evm' (some [uint256Value total, uint256Value cursor]))) :
    ExecTransitionBody config contract evm locals maxDepositTransition.body
      (.returned (resumeAfterInternalCall
        (maxDepositCallerFrame locals (immStore v) evm.executionEnv.calldata) "__c0"
        (some [uint256Value total, uint256Value cursor])) evm' (some [uint256Value total]))
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal
    (internalCallFunctionReturn (callee := allocatedMaxDepositFunction)
      (argVals := [uint256Value ⟨128⟩]) ?_ allocatedMaxDepositFunction_lookup rfl hbody)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
    rfl
  · simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]
    rfl

theorem maxDepositBodyReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ⟨128⟩) evm
      allocatedMaxDepositFunction.body .reverted) :
    ExecTransitionBody config contract evm locals maxDepositTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedMaxDepositFunction)
      (argVals := [uint256Value ⟨128⟩]) ?_ allocatedMaxDepositFunction_lookup rfl hbody)
  simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
