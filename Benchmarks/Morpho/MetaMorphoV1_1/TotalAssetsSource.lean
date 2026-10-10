import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsSimulation

/-! totalAssets returns the total component of the cursor-aware accrued-assets helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def totalAssetsCallerFrame (locals imms : Store) (data : ByteArray) : Frame :=
  { contract := contract, locals := locals.insert "__calldata" (.bytes data), immutables := imms }

def totalAssetsResultFrame (frame : Frame) (lost total shares ptr : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "__c0"
      (.tuple [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
        uint256Value ptr])).insert "newTotalAssets" (uint256Value total) }

theorem totalAssetsBodyReturns (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {final : Frame} {lost total shares ptr : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ⟨128⟩) evm
      allocatedAccruedFeeAssetsFunction.body
      (.returned final evm'
        [.tuple [uint256Value shares, uint256Value total, uint256Value lost], uint256Value ptr])) :
    ExecTransitionBody config contract evm locals totalAssetsTransition.body
      (.returned
        (totalAssetsResultFrame
          (totalAssetsCallerFrame locals (immStore v) evm.executionEnv.calldata)
          lost total shares ptr)
        evm' [uint256Value total]) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal
    (internalCallFunctionReturn (callee := allocatedAccruedFeeAssetsFunction)
      (argVals := [uint256Value ⟨128⟩]) ?_ rfl rfl hbody)
  · apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value total) ?_)
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp only [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption,
        bind, EvalResult.bind, pure]
    · simp only [evalExpr?, resumeAfterInternalCall, collapseReturns, store_get_self,
        EvalResult.ofOption, bind, EvalResult.bind]
      rfl
  · simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]
    rfl

theorem totalAssetsBodyReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ⟨128⟩) evm
      allocatedAccruedFeeAssetsFunction.body .reverted) :
    ExecTransitionBody config contract evm locals totalAssetsTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedAccruedFeeAssetsFunction)
      (argVals := [uint256Value ⟨128⟩]) ?_ rfl rfl hbody)
  simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
