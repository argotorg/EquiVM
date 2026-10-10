import Benchmarks.Morpho.MetaMorphoV1_1.AssetViewConversionSimulation

/-! The public asset views call the allocated conversion and return its value component. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def assetViewCallerFrame (locals imms : Store) (data : ByteArray) : Frame :=
  { contract := contract
    locals := locals.insert "__calldata" (.bytes data)
    immutables := imms }

theorem assetViewBodyReturns (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {final : Frame} {assets total cursor : UInt256}
    (hassets : locals.get? "shares" = some (uint256Value assets))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedAssetsFrame (immStore v) assets ⟨128⟩) evm
      allocatedConvertToAssetsFunction.body
      (.returned final evm' (some [uint256Value total, uint256Value cursor]))) :
    ExecTransitionBody config contract evm locals allocatedAssetViewBody
      (.returned (resumeAfterInternalCall
        (assetViewCallerFrame locals (immStore v) evm.executionEnv.calldata) "__c0"
        (some [uint256Value total, uint256Value cursor])) evm' (some [uint256Value total]))
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal
    (internalCallFunctionReturn (callee := allocatedConvertToAssetsFunction)
      (argVals := [uint256Value assets, uint256Value ⟨0⟩, uint256Value ⟨128⟩])
      ?_ rfl rfl hbody)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
    rfl
  · simp only [evalExprs?, evalExpr?,
      store_get_ne _ _ (by decide : ("__calldata" == "shares") = false),
      hassets, EvalResult.ofOption, bind, EvalResult.bind, pure]
    rfl

theorem assetViewBodyReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} (locals : Store) {assets : UInt256}
    (hassets : locals.get? "shares" = some (uint256Value assets))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedAssetsFrame (immStore v) assets ⟨128⟩) evm
      allocatedConvertToAssetsFunction.body .reverted) :
    ExecTransitionBody config contract evm locals allocatedAssetViewBody .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedConvertToAssetsFunction)
      (argVals := [uint256Value assets, uint256Value ⟨0⟩, uint256Value ⟨128⟩])
      ?_ rfl rfl hbody)
  simp only [evalExprs?, evalExpr?,
    store_get_ne _ _ (by decide : ("__calldata" == "shares") = false),
    hassets, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
