import Benchmarks.Morpho.MetaMorphoV1_1.ShareViewConversionSimulation

/-! The public share views call the allocated conversion and return its value component. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def shareViewCallerFrame (locals imms : Store) (data : ByteArray) : Frame :=
  { contract := contract
    locals := locals.insert "__calldata" (.bytes data)
    immutables := imms }

theorem shareViewBodyReturns (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {final : Frame} {assets total cursor : UInt256}
    (hassets : locals.get? "assets" = some (uint256Value assets))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedConvertFrame (immStore v) assets ⟨128⟩) evm
      allocatedConvertToSharesFunction.body
      (.returned final evm' (some [uint256Value total, uint256Value cursor]))) :
    ExecTransitionBody config contract evm locals allocatedShareViewBody
      (.returned (resumeAfterInternalCall
        (shareViewCallerFrame locals (immStore v) evm.executionEnv.calldata) "__c0"
        (some [uint256Value total, uint256Value cursor])) evm' (some [uint256Value total]))
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal
    (internalCallFunctionReturn (callee := allocatedConvertToSharesFunction)
      (argVals := [uint256Value assets, uint256Value ⟨0⟩, uint256Value ⟨128⟩])
      ?_ rfl rfl hbody)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
    rfl
  · simp only [evalExprs?, evalExpr?,
      store_get_ne _ _ (by decide : ("__calldata" == "assets") = false),
      hassets, EvalResult.ofOption, bind, EvalResult.bind, pure]
    rfl

theorem shareViewBodyReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} (locals : Store) {assets : UInt256}
    (hassets : locals.get? "assets" = some (uint256Value assets))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedConvertFrame (immStore v) assets ⟨128⟩) evm
      allocatedConvertToSharesFunction.body .reverted) :
    ExecTransitionBody config contract evm locals allocatedShareViewBody .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedConvertToSharesFunction)
      (argVals := [uint256Value assets, uint256Value ⟨0⟩, uint256Value ⟨128⟩])
      ?_ rfl rfl hbody)
  simp only [evalExprs?, evalExpr?,
    store_get_ne _ _ (by decide : ("__calldata" == "assets") = false),
    hassets, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
