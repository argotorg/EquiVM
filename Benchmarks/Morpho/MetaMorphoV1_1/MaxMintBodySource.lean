import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositBodySource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedConvertSimulation

/-! Source composition for maxMint's capacity and accrued-share conversion calls. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxMintInitialFrame (locals imms : Store) (data : ByteArray) : Frame :=
  { contract := contract
    locals := (locals.insert "__calldata" (.bytes data)).insert cursorName (uint256Value ⟨128⟩)
    immutables := imms }

def maxMintDepositFrame (locals imms : Store) (data : ByteArray) (assets ptr : UInt256) : Frame :=
  cursorResultFrame (maxMintInitialFrame locals imms data) "suppliable" (uint256Value assets) ptr

def maxMintConversionTail : List Stmt :=
  cursorCall allocatedConvertToSharesFunction.name [.var "suppliable", .intLit 0] "__c1" ++
    [.return [.var "__c1"]]

theorem maxMintTransition_tail :
    maxMintTransition.body.drop 3 =
      .letDecl cursorName none (.intLit 128) ::
        (cursorCall allocatedMaxDepositFunction.name [] "suppliable" ++ maxMintConversionTail) :=
  by decide +kernel

theorem maxMintSourcePrefix (v : MetaMorphoV1_1Immutables) {evm : State} (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := locals, immutables := immStore v }
      maxMintTransition.body (maxMintInitialFrame locals (immStore v) evm.executionEnv.calldata)
      (cursorCall allocatedMaxDepositFunction.name [] "suppliable" ++ maxMintConversionTail) := by
  refine ⟨fun h ↦ ?_⟩
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  change ExecBlock _ _ _ (maxMintTransition.body.drop 3) _
  rw [maxMintTransition_tail]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩) ?_) h
  simp only [evalExpr?, pure]; rfl

theorem maxMintDepositArgs (locals imms : Store) (data : ByteArray) (evm : State) :
    evalExprs? config (maxMintInitialFrame locals imms data) evm [.var cursorName] =
      .ok [uint256Value ⟨128⟩] := by
  simp only [evalExprs?, evalExpr?, maxMintInitialFrame, store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem maxMintConvertArgs (locals imms : Store) (data : ByteArray) (evm : State)
    (assets ptr : UInt256) :
    evalExprs? config (maxMintDepositFrame locals imms data assets ptr) evm
      [.var "suppliable", .intLit 0, .var cursorName] =
      .ok [uint256Value assets, uint256Value ⟨0⟩, uint256Value ptr] := by
  have hv := cursorResultFrame_value (maxMintInitialFrame locals imms data)
    "suppliable" (uint256Value assets) ptr (by decide)
  have hp := cursorResultFrame_cursor (maxMintInitialFrame locals imms data)
    "suppliable" (uint256Value assets) ptr
  simp only [evalExprs?, evalExpr?, maxMintDepositFrame, hv, hp,
    EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem maxMintDepositSource (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {final : Frame} {assets ptr : UInt256}
    (hbody : ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ⟨128⟩) evm
      allocatedMaxDepositFunction.body
      (.returned final evm' [uint256Value assets, uint256Value ptr]))
    {outcome : ExecResult}
    (htail : ExecBlock config
      (maxMintDepositFrame locals (immStore v) evm.executionEnv.calldata assets ptr) evm'
      maxMintConversionTail outcome) :
    ExecBlock config (maxMintInitialFrame locals (immStore v) evm.executionEnv.calldata) evm
      (cursorCall allocatedMaxDepositFunction.name [] "suppliable" ++ maxMintConversionTail)
      outcome := by
  exact cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedMaxDepositFunction)
      (maxMintDepositArgs locals (immStore v) evm.executionEnv.calldata evm)
      allocatedMaxDepositFunction_lookup rfl hbody) htail

theorem maxMintBodyDepositReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbody : ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ⟨128⟩) evm
      allocatedMaxDepositFunction.body .reverted) :
    ExecTransitionBody config contract evm locals maxMintTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (maxMintSourcePrefix v locals hwv hhi).run
  exact ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedMaxDepositFunction)
      (maxMintDepositArgs locals (immStore v) evm.executionEnv.calldata evm)
      allocatedMaxDepositFunction_lookup rfl hbody)

theorem maxMintBodyConvertReverts (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {final : Frame} {assets ptr : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hdeposit : ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ⟨128⟩) evm
      allocatedMaxDepositFunction.body
      (.returned final evm' [uint256Value assets, uint256Value ptr]))
    (hconvert : ExecFuncBody config (allocatedConvertFrame (immStore v) assets ptr) evm'
      allocatedConvertToSharesFunction.body .reverted) :
    ExecTransitionBody config contract evm locals maxMintTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (maxMintSourcePrefix v locals hwv hhi).run
  apply maxMintDepositSource v locals hdeposit
  exact ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedConvertToSharesFunction)
      (maxMintConvertArgs locals (immStore v) evm.executionEnv.calldata evm' assets ptr)
      rfl rfl hconvert)

theorem maxMintBodyReturns (v : MetaMorphoV1_1Immutables)
    {evm evm' evm'' : State} (locals : Store) {final final' : Frame}
    {assets ptr result ptr' : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hdeposit : ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ⟨128⟩) evm
      allocatedMaxDepositFunction.body
      (.returned final evm' [uint256Value assets, uint256Value ptr]))
    (hconvert : ExecFuncBody config (allocatedConvertFrame (immStore v) assets ptr) evm'
      allocatedConvertToSharesFunction.body
      (.returned final' evm'' [uint256Value result, uint256Value ptr'])) :
    ExecTransitionBody config contract evm locals maxMintTransition.body
      (.returned (cursorResultFrame
        (maxMintDepositFrame locals (immStore v) evm.executionEnv.calldata assets ptr)
        "__c1" (uint256Value result) ptr') evm'' [uint256Value result]) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (maxMintSourcePrefix v locals hwv hhi).run
  apply maxMintDepositSource v locals hdeposit
  apply cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedConvertToSharesFunction)
      (maxMintConvertArgs locals (immStore v) evm.executionEnv.calldata evm' assets ptr)
      rfl rfl hconvert)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, cursorResultFrame_value _ "__c1" _ _ (by decide),
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
