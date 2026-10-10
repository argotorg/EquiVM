import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawFunction

/-! The public maxWithdraw wrapper around the internal withdrawal calculation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxWithdrawInitialFrame (locals imms : Store) (data : ByteArray) : Frame :=
  { contract := contract
    locals := ((locals.insert "__calldata" (.bytes data)).insert "assets"
      (uint256Value ⟨0⟩)).insert cursorName (uint256Value ⟨128⟩)
    immutables := imms }

def maxWithdrawPublicReturnFrame (frame : Frame) (assets supply total ptr : UInt256) : Frame :=
  let resumed := cursorResultFrame frame "__c0"
    (.tuple [uint256Value assets, uint256Value supply, uint256Value total]) ptr
  { resumed with locals := resumed.locals.insert "assets" (uint256Value assets) }

def maxWithdrawPublicTail : List Stmt :=
  [.assign .localVar ⟨"assets", []⟩ (.tupleGet (.var "__c0") 0), .return [.var "assets"]]

theorem maxWithdrawTransition_tail :
    maxWithdrawTransition.body.drop 3 =
      [.letDecl "assets" (some abiUInt256) (.intLit 0),
        .letDecl cursorName none (.intLit 128)] ++
      cursorCall allocatedMaxWithdrawFunction.name [.var "owner"] "__c0" ++
        maxWithdrawPublicTail := by decide +kernel

theorem maxWithdrawSourcePrefix (v : MetaMorphoV1_1Immutables) {evm : State} (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, locals, immStore v⟩ maxWithdrawTransition.body
      (maxWithdrawInitialFrame locals (immStore v) evm.executionEnv.calldata)
      (cursorCall allocatedMaxWithdrawFunction.name [.var "owner"] "__c0" ++
        maxWithdrawPublicTail) := by
  refine ⟨fun h ↦ ?_⟩
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  change ExecBlock _ _ _ (maxWithdrawTransition.body.drop 3) _
  rw [maxWithdrawTransition_tail]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl)) h

theorem maxWithdrawPublicArgs {locals imms : Store} {data : ByteArray} {evm : State}
    {owner : AccountAddress} (ho : locals.get? "owner" = some (.address owner)) :
    evalExprs? config (maxWithdrawInitialFrame locals imms data) evm
      [.var "owner", .var cursorName] = .ok [.address owner, uint256Value ⟨128⟩] := by
  simp only [evalExprs?, evalExpr?, maxWithdrawInitialFrame, store_get_self,
    store_get_ne _ _ (by decide : (cursorName == "owner") = false),
    store_get_ne _ _ (by decide : ("assets" == "owner") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "owner") = false),
    ho, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem maxWithdrawBodyReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} (locals : Store) {owner : AccountAddress}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : locals.get? "owner" = some (.address owner))
    (hbody : ExecFuncBody config (maxWithdrawFrame (immStore v) owner ⟨128⟩) evm
      allocatedMaxWithdrawFunction.body .reverted) :
    ExecTransitionBody config contract evm locals maxWithdrawTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (maxWithdrawSourcePrefix v locals hwv hhi).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedMaxWithdrawFunction)
    (maxWithdrawPublicArgs ho) rfl rfl hbody)

theorem maxWithdrawBodyReturns (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {owner : AccountAddress} {final : Frame}
    {assets supply total ptr : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : locals.get? "owner" = some (.address owner))
    (hbody : ExecFuncBody config (maxWithdrawFrame (immStore v) owner ⟨128⟩) evm
      allocatedMaxWithdrawFunction.body
      (.returned final evm'
        [.tuple [uint256Value assets, uint256Value supply, uint256Value total],
          uint256Value ptr])) :
    ExecTransitionBody config contract evm locals maxWithdrawTransition.body
      (.returned (maxWithdrawPublicReturnFrame
        (maxWithdrawInitialFrame locals (immStore v) evm.executionEnv.calldata)
        assets supply total ptr) evm' [uint256Value assets]) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (maxWithdrawSourcePrefix v locals hwv hhi).run
  apply cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedMaxWithdrawFunction)
      (maxWithdrawPublicArgs ho) rfl rfl hbody)
  have hv := cursorResultFrame_value
    (maxWithdrawInitialFrame locals (immStore v) evm.executionEnv.calldata) "__c0"
    (.tuple [uint256Value assets, uint256Value supply, uint256Value total]) ptr (by decide)
  apply ExecBlock.consNormal (ExecStmt.assign (value := uint256Value assets) ?_ ?_)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, maxWithdrawPublicReturnFrame, store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  · simp only [evalExpr?, hv, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  · simp [assignStorageRef?, updateLocalPath?, maxWithdrawPublicReturnFrame,
      cursorResultFrame, maxWithdrawInitialFrame,
      cursorName, slotsAndCursorName, Std.HashMap.getElem_insert,
      bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
