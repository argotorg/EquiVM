import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawFunction

/-! The public maxRedeem wrapper and its final conversion of assets to shares. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxRedeemInitialFrame (locals imms : Store) (data : ByteArray) : Frame :=
  { contract := contract
    locals := (locals.insert "__calldata" (.bytes data)).insert cursorName (uint256Value ⟨128⟩)
    immutables := imms }

def maxRedeemResumedFrame (frame : Frame) (assets supply total ptr : UInt256) : Frame :=
  cursorResultFrame frame "__c0"
    (.tuple [uint256Value assets, uint256Value supply, uint256Value total]) ptr

def maxRedeemTotalsFrame (frame : Frame) (assets supply total ptr : UInt256) : Frame :=
  { maxRedeemResumedFrame frame assets supply total ptr with
    locals := (((maxRedeemResumedFrame frame assets supply total ptr).locals.insert "assets"
      (uint256Value assets)).insert "newTotalSupply" (uint256Value supply)).insert
      "newTotalAssets" (uint256Value total) }

def maxRedeemConvertArgs : List Expr :=
  [.var "assets", .var "newTotalSupply", .var "newTotalAssets", .intLit 0]

def maxRedeemConversionTail : List Stmt :=
  [.internalCall "_convertToSharesWithTotals" maxRedeemConvertArgs "__c1", .return [.var "__c1"]]

def maxRedeemPublicTail : List Stmt :=
  [.letDecl "assets" (some abiUInt256) (.tupleGet (.var "__c0") 0),
    .letDecl "newTotalSupply" (some abiUInt256) (.tupleGet (.var "__c0") 1),
    .letDecl "newTotalAssets" (some abiUInt256) (.tupleGet (.var "__c0") 2)] ++
      maxRedeemConversionTail

theorem maxRedeemTransition_tail :
    maxRedeemTransition.body.drop 3 =
      .letDecl cursorName none (.intLit 128) ::
        (cursorCall allocatedMaxWithdrawFunction.name [.var "owner"] "__c0" ++
          maxRedeemPublicTail) := by decide +kernel

theorem maxRedeemSourcePrefix (v : MetaMorphoV1_1Immutables) {evm : State} (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, locals, immStore v⟩ maxRedeemTransition.body
      (maxRedeemInitialFrame locals (immStore v) evm.executionEnv.calldata)
      (cursorCall allocatedMaxWithdrawFunction.name [.var "owner"] "__c0" ++
        maxRedeemPublicTail) := by
  refine ⟨fun h ↦ ?_⟩
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  change ExecBlock _ _ _ (maxRedeemTransition.body.drop 3) _
  rw [maxRedeemTransition_tail]
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl)) h

theorem maxRedeemWithdrawArgs {locals imms : Store} {data : ByteArray} {evm : State}
    {owner : AccountAddress} (ho : locals.get? "owner" = some (.address owner)) :
    evalExprs? config (maxRedeemInitialFrame locals imms data) evm
      [.var "owner", .var cursorName] = .ok [.address owner, uint256Value ⟨128⟩] := by
  simp only [evalExprs?, evalExpr?, maxRedeemInitialFrame, store_get_self,
    store_get_ne _ _ (by decide : (cursorName == "owner") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "owner") = false),
    ho, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem maxRedeemBodyReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} (locals : Store) {owner : AccountAddress}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : locals.get? "owner" = some (.address owner))
    (hbody : ExecFuncBody config (maxWithdrawFrame (immStore v) owner ⟨128⟩) evm
      allocatedMaxWithdrawFunction.body .reverted) :
    ExecTransitionBody config contract evm locals maxRedeemTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (maxRedeemSourcePrefix v locals hwv hhi).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedMaxWithdrawFunction)
    (maxRedeemWithdrawArgs ho) rfl rfl hbody)

theorem maxRedeemTotalsSource (frame : Frame) (evm : State) (assets supply total ptr : UInt256) :
    ABlock config evm (maxRedeemResumedFrame frame assets supply total ptr) maxRedeemPublicTail
      (maxRedeemTotalsFrame frame assets supply total ptr) maxRedeemConversionTail := by
  have hv := cursorResultFrame_value frame "__c0"
    (.tuple [uint256Value assets, uint256Value supply, uint256Value total]) ptr (by decide)
  refine ⟨fun h ↦ ?_⟩
  dsimp only [maxRedeemTotalsFrame] at h
  dsimp only [maxRedeemPublicTail, List.append]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value assets) ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value supply) ?_)
    · apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value total) ?_)
      · exact h
      · simp only [evalExpr?, maxRedeemResumedFrame,
        store_get_ne _ _ (by decide : ("newTotalSupply" == "__c0") = false),
        store_get_ne _ _ (by decide : ("assets" == "__c0") = false),
          hv, EvalResult.ofOption, bind, EvalResult.bind]; rfl
    · simp only [evalExpr?, maxRedeemResumedFrame,
        store_get_ne _ _ (by decide : ("assets" == "__c0") = false),
        hv, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  · simp only [evalExpr?, maxRedeemResumedFrame,
      hv, EvalResult.ofOption, bind, EvalResult.bind]; rfl

theorem maxRedeemConvertArgsSource (frame : Frame) (evm : State)
    (assets supply total ptr : UInt256) :
    evalExprs? config (maxRedeemTotalsFrame frame assets supply total ptr) evm
      maxRedeemConvertArgs = .ok [uint256Value assets, uint256Value supply, uint256Value total,
        uint256Value ⟨0⟩] := by
  simp [maxRedeemConvertArgs, maxRedeemTotalsFrame, evalExprs?, evalExpr?,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem maxRedeemBodyPrefix (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {owner : AccountAddress} {final : Frame}
    {assets supply total ptr : UInt256} {outcome : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : locals.get? "owner" = some (.address owner))
    (hbody : ExecFuncBody config (maxWithdrawFrame (immStore v) owner ⟨128⟩) evm
      allocatedMaxWithdrawFunction.body
      (.returned final evm'
        [.tuple [uint256Value assets, uint256Value supply, uint256Value total], uint256Value ptr]))
    (htail : ExecBlock config (maxRedeemTotalsFrame
      (maxRedeemInitialFrame locals (immStore v) evm.executionEnv.calldata) assets supply total ptr)
      evm' maxRedeemConversionTail outcome) :
    ExecBlock config ⟨contract, locals, immStore v⟩ evm maxRedeemTransition.body outcome := by
  apply (maxRedeemSourcePrefix v locals hwv hhi).run
  apply cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedMaxWithdrawFunction)
      (maxRedeemWithdrawArgs ho) rfl rfl hbody)
  exact (maxRedeemTotalsSource _ evm' assets supply total ptr).run htail

theorem maxRedeemBodyConvertReverts (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {owner : AccountAddress} {final : Frame}
    {assets supply total ptr : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : locals.get? "owner" = some (.address owner))
    (hbody : ExecFuncBody config (maxWithdrawFrame (immStore v) owner ⟨128⟩) evm
      allocatedMaxWithdrawFunction.body
      (.returned final evm'
        [.tuple [uint256Value assets, uint256Value supply, uint256Value total], uint256Value ptr]))
    (hbad : ¬ convertSharesFits v.DECIMALS_OFFSET assets supply total) :
    ExecTransitionBody config contract evm locals maxRedeemTransition.body .reverted
      (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply maxRedeemBodyPrefix v locals hwv hhi ho hbody
  exact ExecBlock.consRevert (convertSharesCallReverts v
    (maxRedeemConvertArgsSource
      (maxRedeemInitialFrame locals (immStore v) evm.executionEnv.calldata)
      evm' assets supply total ptr) hbad)

theorem maxRedeemBodyReturns (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} (locals : Store) {owner : AccountAddress} {final : Frame}
    {assets supply total ptr : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : locals.get? "owner" = some (.address owner))
    (hbody : ExecFuncBody config (maxWithdrawFrame (immStore v) owner ⟨128⟩) evm
      allocatedMaxWithdrawFunction.body
      (.returned final evm'
        [.tuple [uint256Value assets, uint256Value supply, uint256Value total], uint256Value ptr]))
    (hfit : convertSharesFits v.DECIMALS_OFFSET assets supply total) :
    let result := convertSharesWord v.DECIMALS_OFFSET assets supply total
    let totals := maxRedeemTotalsFrame
      (maxRedeemInitialFrame locals (immStore v) evm.executionEnv.calldata) assets supply total ptr
    ExecTransitionBody config contract evm locals maxRedeemTransition.body
      (.returned { totals with locals := totals.locals.insert "__c1" (uint256Value result) }
        evm' [uint256Value result]) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply maxRedeemBodyPrefix v locals hwv hhi ho hbody
  apply ExecBlock.consNormal (convertSharesCall v
    (maxRedeemConvertArgsSource
      (maxRedeemInitialFrame locals (immStore v) evm.executionEnv.calldata)
      evm' assets supply total ptr) hfit)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
