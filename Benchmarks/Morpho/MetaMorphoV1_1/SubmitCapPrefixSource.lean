import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapSyntax

/-! Source authorization, asset validation, and the modular last-update call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

set_option maxRecDepth 2000

theorem submitCapPrefix (evm : State) (imms : Store) (out : ByteArray) (cap : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, submitCapInitialLocals out cap, imms⟩ submitCapBody
      (submitCapParamsFrame evm imms out cap) (submitCapBody.drop 5) := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (ExecStmt.letDecl (marketParamsTupleStructSource out ?_))
  · refine ExecBlock.consNormal ?_ htail
    apply ExecStmt.letDecl
    simp only [evalExpr?, pure]; rfl
  · simp [evalExpr?, submitCapInitialLocals, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem submitCapRolePrefix (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm) :
    ABlock config evm ⟨contract, submitCapInitialLocals out cap, immStore v⟩ submitCapBody
      (submitCapAssetFrame v evm out cap)
      (.require submitCapAssetCondition :: submitCapReader ++ submitCapGuards ++
        [submitCapBranch]) := by
  constructor
  intro result htail
  apply (submitCapPrefix evm (immStore v) out cap hwv hhi).run
  apply ExecBlock.consNormal (curatorRoleCall evm _ (immStore v) "__role" hrole)
  apply ExecBlock.consNormal (marketParamsIdCall evm _ (immStore v) (marketParamsData out)
    "id" (.var "marketParams") ?_)
  · exact ExecBlock.consNormal
      (internalCallReturnExpr (retTy := [.elem .address]) (expr := .immutable "_asset")
        (value := .address v._asset) rfl (evalImmutable__asset _ _ _ _ _)) htail
  · simp [evalExpr?, submitCapRoleFrame, submitCapParamsFrame, cursorName,
      Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem submitCapAssetSource (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap : UInt256) :
    evalExpr? config (submitCapAssetFrame v evm out cap) evm submitCapAssetCondition =
      .ok (.bool (decide ((marketParamsData out).loanToken = v._asset))) := by
  apply evalExpr_addressEq
  · have hp : evalExpr? config (submitCapAssetFrame v evm out cap) evm
        (.var "marketParams") = .ok (marketParamsData out).value := by
      simp [evalExpr?, submitCapAssetFrame, submitCapHashFrame, submitCapRoleFrame,
        submitCapParamsFrame, cursorName, Std.HashMap.getElem_insert, EvalResult.ofOption]
    exact evalExpr_structField hp rfl
  · simp only [evalExpr?, submitCapAssetFrame, store_get_self, EvalResult.ofOption]

theorem submitCapReaderPrefix (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (ha : (marketParamsData out).loanToken = v._asset) :
    ABlock config evm ⟨contract, submitCapInitialLocals out cap, immStore v⟩ submitCapBody
      (submitCapAssetFrame v evm out cap) (submitCapReader ++ submitCapGuards ++
        [submitCapBranch]) :=
  (submitCapRolePrefix v evm out cap hwv hhi hrole).requireStep
    (by rw [submitCapAssetSource, decide_eq_true ha])

theorem submitCapReaderArgs (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap : UInt256) :
    evalExprs? config (submitCapAssetFrame v evm out cap) evm
      [.immutable "MORPHO", .var "id", .var cursorName] =
      .ok [.address v.MORPHO, wordBytes32Value (marketParamsData out).id,
        uint256Value ⟨288⟩] := by
  have hm : evalExpr? config (submitCapAssetFrame v evm out cap) evm
      (.immutable "MORPHO") = .ok (.address v.MORPHO) := evalImmutable_MORPHO _ _ _ _ _
  simp only [evalExprs?, hm, bind, EvalResult.bind, pure]
  simp [evalExpr?, submitCapAssetFrame, submitCapHashFrame, submitCapRoleFrame,
    submitCapParamsFrame, cursorName, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem submitCapBodyRoleReverts (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : ¬ curatorRoleAllowed evm) :
    ExecTransitionBody config contract evm (submitCapInitialLocals out cap) submitCapBody
      .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (submitCapPrefix evm (immStore v) out cap hwv hhi).run
  exact ExecBlock.consRevert (curatorRoleCallReverts evm _ (immStore v) "__role" hrole)

theorem submitCapBodyAssetReverts (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (ha : (marketParamsData out).loanToken ≠ v._asset) :
    ExecTransitionBody config contract evm (submitCapInitialLocals out cap) submitCapBody
      .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  exact (submitCapRolePrefix v evm out cap hwv hhi hrole).requireRevert
    (by rw [submitCapAssetSource, decide_eq_false ha])

theorem submitCapBodyReaderReverts (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (ha : (marketParamsData out).loanToken = v._asset)
    (hcallee : ExecFuncBody config
      (lastUpdateFrame (immStore v) v.MORPHO (marketParamsData out).id ⟨288⟩) evm
      allocatedLastUpdateFunction.body .reverted) :
    ExecTransitionBody config contract evm (submitCapInitialLocals out cap) submitCapBody
      .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (submitCapReaderPrefix v evm out cap hwv hhi hrole ha).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedLastUpdateFunction)
    (submitCapReaderArgs v evm out cap) allocatedLastUpdateFunction_lookup rfl hcallee)

theorem submitCapReaderReturnPrefix (v : MetaMorphoV1_1Immutables) (evm evm' : State)
    (out : ByteArray) (cap last cursor : UInt256) :
    ABlock config evm' (submitCapReaderFrame v evm out cap last cursor)
      (submitCapReader.drop 1 ++ submitCapGuards ++ [submitCapBranch])
      (submitCapResultFrame v evm out cap last cursor) (submitCapGuards ++ [submitCapBranch]) := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value last) ?_)
  · refine ExecBlock.consNormal ?_ htail
    apply ExecStmt.letDecl
    simp [evalExpr?, submitCapReaderFrame, resumeAfterInternalCall, collapseReturns,
      slotsAndCursorName,
      tupleGetValue?, Std.HashMap.getElem_insert, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  · simp [evalExpr?, submitCapReaderFrame, resumeAfterInternalCall, collapseReturns,
      slotsAndCursorName,
      tupleGetValue?, Std.HashMap.getElem_insert, EvalResult.ofOption,
      bind, EvalResult.bind, pure]

theorem submitCapReaderContinue (v : MetaMorphoV1_1Immutables) (evm evm' : State)
    (out : ByteArray) (cap last cursor : UInt256) (final : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (ha : (marketParamsData out).loanToken = v._asset)
    (hcallee : ExecFuncBody config
      (lastUpdateFrame (immStore v) v.MORPHO (marketParamsData out).id ⟨288⟩) evm
      allocatedLastUpdateFunction.body
      (.returned final evm' (some [uint256Value last, uint256Value cursor])))
    {result : ExecResult}
    (htail : ExecBlock config (submitCapResultFrame v evm out cap last cursor) evm'
      (submitCapGuards ++ [submitCapBranch]) result) :
    ExecBlock config ⟨contract, submitCapInitialLocals out cap, immStore v⟩ evm
      submitCapBody result := by
  apply (submitCapReaderPrefix v evm out cap hwv hhi hrole ha).run
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedLastUpdateFunction)
    (submitCapReaderArgs v evm out cap) allocatedLastUpdateFunction_lookup rfl hcallee)
  exact (submitCapReaderReturnPrefix v evm evm' out cap last cursor).run htail

end Benchmarks.Morpho.MetaMorphoV1_1
