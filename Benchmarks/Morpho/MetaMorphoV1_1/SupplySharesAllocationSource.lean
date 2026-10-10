import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesSource
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsSimulation

/-! Source execution of the supply-share reader, including compiler allocation failures. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem allocatedSupplySharesFunction_lookup :
    lookupCallable? contract allocatedSupplySharesFunction.name =
      some allocatedSupplySharesFunction.toCallable := by
  rfl

def allocatedSupplySharesFrame (imms : Store) (morpho user : AccountAddress)
    (id ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert cursorName (uint256Value ptr)).insert "user"
      (.address user)).insert "id" (wordBytes32Value id)).insert "morpho" (.address morpho)
    immutables := imms }

def allocatedSupplySharesPrefixFrame (imms : Store) (morpho user : AccountAddress)
    (id ptr : UInt256) : Frame :=
  { allocatedSupplySharesFrame imms morpho user id ptr with
    locals := (allocatedSupplySharesFrame imms morpho user id ptr).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨256⟩)) }

def allocatedSupplySharesCallFrame (imms : Store) (morpho user : AccountAddress)
    (id ptr : UInt256) : Frame :=
  { allocatedSupplySharesPrefixFrame imms morpho user id ptr with
    locals := ((allocatedSupplySharesPrefixFrame imms morpho user id ptr).locals.insert "__c0"
      (wordBytes32Value (positionSupplySharesSlot id user))).insert "slot"
      (.array [wordBytes32Value (positionSupplySharesSlot id user)]) }

def allocatedSupplySharesResultFrame (imms : Store) (morpho user : AccountAddress)
    (id ptr finalPtr : UInt256) (values : List Value) : Frame :=
  { allocatedSupplySharesCallFrame imms morpho user id ptr with
    locals := (allocatedSupplySharesCallFrame imms morpho user id ptr).locals.insert
      slotsAndCursorName (.tuple [.array values, uint256Value finalPtr]) }

theorem allocatedSupplySharesFrame_cursor (evm : State) (imms : Store)
    (morpho user : AccountAddress) (id ptr : UInt256) :
    evalExpr? config (allocatedSupplySharesFrame imms morpho user id ptr) evm
      (.var cursorName) = .ok (uint256Value ptr) := by
  simp only [evalExpr?, allocatedSupplySharesFrame,
    store_get_ne _ _ (by decide : ("morpho" == cursorName) = false),
    store_get_ne _ _ (by decide : ("id" == cursorName) = false),
    store_get_ne _ _ (by decide : ("user" == cursorName) = false),
    store_get_self, EvalResult.ofOption]

theorem allocatedSupplySharesPrefix (evm : State) (imms : Store)
    (morpho user : AccountAddress) (id ptr : UInt256) (hfit : allocationFits ptr ⟨256⟩) :
    ABlock config evm (allocatedSupplySharesFrame imms morpho user id ptr)
      allocatedSupplySharesFunction.body
      (allocatedSupplySharesCallFrame imms morpho user id ptr)
      (allocatedSupplySharesFunction.body.drop 3) := by
  constructor
  intro result htail
  refine ExecBlock.consNormal (allocateCallReturns (cfg := config)
    (frame := allocatedSupplySharesFrame imms morpho user id ptr) cursorName
    allocateFunction_lookup (allocatedSupplySharesFrame_cursor evm imms morpho user id ptr)
    (by simp only [evalExpr?, pure]; rfl) hfit) ?_
  refine ExecBlock.consNormal (positionSupplySharesSlotCall evm _ imms id user "__c0" _ _ ?_ ?_)
    (ExecBlock.consNormal (morphoArrayCall evm _ imms
      (wordBytes32Value (positionSupplySharesSlot id user)) "slot" _ ?_) htail)
  · simp only [evalExpr?, allocatedSupplySharesFrame,
      store_get_ne _ _ (by decide : (cursorName == "id") = false),
      store_get_ne _ _ (by decide : ("morpho" == "id") = false),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, allocatedSupplySharesFrame,
      store_get_ne _ _ (by decide : (cursorName == "user") = false),
      store_get_ne _ _ (by decide : ("morpho" == "user") = false),
      store_get_ne _ _ (by decide : ("id" == "user") = false),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption]

theorem allocatedSupplySharesBodyPrefixReverts (evm : State) (imms : Store)
    (morpho user : AccountAddress) (id ptr : UInt256) (hfit : ¬ allocationFits ptr ⟨256⟩) :
    ExecFuncBody config (allocatedSupplySharesFrame imms morpho user id ptr) evm
      allocatedSupplySharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (allocateCallReverts (cfg := config)
    (frame := allocatedSupplySharesFrame imms morpho user id ptr) cursorName
    allocateFunction_lookup (allocatedSupplySharesFrame_cursor evm imms morpho user id ptr)
    (by simp only [evalExpr?, pure]; rfl) hfit)

theorem allocatedSupplySharesCall_args (evm : State) (imms : Store)
    (morpho user : AccountAddress) (id ptr : UInt256) :
    evalExprs? config (allocatedSupplySharesCallFrame imms morpho user id ptr) evm
      [.var "morpho", .var "slot", .var cursorName] =
      .ok [.address morpho, .array [wordBytes32Value (positionSupplySharesSlot id user)],
        uint256Value (nextCursor ptr ⟨256⟩)] := by
  simp only [evalExprs?, evalExpr?, allocatedSupplySharesCallFrame,
    allocatedSupplySharesPrefixFrame, allocatedSupplySharesFrame,
    store_get_ne _ _ (by decide : ("slot" == "morpho") = false),
    store_get_ne _ _ (by decide : ("__c0" == "morpho") = false),
    store_get_ne _ _ (by decide : (cursorName == "morpho") = false),
    store_get_ne _ _ (by decide : ("slot" == cursorName) = false),
    store_get_ne _ _ (by decide : ("__c0" == cursorName) = false),
    store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem allocatedSupplySharesBodyCallReverts (evm : State) (imms : Store)
    (morpho user : AccountAddress) (id ptr : UInt256) (hfit : allocationFits ptr ⟨256⟩)
    (hbody : ExecFuncBody config
      (extSloadsFrame (allocatedSupplySharesCallFrame imms morpho user id ptr)
        (nextCursor ptr ⟨256⟩) morpho [wordBytes32Value (positionSupplySharesSlot id user)])
      evm extSloadsFunction.body .reverted) :
    ExecFuncBody config (allocatedSupplySharesFrame imms morpho user id ptr) evm
      allocatedSupplySharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (allocatedSupplySharesPrefix evm imms morpho user id ptr hfit).run
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := extSloadsFunction) (allocatedSupplySharesCall_args evm imms morpho user id ptr)
    extSloadsFunction_lookup rfl hbody)

theorem allocatedSupplySharesBodyReturnPrefix {evm evm' : State} {imms : Store}
    {morpho user : AccountAddress} {id ptr finalPtr : UInt256} {values : List Value}
    {calleeFrame : Frame} (hfit : allocationFits ptr ⟨256⟩)
    (hbody : ExecFuncBody config
      (extSloadsFrame (allocatedSupplySharesCallFrame imms morpho user id ptr)
        (nextCursor ptr ⟨256⟩) morpho [wordBytes32Value (positionSupplySharesSlot id user)])
      evm extSloadsFunction.body
      (.returned calleeFrame evm' (some [.array values, uint256Value finalPtr])))
    {result : ExecResult}
    (htail : ExecBlock config
      (allocatedSupplySharesResultFrame imms morpho user id ptr finalPtr values) evm'
      (allocatedSupplySharesFunction.body.drop 4) result) :
    ExecBlock config (allocatedSupplySharesFrame imms morpho user id ptr) evm
      allocatedSupplySharesFunction.body result := by
  apply (allocatedSupplySharesPrefix evm imms morpho user id ptr hfit).run
  exact ExecBlock.consNormal (internalCallFunctionReturn
    (callee := extSloadsFunction) (allocatedSupplySharesCall_args evm imms morpho user id ptr)
    extSloadsFunction_lookup rfl hbody) htail

theorem allocatedSupplySharesBodyReturns {evm evm' : State} {imms : Store}
    {morpho user : AccountAddress} {id ptr finalPtr value : UInt256} {values : List Value}
    {calleeFrame : Frame} (hfit : allocationFits ptr ⟨256⟩)
    (hbody : ExecFuncBody config
      (extSloadsFrame (allocatedSupplySharesCallFrame imms morpho user id ptr)
        (nextCursor ptr ⟨256⟩) morpho [wordBytes32Value (positionSupplySharesSlot id user)])
      evm extSloadsFunction.body
      (.returned calleeFrame evm'
        (some [.array (wordBytes32Value value :: values), uint256Value finalPtr]))) :
    ExecFuncBody config (allocatedSupplySharesFrame imms morpho user id ptr) evm
      allocatedSupplySharesFunction.body
      (.returned
        (allocatedSupplySharesResultFrame imms morpho user id ptr finalPtr
          (wordBytes32Value value :: values)) evm'
        (some [uint256Value value, uint256Value finalPtr])) := by
  apply ExecFuncBody.execBlockRet
  apply allocatedSupplySharesBodyReturnPrefix hfit hbody
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hv : evalExpr? config
      (allocatedSupplySharesResultFrame imms morpho user id ptr finalPtr
        (wordBytes32Value value :: values)) evm'
      (.cast (.index (.tupleGet (.var slotsAndCursorName) 0) (.intLit 0))
        (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (uint256Value value) := by
    apply evalExpr_bytes32ToUint
    apply evalExpr_arrayHead (value := wordBytes32Value value) (values := values)
    simp only [evalExpr?, allocatedSupplySharesResultFrame, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind]
    rfl
  change evalExprs? config _ evm'
    [.cast (.index (.tupleGet (.var slotsAndCursorName) 0) (.intLit 0))
       (.elem (.int (.uint ⟨256, by decide⟩))),
     .tupleGet (.var slotsAndCursorName) 1] = _
  simp only [evalExprs?, hv, bind, EvalResult.bind, pure]
  simp only [evalExpr?, allocatedSupplySharesResultFrame, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind]
  rfl

theorem allocatedSupplySharesBodyEmpty {evm evm' : State} {imms : Store}
    {morpho user : AccountAddress} {id ptr finalPtr : UInt256} {calleeFrame : Frame}
    (hfit : allocationFits ptr ⟨256⟩)
    (hbody : ExecFuncBody config
      (extSloadsFrame (allocatedSupplySharesCallFrame imms morpho user id ptr)
        (nextCursor ptr ⟨256⟩) morpho [wordBytes32Value (positionSupplySharesSlot id user)])
      evm extSloadsFunction.body
      (.returned calleeFrame evm' (some [.array [], uint256Value finalPtr]))) :
    ExecFuncBody config (allocatedSupplySharesFrame imms morpho user id ptr) evm
      allocatedSupplySharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply allocatedSupplySharesBodyReturnPrefix hfit hbody
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  simp only [evalExprs?, evalExpr?, allocatedSupplySharesResultFrame, store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure, evalIndex?]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
