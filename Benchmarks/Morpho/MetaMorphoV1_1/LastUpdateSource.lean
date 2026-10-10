import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSlotSource
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesSource
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptCapStorage

/-! Source execution of the allocated last-update reader. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option maxRecDepth 2000

theorem allocatedLastUpdateFunction_lookup :
    lookupCallable? contract allocatedLastUpdateFunction.name =
      some allocatedLastUpdateFunction.toCallable := by rfl

def lastUpdateFrame (imms : Store) (morpho : AccountAddress) (id ptr : UInt256) : Frame :=
  ⟨contract, (((∅ : Store).insert cursorName (uint256Value ptr)).insert "id"
    (wordBytes32Value id)).insert "morpho" (.address morpho), imms⟩

def lastUpdateAllocatedFrame (imms : Store) (morpho : AccountAddress) (id ptr : UInt256) : Frame :=
  { lastUpdateFrame imms morpho id ptr with
    locals := (lastUpdateFrame imms morpho id ptr).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨160⟩)) }

def lastUpdateCallFrame (imms : Store) (morpho : AccountAddress) (id ptr : UInt256) : Frame :=
  { lastUpdateAllocatedFrame imms morpho id ptr with
    locals := ((lastUpdateAllocatedFrame imms morpho id ptr).locals.insert "__c0"
      (wordBytes32Value (lastUpdateSlot id))).insert "slot"
      (.array [wordBytes32Value (lastUpdateSlot id)]) }

def lastUpdateResultFrame (imms : Store) (morpho : AccountAddress)
    (id ptr cursor : UInt256) (values : List Value) : Frame :=
  { lastUpdateCallFrame imms morpho id ptr with
    locals := (lastUpdateCallFrame imms morpho id ptr).locals.insert slotsAndCursorName
      (.tuple [.array values, uint256Value cursor]) }

def lastUpdateValue (word : UInt256) : UInt256 :=
  UInt256.land word (UInt256.ofNat (2 ^ 128 - 1))

theorem lastUpdateValue_toNat (word : UInt256) :
    (lastUpdateValue word).toNat = word.toNat % 2 ^ 128 := by
  rw [lastUpdateValue, uland_toNat,
    UInt256.toNat_ofNat_of_lt (by decide : 2 ^ 128 - 1 < UInt256.size)]
  exact nat_land_mask_eq_mod _ _

theorem lastUpdateAllocationPrefix (evm : State) (imms : Store) (morpho : AccountAddress)
    (id ptr : UInt256) (hfit : allocationFits ptr ⟨160⟩) :
    ABlock config evm (lastUpdateFrame imms morpho id ptr) allocatedLastUpdateFunction.body
      (lastUpdateAllocatedFrame imms morpho id ptr) (allocatedLastUpdateFunction.body.drop 1) := by
  constructor
  intro result htail
  exact ExecBlock.consNormal (allocateCallReturns cursorName allocateFunction_lookup
    (by simp [evalExpr?, lastUpdateFrame, Std.HashMap.getElem_insert, EvalResult.ofOption,
      cursorName])
    (by simp only [evalExpr?, pure]; rfl) hfit) htail

theorem lastUpdatePrefix (evm : State) (imms : Store) (morpho : AccountAddress)
    (id ptr : UInt256) (hfit : allocationFits ptr ⟨160⟩)
    (hslot : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size) :
    ABlock config evm (lastUpdateFrame imms morpho id ptr) allocatedLastUpdateFunction.body
      (lastUpdateCallFrame imms morpho id ptr) (allocatedLastUpdateFunction.body.drop 3) := by
  constructor
  intro result htail
  apply (lastUpdateAllocationPrefix evm imms morpho id ptr hfit).run
  refine ExecBlock.consNormal (lastUpdateSlotCall evm _ imms id "__c0" (.var "id") ?_ hslot)
    (ExecBlock.consNormal (morphoArrayCall evm _ imms (wordBytes32Value (lastUpdateSlot id))
      "slot" (.var "__c0") ?_) htail)
  · simp [evalExpr?, lastUpdateFrame, Std.HashMap.getElem_insert, EvalResult.ofOption,
      cursorName]
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption]

theorem lastUpdateBodySlotReverts (evm : State) (imms : Store) (morpho : AccountAddress)
    (id ptr : UInt256) (hfit : allocationFits ptr ⟨160⟩)
    (hbad : UInt256.size ≤ (solcMappingSlot ⟨3⟩ id).toNat + 2) :
    ExecFuncBody config (lastUpdateFrame imms morpho id ptr) evm
      allocatedLastUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (lastUpdateAllocationPrefix evm imms morpho id ptr hfit).run
  apply ExecBlock.consRevert (lastUpdateSlotCallReverts evm _ imms id "__c0" (.var "id") ?_ hbad)
  simp [evalExpr?, lastUpdateFrame, Std.HashMap.getElem_insert, EvalResult.ofOption, cursorName]

theorem lastUpdateCallArgs (evm : State) (imms : Store) (morpho : AccountAddress)
    (id ptr : UInt256) :
    evalExprs? config (lastUpdateCallFrame imms morpho id ptr) evm
      [.var "morpho", .var "slot", .var cursorName] =
      .ok [.address morpho, .array [wordBytes32Value (lastUpdateSlot id)],
        uint256Value (nextCursor ptr ⟨160⟩)] := by
  simp [evalExprs?, evalExpr?, lastUpdateCallFrame, lastUpdateAllocatedFrame, lastUpdateFrame,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure, cursorName]

theorem lastUpdateBodyCallReverts {evm : State} {imms : Store} {morpho : AccountAddress}
    {id ptr : UInt256} (hfit : allocationFits ptr ⟨160⟩)
    (hslot : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size)
    (hbody : ExecFuncBody config
      (extSloadsFrame (lastUpdateCallFrame imms morpho id ptr) (nextCursor ptr ⟨160⟩)
        morpho [wordBytes32Value (lastUpdateSlot id)]) evm extSloadsFunction.body .reverted) :
    ExecFuncBody config (lastUpdateFrame imms morpho id ptr) evm
      allocatedLastUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (lastUpdatePrefix evm imms morpho id ptr hfit hslot).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := extSloadsFunction)
    (lastUpdateCallArgs evm imms morpho id ptr) extSloadsFunction_lookup rfl hbody)

theorem lastUpdateBodyReturnPrefix {evm evm' : State} {imms : Store} {morpho : AccountAddress}
    {id ptr cursor : UInt256} {values : List Value} {calleeFrame : Frame}
    (hfit : allocationFits ptr ⟨160⟩)
    (hslot : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size)
    (hbody : ExecFuncBody config
      (extSloadsFrame (lastUpdateCallFrame imms morpho id ptr) (nextCursor ptr ⟨160⟩)
        morpho [wordBytes32Value (lastUpdateSlot id)]) evm extSloadsFunction.body
      (.returned calleeFrame evm' (some [.array values, uint256Value cursor])))
    {result : ExecResult}
    (htail : ExecBlock config (lastUpdateResultFrame imms morpho id ptr cursor values) evm'
      (allocatedLastUpdateFunction.body.drop 4) result) :
    ExecBlock config (lastUpdateFrame imms morpho id ptr) evm
      allocatedLastUpdateFunction.body result := by
  apply (lastUpdatePrefix evm imms morpho id ptr hfit hslot).run
  exact ExecBlock.consNormal (internalCallFunctionReturn (callee := extSloadsFunction)
    (lastUpdateCallArgs evm imms morpho id ptr) extSloadsFunction_lookup rfl hbody) htail

theorem lastUpdateBodyReturns {evm evm' : State} {imms : Store} {morpho : AccountAddress}
    {id ptr cursor value : UInt256} {values : List Value} {calleeFrame : Frame}
    (hfit : allocationFits ptr ⟨160⟩)
    (hslot : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size)
    (hbody : ExecFuncBody config
      (extSloadsFrame (lastUpdateCallFrame imms morpho id ptr) (nextCursor ptr ⟨160⟩)
        morpho [wordBytes32Value (lastUpdateSlot id)]) evm extSloadsFunction.body
      (.returned calleeFrame evm'
        (some [.array (wordBytes32Value value :: values), uint256Value cursor]))) :
    ExecFuncBody config (lastUpdateFrame imms morpho id ptr) evm allocatedLastUpdateFunction.body
      (.returned (lastUpdateResultFrame imms morpho id ptr cursor (wordBytes32Value value :: values))
        evm' (some [uint256Value (lastUpdateValue value), uint256Value cursor])) := by
  apply ExecFuncBody.execBlockRet
  apply lastUpdateBodyReturnPrefix hfit hslot hbody
  have hv : evalExpr? config
      (lastUpdateResultFrame imms morpho id ptr cursor (wordBytes32Value value :: values)) evm'
      (.cast (.index (.tupleGet (.var slotsAndCursorName) 0) (.intLit 0))
        (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (uint256Value value) := by
    apply evalExpr_bytes32ToUint
    apply evalExpr_arrayHead (value := wordBytes32Value value) (values := values)
    simp only [evalExpr?, lastUpdateResultFrame, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind]
    rfl
  have hc := uintCastNatSource ⟨128, by decide⟩ hv
  rw [← lastUpdateValue_toNat] at hc
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, hc, bind, EvalResult.bind, pure]
  simp only [evalExpr?, lastUpdateResultFrame, store_get_self,
    EvalResult.ofOption]
  rfl

theorem lastUpdateBodyEmpty {evm evm' : State} {imms : Store} {morpho : AccountAddress}
    {id ptr cursor : UInt256} {calleeFrame : Frame} (hfit : allocationFits ptr ⟨160⟩)
    (hslot : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size)
    (hbody : ExecFuncBody config
      (extSloadsFrame (lastUpdateCallFrame imms morpho id ptr) (nextCursor ptr ⟨160⟩)
        morpho [wordBytes32Value (lastUpdateSlot id)]) evm extSloadsFunction.body
      (.returned calleeFrame evm' (some [.array [], uint256Value cursor]))) :
    ExecFuncBody config (lastUpdateFrame imms morpho id ptr) evm
      allocatedLastUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply lastUpdateBodyReturnPrefix hfit hslot hbody
  apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
  simp only [evalExprs?, evalExpr?, lastUpdateResultFrame,
    store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure, evalIndex?]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
