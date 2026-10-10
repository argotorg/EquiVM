import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! Source execution of the market-parameter reader with its compiled reservations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem allocatedMarketParamsFunction_body :
    allocatedMarketParamsFunction.body =
      [reserveBytes 160,
       .letDecl "morphoTarget" (some (.elem .address)) (.immutable "MORPHO"),
       .externalCall (.var "morphoTarget") "idToMarketParams" (.intLit 0) [.var "id"]
         "__c0" false,
       reserveBytes 320,
       .return [.var "__c0", .var cursorName]] := by
  change reserveBytes 160 ::
    allocationBody (fun _ ↦ none) (fun name ↦ if name == "idToMarketParams" then 320 else 0)
      [.letDecl "morphoTarget" (some (.elem .address)) (.immutable "MORPHO"),
       .externalCall (.var "morphoTarget") "idToMarketParams" (.intLit 0) [.var "id"]
         "__c0" false,
       .return [.var "__c0"]] = _
  simp [allocationBody, allocationStatement, returnValueExpr]

set_option maxRecDepth 2000 in
theorem allocatedMarketParamsFunction_lookup :
    lookupCallable? contract allocatedMarketParamsFunction.name =
      some allocatedMarketParamsFunction.toCallable := by
  rfl

def allocatedMarketParamsFrame (v : MetaMorphoV1_1Immutables) (id ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert cursorName (uint256Value ptr)).insert "id" (wordBytes32Value id)
    immutables := immStore v }

def allocatedMarketParamsReserveFrame (v : MetaMorphoV1_1Immutables) (id ptr : UInt256) : Frame :=
  { allocatedMarketParamsFrame v id ptr with
    locals := (allocatedMarketParamsFrame v id ptr).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨160⟩)) }

def allocatedMarketParamsCallFrame (v : MetaMorphoV1_1Immutables) (id ptr : UInt256) : Frame :=
  { allocatedMarketParamsReserveFrame v id ptr with
    locals := (allocatedMarketParamsReserveFrame v id ptr).locals.insert "morphoTarget"
      (.address v.MORPHO) }

def allocatedMarketParamsDecodedFrame (v : MetaMorphoV1_1Immutables) (id ptr : UInt256)
    (value : Value) : Frame :=
  { allocatedMarketParamsCallFrame v id ptr with
    locals := (allocatedMarketParamsCallFrame v id ptr).locals.insert "__c0" value }

def marketParamsFinalCursor (ptr : UInt256) : UInt256 :=
  nextCursor (nextCursor ptr ⟨160⟩) ⟨320⟩

def allocatedMarketParamsResultFrame (v : MetaMorphoV1_1Immutables) (id ptr : UInt256)
    (value : Value) : Frame :=
  { allocatedMarketParamsDecodedFrame v id ptr value with
    locals := (allocatedMarketParamsDecodedFrame v id ptr value).locals.insert cursorName
      (uint256Value (marketParamsFinalCursor ptr)) }

theorem allocatedMarketParamsFrame_cursor (v : MetaMorphoV1_1Immutables) (evm : State)
    (id ptr : UInt256) :
    evalExpr? config (allocatedMarketParamsFrame v id ptr) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, allocatedMarketParamsFrame,
    store_get_ne _ _ (by decide : ("id" == cursorName) = false),
    store_get_self, EvalResult.ofOption]

theorem allocatedMarketParamsPrefix (v : MetaMorphoV1_1Immutables) (evm : State)
    (id ptr : UInt256) (hfit : allocationFits ptr ⟨160⟩) :
    ABlock config evm (allocatedMarketParamsFrame v id ptr) allocatedMarketParamsFunction.body
      (allocatedMarketParamsCallFrame v id ptr) (allocatedMarketParamsFunction.body.drop 2) := by
  constructor
  intro result htail
  rw [allocatedMarketParamsFunction_body] at htail ⊢
  simp only [List.drop_succ_cons, List.drop_zero] at htail
  refine ExecBlock.consNormal (allocateCallReturns (cfg := config)
    (frame := allocatedMarketParamsFrame v id ptr) cursorName allocateFunction_lookup
    (allocatedMarketParamsFrame_cursor v evm id ptr)
    (by simp only [evalExpr?, pure]; rfl) hfit) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_MORPHO _ _ _ _ _)) htail

theorem allocatedMarketParamsCall_args (v : MetaMorphoV1_1Immutables) (evm : State)
    (id ptr : UInt256) :
    evalExprs? config (allocatedMarketParamsCallFrame v id ptr) evm [.var "id"] =
      .ok [wordBytes32Value id] := by
  apply evalExprs?_singleton
  simp only [evalExpr?, allocatedMarketParamsCallFrame, allocatedMarketParamsReserveFrame,
    allocatedMarketParamsFrame,
    store_get_ne _ _ (by decide : ("morphoTarget" == "id") = false),
    store_get_ne _ _ (by decide : (cursorName == "id") = false),
    store_get_self, EvalResult.ofOption]

theorem allocatedMarketParamsCall_target (v : MetaMorphoV1_1Immutables) (evm : State)
    (id ptr : UInt256) :
    evalExpr? config (allocatedMarketParamsCallFrame v id ptr) evm (.var "morphoTarget") =
      .ok (.address v.MORPHO) := by
  simp only [evalExpr?, allocatedMarketParamsCallFrame, store_get_self, EvalResult.ofOption]

theorem allocatedMarketParamsBodyPrefixReverts (v : MetaMorphoV1_1Immutables) (evm : State)
    (id ptr : UInt256) (hfit : ¬ allocationFits ptr ⟨160⟩) :
    ExecFuncBody config (allocatedMarketParamsFrame v id ptr) evm
      allocatedMarketParamsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (allocateCallReverts (cfg := config)
    (frame := allocatedMarketParamsFrame v id ptr) cursorName allocateFunction_lookup
    (allocatedMarketParamsFrame_cursor v evm id ptr)
    (by simp only [evalExpr?, pure]; rfl) hfit)

theorem allocatedMarketParamsBodyCallReverts (v : MetaMorphoV1_1Immutables)
    (evm evm' : State) (id ptr : UInt256) (out : ByteArray)
    (hfit : allocationFits ptr ⟨160⟩)
    (hcall : typedCallViaEVM config evm v.MORPHO "idToMarketParams" 0 [wordBytes32Value id]
      (false, evm', out) false) :
    ExecFuncBody config (allocatedMarketParamsFrame v id ptr) evm
      allocatedMarketParamsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (allocatedMarketParamsPrefix v evm id ptr hfit).run
  rw [allocatedMarketParamsFunction_body]
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0)
    (eth := .intLit 0)
    (allocatedMarketParamsCall_target v evm id ptr) (by simp only [evalExpr?, pure])
    (allocatedMarketParamsCall_args v evm id ptr)
    (by rw [show EVM.address (v.MORPHO : Nat) = v.MORPHO from
          evm_address_of_address_toNat v.MORPHO]
        exact hcall))

theorem allocatedMarketParamsBodyDecodeReverts (v : MetaMorphoV1_1Immutables)
    (evm evm' : State) (id ptr : UInt256) (out : ByteArray)
    (hfit : allocationFits ptr ⟨160⟩)
    (hcall : typedCallViaEVM config evm v.MORPHO "idToMarketParams" 0 [wordBytes32Value id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "idToMarketParams" out = none) :
    ExecFuncBody config (allocatedMarketParamsFrame v id ptr) evm
      allocatedMarketParamsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (allocatedMarketParamsPrefix v evm id ptr hfit).run
  rw [allocatedMarketParamsFunction_body]
  exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0)
    (eth := .intLit 0)
    (allocatedMarketParamsCall_target v evm id ptr) (by simp only [evalExpr?, pure])
    (allocatedMarketParamsCall_args v evm id ptr)
    (by rw [show EVM.address (v.MORPHO : Nat) = v.MORPHO from
          evm_address_of_address_toNat v.MORPHO]
        exact hcall) hdecode)

theorem allocatedMarketParamsDecodePrefix {v : MetaMorphoV1_1Immutables}
    {evm evm' : State} {id ptr : UInt256} {out : ByteArray} {value : Value}
    (hfit : allocationFits ptr ⟨160⟩)
    (hcall : typedCallViaEVM config evm v.MORPHO "idToMarketParams" 0 [wordBytes32Value id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "idToMarketParams" out = some [value])
    {result : ExecResult}
    (htail : ExecBlock config (allocatedMarketParamsDecodedFrame v id ptr value) evm'
      (allocatedMarketParamsFunction.body.drop 3) result) :
    ExecBlock config (allocatedMarketParamsFrame v id ptr) evm
      allocatedMarketParamsFunction.body result := by
  apply (allocatedMarketParamsPrefix v evm id ptr hfit).run
  rw [allocatedMarketParamsFunction_body] at htail ⊢
  exact ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0)
    (eth := .intLit 0)
    (allocatedMarketParamsCall_target v evm id ptr) (by simp only [evalExpr?, pure])
    (allocatedMarketParamsCall_args v evm id ptr)
    (by rw [show EVM.address (v.MORPHO : Nat) = v.MORPHO from
          evm_address_of_address_toNat v.MORPHO]
        exact hcall) hdecode) htail

theorem allocatedMarketParamsDecodedFrame_cursor (v : MetaMorphoV1_1Immutables)
    (evm : State) (id ptr : UInt256) (value : Value) :
    evalExpr? config (allocatedMarketParamsDecodedFrame v id ptr value) evm (.var cursorName) =
      .ok (uint256Value (nextCursor ptr ⟨160⟩)) := by
  simp only [evalExpr?, allocatedMarketParamsDecodedFrame, allocatedMarketParamsCallFrame,
    allocatedMarketParamsReserveFrame,
    store_get_ne _ _ (by decide : ("__c0" == cursorName) = false),
    store_get_ne _ _ (by decide : ("morphoTarget" == cursorName) = false),
    store_get_self, EvalResult.ofOption]

theorem allocatedMarketParamsBodyAllocationReverts {v : MetaMorphoV1_1Immutables}
    {evm evm' : State} {id ptr : UInt256} {out : ByteArray} {value : Value}
    (hfit : allocationFits ptr ⟨160⟩)
    (hcall : typedCallViaEVM config evm v.MORPHO "idToMarketParams" 0 [wordBytes32Value id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "idToMarketParams" out = some [value])
    (hpost : ¬ allocationFits (nextCursor ptr ⟨160⟩) ⟨320⟩) :
    ExecFuncBody config (allocatedMarketParamsFrame v id ptr) evm
      allocatedMarketParamsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply allocatedMarketParamsDecodePrefix hfit hcall hdecode
  rw [allocatedMarketParamsFunction_body]
  exact ExecBlock.consRevert (allocateCallReverts (cfg := config)
    (frame := allocatedMarketParamsDecodedFrame v id ptr value) cursorName allocateFunction_lookup
    (allocatedMarketParamsDecodedFrame_cursor v evm' id ptr value)
    (by simp only [evalExpr?, pure]; rfl) hpost)

theorem allocatedMarketParamsBodyReturns {v : MetaMorphoV1_1Immutables}
    {evm evm' : State} {id ptr : UInt256} {out : ByteArray} {value : Value}
    (hfit : allocationFits ptr ⟨160⟩)
    (hcall : typedCallViaEVM config evm v.MORPHO "idToMarketParams" 0 [wordBytes32Value id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "idToMarketParams" out = some [value])
    (hpost : allocationFits (nextCursor ptr ⟨160⟩) ⟨320⟩) :
    ExecFuncBody config (allocatedMarketParamsFrame v id ptr) evm
      allocatedMarketParamsFunction.body
      (.returned (allocatedMarketParamsResultFrame v id ptr value) evm'
        (some [value, uint256Value (marketParamsFinalCursor ptr)])) := by
  apply ExecFuncBody.execBlockRet
  apply allocatedMarketParamsDecodePrefix hfit hcall hdecode
  rw [allocatedMarketParamsFunction_body]
  refine ExecBlock.consNormal (allocateCallReturns (cfg := config)
    (frame := allocatedMarketParamsDecodedFrame v id ptr value) cursorName allocateFunction_lookup
    (allocatedMarketParamsDecodedFrame_cursor v evm' id ptr value)
    (by simp only [evalExpr?, pure]; rfl) hpost) ?_
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?,
    store_get_ne _ _ (by decide : (cursorName == "__c0") = false),
    allocatedMarketParamsDecodedFrame, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure, marketParamsFinalCursor]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
