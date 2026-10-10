import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketABI
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! Source execution through the first market call and its compiled reservations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem allocatedMarketBalancesFunction_prefix :
    allocatedMarketBalancesFunction.body =
      [.internalCall "MarketParamsLib_id" [.var "marketParams"] "id",
       .externalCall (.var "morpho") "market" (.intLit 0) [.var "id"] "market" false,
       reserveBytes 384] ++ allocatedMarketBalancesFunction.body.drop 3 := by
  let reserves := fun name ↦
    if name == "market" then 384 else if name == "borrowRateView" then 32 else 0
  have hsplit (tail : List Stmt) :
      allocationBody marketBalancesAllocationCalls reserves
        (.internalCall "MarketParamsLib_id" [.var "marketParams"] "id" ::
          .externalCall (.var "morpho") "market" (.intLit 0) [.var "id"] "market" false :: tail) =
        [.internalCall "MarketParamsLib_id" [.var "marketParams"] "id",
         .externalCall (.var "morpho") "market" (.intLit 0) [.var "id"] "market" false,
         reserveBytes 384] ++ allocationBody marketBalancesAllocationCalls reserves tail := by
    simp [allocationBody, allocationStatement, marketBalancesAllocationCalls, reserves]
  have hb := hsplit ((Syntax.contractSyntax.functions[55]!).body.drop 2)
  change allocatedMarketBalancesFunction.body = _ at hb
  rw [hb]
  rfl

set_option maxRecDepth 2000 in
theorem allocatedMarketBalancesFunction_lookup :
    lookupCallable? contract allocatedMarketBalancesFunction.name =
      some allocatedMarketBalancesFunction.toCallable := by
  rfl

def allocatedMarketBalancesFrame (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert cursorName (uint256Value ptr)).insert
      "marketParams" p.value).insert "morpho" (.address morpho)
    immutables := imms }

def allocatedMarketBalancesCallFrame (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) : Frame :=
  { allocatedMarketBalancesFrame imms morpho p ptr with
    locals := (allocatedMarketBalancesFrame imms morpho p ptr).locals.insert
      "id" (wordBytes32Value p.id) }

def allocatedMarketBalancesDecodedFrame (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (out : ByteArray) : Frame :=
  { allocatedMarketBalancesCallFrame imms morpho p ptr with
    locals := (allocatedMarketBalancesCallFrame imms morpho p ptr).locals.insert
      "market" (marketValue out) }

def allocatedMarketBalancesReserveFrame (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (out : ByteArray) : Frame :=
  { allocatedMarketBalancesDecodedFrame imms morpho p ptr out with
    locals := (allocatedMarketBalancesDecodedFrame imms morpho p ptr out).locals.insert
      cursorName (uint256Value (nextCursor ptr ⟨384⟩)) }

theorem allocatedMarketBalancesIdPrefix (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (evm : State) :
    ABlock config evm (allocatedMarketBalancesFrame imms morpho p ptr)
      allocatedMarketBalancesFunction.body (allocatedMarketBalancesCallFrame imms morpho p ptr)
      (allocatedMarketBalancesFunction.body.drop 1) := by
  constructor
  intro result htail
  rw [allocatedMarketBalancesFunction_prefix] at htail ⊢
  apply ExecBlock.consNormal _ htail
  apply marketParamsIdCall
  simp only [evalExpr?,
    store_get_ne _ _ (by decide : ("morpho" == "marketParams") = false),
    store_get_self, EvalResult.ofOption]

theorem allocatedMarketBalancesCall_args (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (evm : State) :
    evalExprs? config (allocatedMarketBalancesCallFrame imms morpho p ptr) evm [.var "id"] =
      .ok [wordBytes32Value p.id] := by
  apply evalExprs?_singleton
  simp only [evalExpr?, allocatedMarketBalancesCallFrame, store_get_self, EvalResult.ofOption]

theorem allocatedMarketBalancesCall_target (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (evm : State) :
    evalExpr? config (allocatedMarketBalancesCallFrame imms morpho p ptr) evm (.var "morpho") =
      .ok (.address morpho) := by
  simp only [evalExpr?, allocatedMarketBalancesCallFrame, allocatedMarketBalancesFrame,
    store_get_ne _ _ (by decide : ("id" == "morpho") = false), store_get_self, EvalResult.ofOption]

theorem allocatedMarketBalancesBodyCallReverts {imms : Store} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr : UInt256} {evm evm' : State} {out : ByteArray}
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value p.id]
      (false, evm', out) false) :
    ExecFuncBody config (allocatedMarketBalancesFrame imms morpho p ptr) evm
      allocatedMarketBalancesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (allocatedMarketBalancesIdPrefix imms morpho p ptr evm).run
  rw [allocatedMarketBalancesFunction_prefix]
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) (eth := .intLit 0)
    (allocatedMarketBalancesCall_target imms morpho p ptr evm)
    (by simp only [evalExpr?, pure]) (allocatedMarketBalancesCall_args imms morpho p ptr evm)
    (by rw [show EVM.address (morpho : Nat) = morpho from
          evm_address_of_address_toNat morpho]
        exact hcall))

theorem allocatedMarketBalancesBodyDecodeReverts {imms : Store} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr : UInt256} {evm evm' : State} {out : ByteArray}
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value p.id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "market" out = none) :
    ExecFuncBody config (allocatedMarketBalancesFrame imms morpho p ptr) evm
      allocatedMarketBalancesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (allocatedMarketBalancesIdPrefix imms morpho p ptr evm).run
  rw [allocatedMarketBalancesFunction_prefix]
  exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0)
    (eth := .intLit 0) (allocatedMarketBalancesCall_target imms morpho p ptr evm)
    (by simp only [evalExpr?, pure]) (allocatedMarketBalancesCall_args imms morpho p ptr evm)
    (by rw [show EVM.address (morpho : Nat) = morpho from
          evm_address_of_address_toNat morpho]
        exact hcall) hdecode)

theorem allocatedMarketBalancesDecodePrefix {imms : Store} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr : UInt256} {evm evm' : State} {out : ByteArray}
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value p.id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "market" out = some [marketValue out])
    {result : ExecResult}
    (htail : ExecBlock config (allocatedMarketBalancesDecodedFrame imms morpho p ptr out) evm'
      (allocatedMarketBalancesFunction.body.drop 2) result) :
    ExecBlock config (allocatedMarketBalancesFrame imms morpho p ptr) evm
      allocatedMarketBalancesFunction.body result := by
  apply (allocatedMarketBalancesIdPrefix imms morpho p ptr evm).run
  rw [allocatedMarketBalancesFunction_prefix] at htail ⊢
  exact ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) (eth := .intLit 0)
    (allocatedMarketBalancesCall_target imms morpho p ptr evm)
    (by simp only [evalExpr?, pure]) (allocatedMarketBalancesCall_args imms morpho p ptr evm)
    (by rw [show EVM.address (morpho : Nat) = morpho from
          evm_address_of_address_toNat morpho]
        exact hcall) hdecode) htail

theorem allocatedMarketBalancesDecodedFrame_cursor (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (out : ByteArray) (evm : State) :
    evalExpr? config (allocatedMarketBalancesDecodedFrame imms morpho p ptr out) evm
      (.var cursorName) = .ok (uint256Value ptr) := by
  simp only [evalExpr?, allocatedMarketBalancesDecodedFrame, allocatedMarketBalancesCallFrame,
    allocatedMarketBalancesFrame, store_get_ne _ _ (by decide : ("market" == cursorName) = false),
    store_get_ne _ _ (by decide : ("id" == cursorName) = false),
    store_get_ne _ _ (by decide : ("morpho" == cursorName) = false),
    store_get_ne _ _ (by decide : ("marketParams" == cursorName) = false),
    store_get_self, EvalResult.ofOption]

theorem allocatedMarketBalancesBodyAllocationReverts {imms : Store} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr : UInt256} {evm evm' : State} {out : ByteArray}
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value p.id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "market" out = some [marketValue out])
    (hfit : ¬ allocationFits ptr ⟨384⟩) :
    ExecFuncBody config (allocatedMarketBalancesFrame imms morpho p ptr) evm
      allocatedMarketBalancesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply allocatedMarketBalancesDecodePrefix hcall hdecode
  rw [allocatedMarketBalancesFunction_prefix]
  exact ExecBlock.consRevert (allocateCallReverts (cfg := config)
    (frame := allocatedMarketBalancesDecodedFrame imms morpho p ptr out) cursorName
    allocateFunction_lookup (allocatedMarketBalancesDecodedFrame_cursor imms morpho p ptr out evm')
    (by simp only [evalExpr?, pure]; rfl) hfit)

theorem allocatedMarketBalancesAllocationPrefix {imms : Store} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr : UInt256} {evm evm' : State} {out : ByteArray}
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value p.id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "market" out = some [marketValue out])
    (hfit : allocationFits ptr ⟨384⟩) {result : ExecResult}
    (htail : ExecBlock config (allocatedMarketBalancesReserveFrame imms morpho p ptr out) evm'
      (allocatedMarketBalancesFunction.body.drop 3) result) :
    ExecBlock config (allocatedMarketBalancesFrame imms morpho p ptr) evm
      allocatedMarketBalancesFunction.body result := by
  apply allocatedMarketBalancesDecodePrefix hcall hdecode
  rw [allocatedMarketBalancesFunction_prefix]
  exact ExecBlock.consNormal (allocateCallReturns (cfg := config)
    (frame := allocatedMarketBalancesDecodedFrame imms morpho p ptr out) cursorName
    allocateFunction_lookup (allocatedMarketBalancesDecodedFrame_cursor imms morpho p ptr out evm')
    (by simp only [evalExpr?, pure]; rfl) hfit) htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
