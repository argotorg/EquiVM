import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlots
import Benchmarks.Morpho.MetaMorphoV1_1.MemoryArraySource

/-! Source body of the Morpho supply-share reader, parameterized by its external-call result. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def supplySharesFunction : FunctionDecl := contract.functions[16]!

def supplySharesFrame (imms : Store) (morpho user : AccountAddress) (id : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert "user" (.address user)).insert "id"
      (wordBytes32Value id)).insert "morpho" (.address morpho)
    immutables := imms }

def supplySharesCallFrame (imms : Store) (morpho user : AccountAddress) (id : UInt256) : Frame :=
  { supplySharesFrame imms morpho user id with
    locals := ((supplySharesFrame imms morpho user id).locals.insert "__c0"
      (wordBytes32Value (positionSupplySharesSlot id user))).insert "slot"
      (.array [wordBytes32Value (positionSupplySharesSlot id user)]) }

theorem supplySharesPrefix (evm : EVM.State) (imms : Store)
    (morpho user : AccountAddress) (id : UInt256) :
    ABlock config evm (supplySharesFrame imms morpho user id) supplySharesFunction.body
      (supplySharesCallFrame imms morpho user id) (supplySharesFunction.body.drop 2) := by
  constructor
  intro result htail
  refine ExecBlock.consNormal (positionSupplySharesSlotCall evm _ imms id user "__c0" _ _ ?_ ?_)
    (ExecBlock.consNormal (morphoArrayCall evm _ imms
      (wordBytes32Value (positionSupplySharesSlot id user)) "slot" _ ?_) htail)
  · simp only [evalExpr?,
      store_get_ne _ _ (show ("morpho" == "id") = false from by decide),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?,
      store_get_ne _ _ (show ("morpho" == "user") = false from by decide),
      store_get_ne _ _ (show ("id" == "user") = false from by decide),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption]

theorem supplySharesCallFrame_receiver (evm : EVM.State) (imms : Store)
    (morpho user : AccountAddress) (id : UInt256) :
    evalExpr? config (supplySharesCallFrame imms morpho user id) evm (.var "morpho") =
      .ok (.address morpho) := by
  simp only [evalExpr?, supplySharesCallFrame, supplySharesFrame,
    store_get_ne _ _ (show ("slot" == "morpho") = false from by decide),
    store_get_ne _ _ (show ("__c0" == "morpho") = false from by decide),
    store_get_self, EvalResult.ofOption]

theorem supplySharesCallFrame_args (evm : EVM.State) (imms : Store)
    (morpho user : AccountAddress) (id : UInt256) :
    evalExprs? config (supplySharesCallFrame imms morpho user id) evm [.var "slot"] =
      .ok [.array [wordBytes32Value (positionSupplySharesSlot id user)]] := by
  apply evalExprs?_singleton
  simp only [evalExpr?, supplySharesCallFrame, store_get_self, EvalResult.ofOption]

-- LIBRARY CANDIDATE: the source index-zero expression reads a nonempty array's first element.
theorem evalExpr_arrayHead {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {value : Value} {values : List Value}
    (heval : evalExpr? cfg frame evm expr = .ok (.array (value :: values))) :
    evalExpr? cfg frame evm (.index expr (.intLit 0)) = normalizeRawBoolWord? value := by
  simp only [evalExpr?, heval, bind, EvalResult.bind, pure, evalIndex?]
  rw [if_pos (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)]
  rfl

theorem supplySharesBody (evm evm' : EVM.State) (imms : Store)
    (morpho user : AccountAddress) (id value : UInt256) (values : List Value) (out : ByteArray)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0
      [.array [wordBytes32Value (positionSupplySharesSlot id user)]] (true, evm', out) false)
    (hdecode : config.externalABI.decode? "extSloads" out =
      some [.array (wordBytes32Value value :: values)]) :
    ExecFuncBody config (supplySharesFrame imms morpho user id) evm supplySharesFunction.body
      (.returned
        { supplySharesCallFrame imms morpho user id with
          locals := (supplySharesCallFrame imms morpho user id).locals.insert "__c2"
            (.array (wordBytes32Value value :: values)) } evm' (some [uint256Value value])) := by
  apply ExecFuncBody.execBlockRet
  apply (supplySharesPrefix evm imms morpho user id).run
  refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0)
    (supplySharesCallFrame_receiver evm imms morpho user id)
    (by simp only [evalExpr?, pure]) (supplySharesCallFrame_args evm imms morpho user id)
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]
        exact hcall) hdecode) ?_
  apply ABlock.start.returns
  apply evalExpr_bytes32ToUint
  apply evalExpr_arrayHead (value := wordBytes32Value value) (values := values)
  simp only [evalExpr?, store_get_self, collapseReturns, EvalResult.ofOption]

theorem supplySharesBodyCallFailure (evm evm' : EVM.State) (imms : Store)
    (morpho user : AccountAddress) (id : UInt256) (out : ByteArray)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0
      [.array [wordBytes32Value (positionSupplySharesSlot id user)]] (false, evm', out) false) :
    ExecFuncBody config (supplySharesFrame imms morpho user id) evm
      supplySharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (supplySharesPrefix evm imms morpho user id).run
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0)
    (supplySharesCallFrame_receiver evm imms morpho user id)
    (by simp only [evalExpr?, pure]) (supplySharesCallFrame_args evm imms morpho user id)
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]
        exact hcall))

theorem supplySharesBodyDecodeFailure (evm evm' : EVM.State) (imms : Store)
    (morpho user : AccountAddress) (id : UInt256) (out : ByteArray)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0
      [.array [wordBytes32Value (positionSupplySharesSlot id user)]] (true, evm', out) false)
    (hdecode : config.externalABI.decode? "extSloads" out = none) :
    ExecFuncBody config (supplySharesFrame imms morpho user id) evm
      supplySharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (supplySharesPrefix evm imms morpho user id).run
  exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0)
    (supplySharesCallFrame_receiver evm imms morpho user id)
    (by simp only [evalExpr?, pure]) (supplySharesCallFrame_args evm imms morpho user id)
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]
        exact hcall) hdecode)

theorem supplySharesBodyEmpty (evm evm' : EVM.State) (imms : Store)
    (morpho user : AccountAddress) (id : UInt256) (out : ByteArray)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0
      [.array [wordBytes32Value (positionSupplySharesSlot id user)]] (true, evm', out) false)
    (hdecode : config.externalABI.decode? "extSloads" out = some [.array []]) :
    ExecFuncBody config (supplySharesFrame imms morpho user id) evm
      supplySharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (supplySharesPrefix evm imms morpho user id).run
  refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0)
    (supplySharesCallFrame_receiver evm imms morpho user id)
    (by simp only [evalExpr?, pure]) (supplySharesCallFrame_args evm imms morpho user id)
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]
        exact hcall) hdecode) ?_
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  simp only [evalExprs?, evalExpr?, store_get_self, collapseReturns, EvalResult.ofOption,
    bind, EvalResult.bind, pure, evalIndex?]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
