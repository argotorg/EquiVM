import Benchmarks.Midnight.MarketIdSource
import Benchmarks.Midnight.SettlementFields
import Reasoning.VyperDispatch

variable {fork : Ethereum.Fork}

/-! The touchMarket call frame, market-ID call, and initialized-market branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def touchMarketFunction : FunctionDecl := contract.functions[2]!

def touchMarketArguments (m : MarketData) : Store :=
  (∅ : Store).insert "market" (Model.marketValue m.value)

def touchMarketCallFrame (imms : Store) (m : MarketData) : Frame :=
  { contract := contract, locals := touchMarketArguments m, immutables := imms }

def touchMarketIdFrame (imms : Store) (m : MarketData) : Frame :=
  resumeAfterInternalCall (touchMarketCallFrame imms m) "id" (some [wordBytes32Value m.id])

def touchMarketInitBody : List Stmt :=
  match touchMarketFunction.body[1]! with
  | .ite _ body _ => body
  | _ => []

def marketTickRef : StorageRef :=
  { base := "marketState", steps := [.mindex (.var "id"), .field "tickSpacing"] }

def touchMarketCondition : Expr := .binary .eq (.storage marketTickRef) (.intLit 0)

theorem touchMarketBody_shape : touchMarketFunction.body =
    [.internalCall "IdLib_toId" [.var "market"] "id",
      .ite touchMarketCondition touchMarketInitBody [], .return [.var "id"]] := rfl

theorem evalMarketTick {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm (.storage marketTickRef) =
      .ok (.int (marketTickSpacing (marketFeeWord evm id)).toNat) := by
  apply evalExpr_storage_scalar_value (loc := {
      slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩, offset := 18, size := 1,
      hbound := by decide, type := .int (.uint ⟨8, by decide⟩) })
    (er := { base := "marketState", steps :=
      [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)), .field "tickSpacing"] })
    (t := .int (.uint ⟨8, by decide⟩)) hbase
  · have hlen := word_toBytesBE_length_32 id
    simp only [marketTickRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      hid, EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
  · rw [hc]; rfl
  · rfl
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩,
      offset := 18, size := 1, hbound := _, type := .int (.uint ⟨8, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint8_offset18 evm _

theorem touchMarketIdPrefix (evm : EVM.State) (imms : Store) (m : MarketData) :
    ABlock fork config evm (touchMarketCallFrame imms m) touchMarketFunction.body
      (touchMarketIdFrame imms m) (touchMarketFunction.body.drop 1) := by
  refine ⟨fun h ↦ ExecBlock.consNormal ?_ h⟩
  apply internalCallFunctionReturn (callee := marketIdFunction) (locals := touchMarketArguments m)
    (argVals := [Model.marketValue m.value])
  · simp only [evalExprs?, evalExpr?, touchMarketCallFrame, touchMarketArguments, store_get_self,
      EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact marketIdSourceReturns (store_get_self _ _ _)

theorem touchMarketCondition_eval (evm : EVM.State) (imms : Store) (m : MarketData) :
    evalExpr? config (touchMarketIdFrame imms m) evm touchMarketCondition =
      .ok (.bool (decide ((marketTickSpacing (marketFeeWord evm m.id)).toNat = 0))) := by
  have ht := evalMarketTick (frame := touchMarketIdFrame imms m) (evm := evm) rfl
    (by simp [touchMarketIdFrame, touchMarketCallFrame, touchMarketArguments,
      resumeAfterInternalCall, Std.HashMap.getElem_insert]) (store_get_self _ _ _)
  rw [touchMarketCondition, evalExpr_binary_nonshort (by decide) (by decide), ht]
  simp [evalExpr?, evalBinaryOp?, bind, pure, EvalResult.bind, Reasoning.VyperDispatch.value_int_beq]

theorem touchMarketExistingSource (evm : EVM.State) (imms : Store) (m : MarketData)
    (hinit : marketTickSpacing (marketFeeWord evm m.id) ≠ ⟨0⟩) :
    ExecFuncBody fork config (touchMarketCallFrame imms m) evm touchMarketFunction.body
      (.returned (touchMarketIdFrame imms m) evm (some [wordBytes32Value m.id])) := by
  apply ExecFuncBody.execBlockRet
  apply (touchMarketIdPrefix evm imms m).run
  have hn : (marketTickSpacing (marketFeeWord evm m.id)).toNat ≠ 0 :=
    fun h ↦ hinit (uint256_toNat_eq_zero h)
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
  · exact (touchMarketCondition_eval evm imms m).trans (by rw [decide_eq_false hn])
  exact returnInternalResult "id" (wordBytes32Value m.id)

end Benchmarks.Midnight
