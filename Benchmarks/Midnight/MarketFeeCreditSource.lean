import Benchmarks.Midnight.PositionUpdateStorage

/-! Reading and assigning the market's packed continuous-fee credit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def marketFeeCreditRef : StorageRef :=
  { base := "marketState", steps := [.mindex (.var "id"), .field "continuousFeeCredit"] }

def marketFeeCreditEvalRef (id : UInt256) : EvaledStorageRef :=
  { base := "marketState", steps :=
    [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)), .field "continuousFeeCredit"] }

theorem resolveMarketFeeCredit {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalStorageRef config frame evm marketFeeCreditRef = .ok (marketFeeCreditEvalRef id) := by
  have hlen : (EVM.Word.toBytesBE id).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size id
  simp only [marketFeeCreditRef, marketFeeCreditEvalRef, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, hid, EvalResult.bind, EvalResult.ofOption, valueToKey?,
    wordBytes32Value, pure, bind, hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]

theorem marketFeeCredit_layout (id : UInt256) :
    midnightStorageLayout (marketFeeCreditEvalRef id) =
      some (.leaf (uint128HighLoc (solcMappingSlot ⟨1⟩ id + ⟨1⟩))) := by
  change some (StorageAddr.leaf {
    slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨1⟩,
    offset := 16, size := 16, hbound := _, type := .int packedUInt128Int }) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  rfl

theorem evalMarketFeeCredit {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm (.storage marketFeeCreditRef) =
      .ok (.int (marketFeeCreditWord evm id).toNat) := by
  apply evalExpr_storage_scalar_value (loc := uint128HighLoc (solcMappingSlot ⟨1⟩ id + ⟨1⟩))
    (er := marketFeeCreditEvalRef id) (t := .int packedUInt128Int) hbase (resolveMarketFeeCredit hid)
  · rw [hc]; rfl
  · rfl
  · exact marketFeeCredit_layout id
  · exact storageLocLoad_uint128_high evm _

theorem assignMarketFeeCredit {frame : Frame} {evm : EVM.State} {id value : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    assignStorageRef? config frame evm .storage marketFeeCreditRef (.int value.toNat) =
      .ok (frame, storeHigh128 evm (solcMappingSlot ⟨1⟩ id + ⟨1⟩) value) := by
  apply assignStorageRef_storage_scalar_value (er := marketFeeCreditEvalRef id)
    (loc := uint128HighLoc (solcMappingSlot ⟨1⟩ id + ⟨1⟩))
    (ty := .elem (.int packedUInt128Int)) (layout := midnightStorageLayout)
    hbase (resolveMarketFeeCredit hid)
  · rw [hc]; rfl
  · rfl
  · exact marketFeeCredit_layout id
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint128_high_word evm _ _

end Benchmarks.Midnight
