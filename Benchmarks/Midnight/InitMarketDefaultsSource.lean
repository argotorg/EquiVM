import Benchmarks.Midnight.InitMarketFeeMemory
import Benchmarks.Midnight.TouchMarketSourceBase

/-! Reading the default fee array as one source value before any of its elements are written. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def initDefaultFeesRef (token : AccountAddress) : EvaledStorageRef :=
  { base := "defaultSettlementFeeCbp", steps := [.mindex (.address token)] }

def initDefaultFeeWord (evm : EVM.State) (token : AccountAddress) : UInt256 :=
  Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨4⟩ (UInt256.ofNat token.val))

def settlementFeesValue (word : UInt256) : Value :=
  .array ((initMarketSettlementFeeWords word).map (fun w ↦ .int w.toNat))

theorem initDefaultFeeLayout (token : AccountAddress) (i : Nat) (hi : i < 7) :
    midnightStorageLayout { (initDefaultFeesRef token) with steps :=
      (initDefaultFeesRef token).steps ++ [.aindex (.int i)] } =
      some (.leaf (uint16Loc (solcMappingSlot ⟨4⟩ (UInt256.ofNat token.val)) ⟨i, by omega⟩)) := by
  have hk : keyValueToWord (.int (i : Int)) = UInt256.ofNat i := by
    exact keyValueToWord_int_ofNat_of_lt (lt_trans hi (by decide))
  simp only [initDefaultFeesRef, List.cons_append, List.nil_append, midnightStorageLayout,
    hk, keyValueToWord_address, UInt256.toNat_ofNat_of_lt (lt_trans hi (by decide)),
    Nat.div_eq_of_lt (show i < 16 by omega), Nat.mod_eq_of_lt (show i < 16 by omega)]
  change some (StorageAddr.leaf {
    slot := solcMappingSlot ⟨4⟩ (UInt256.ofNat token.val) + ⟨0⟩,
    offset := Fin.ofNat 32 (i * 2), size := 2, hbound := _, type := .int packedUInt16Int }) = _
  rw [u256_add_zero]
  congr 3
  apply Fin.ext
  change i * 2 % 32 = 2 * i
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem initDefaultFeeRead (evm : EVM.State) (token : AccountAddress) (i : Nat) (hi : i < 7) :
    solidityReadStorage? midnightStorageLayout evm { (initDefaultFeesRef token) with steps :=
      (initDefaultFeesRef token).steps ++ [.aindex (.int i)] } (.elem (.int packedUInt16Int)) =
      .ok (.int (settlementFeeWord (initDefaultFeeWord evm token) i).toNat) := by
  rw [solidityReadStorage?, solidityLeafLoc?_of_leaf (initDefaultFeeLayout token i hi)]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  dsimp only [uint16Loc, packedUInt16Int]
  rw [storageLocLoad_uint_offset evm _ ⟨2 * i, by omega⟩ 2 ⟨16, by decide⟩
    (by decide) (by omega) (by decide), div_byteOffset_eq_shiftRight]
  change EvalResult.ok (Value.int (UInt256.land (UInt256.shiftRight _
    (UInt256.ofNat (8 * (2 * i)))) _).toNat) = _
  rw [show 8 * (2 * i) = 16 * i by omega]
  rfl

theorem initDefaultFeesRead (evm : EVM.State) (token : AccountAddress) :
    solidityReadStorage? midnightStorageLayout evm (initDefaultFeesRef token)
      (.array (.elem (.int packedUInt16Int)) 7) =
      .ok (settlementFeesValue (initDefaultFeeWord evm token)) := by
  rw [solidityReadStorage?]
  simp only [solidityReadArray?, initDefaultFeeRead evm token 0 (by decide),
    initDefaultFeeRead evm token 1 (by decide), initDefaultFeeRead evm token 2 (by decide),
    initDefaultFeeRead evm token 3 (by decide), initDefaultFeeRead evm token 4 (by decide),
    initDefaultFeeRead evm token 5 (by decide), initDefaultFeeRead evm token 6 (by decide),
    EvalResult.bind, bind, pure]
  rfl

theorem evalMarketLoanToken {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.field (.var "market") "loanToken") = .ok (.address m.loanToken) := by
  simp only [evalExpr?, hm, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem evalInitDefaultFees {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hc : frame.contract = contract) (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbase : frame.locals.get? "defaultSettlementFeeCbp" = none) :
    evalExpr? config frame evm (.storage { base := "defaultSettlementFeeCbp", steps :=
      [.mindex (.field (.var "market") "loanToken")] }) =
      .ok (settlementFeesValue (initDefaultFeeWord evm m.loanToken)) := by
  have her : evalStorageRef config frame evm { base := "defaultSettlementFeeCbp", steps :=
      [.mindex (.field (.var "market") "loanToken")] } = .ok (initDefaultFeesRef m.loanToken) := by
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalMarketLoanToken hm,
      EvalResult.ofOption, EvalResult.bind, bind, pure, valueToKey?]
    rfl
  have hty : storageTypeAt? frame.contract.storage (initDefaultFeesRef m.loanToken) =
      some (.array (.elem (.int packedUInt16Int)) 7) := by rw [hc]; rfl
  rw [evalExpr?]
  simp only [resolveStorageRef?_ok hbase her hty, EvalResult.bind, bind]
  exact initDefaultFeesRead evm m.loanToken

theorem evalSettlementFeeIndex {frame : Frame} {evm : EVM.State} {word : UInt256}
    (hget : frame.locals.get? "_defaultSettlementFeeCbp" = some (settlementFeesValue word))
    (i : Fin 7) :
    evalExpr? config frame evm (.index (.var "_defaultSettlementFeeCbp") (.intLit i.val)) =
      .ok (.int (settlementFeeWord word i.val).toNat) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    simp only [evalExpr?, hget, settlementFeesValue, initMarketSettlementFeeWords, List.map_cons,
      List.map_nil, EvalResult.ofOption, EvalResult.bind, bind, pure, evalIndex?, lookupNth?,
      normalizeRawBoolWord?] <;> simp [lookupNth?, normalizeRawBoolWord?]

end Benchmarks.Midnight
