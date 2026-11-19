import Benchmarks.Midnight.HealthStorage
import Benchmarks.Midnight.MarketBalanceFields

/-! Direct debt and market-balance storage references used by repayment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def repayDebtRef : StorageRef := { base := "position", steps :=
  [.mindex (.var "id"), .mindex (.var "onBehalf"), .field "debt"] }

def repayDebtEvaledRef (id user : UInt256) : EvaledStorageRef :=
  { (positionRef id user) with steps := (positionRef id user).steps ++ [.field "debt"] }

def repayDebtLoc (id user : UInt256) : StorageLoc := {
  slot := positionSlot id user + ⟨2⟩, offset := 0, size := 16, hbound := by decide,
  type := .int packedUInt128Int }

theorem resolveRepayDebt {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hu : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat))) :
    resolveStorageRef? config frame evm repayDebtRef =
      .ok (repayDebtEvaledRef id user, .elem (.int packedUInt128Int)) := by
  apply resolveStorageRef?_ok hbase
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [repayDebtRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, hid, hu, EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value,
      pure, bind, hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
    rfl
  · rw [hc]; rfl

theorem repayDebt_layout (id user : UInt256) (hcanon : user.toNat < EVM.addressModulus) :
    midnightStorageLayout (repayDebtEvaledRef id user) = some (.leaf (repayDebtLoc id user)) := by
  change some (StorageAddr.leaf {
    slot := solcMappingSlot
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
      (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨2⟩,
    offset := 0, size := 16, hbound := _, type := .int packedUInt128Int }) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
    keyValueToWord_address_of_canonical user hcanon]
  rfl

theorem evalRepayDebt {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hu : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat)))
    (hcanon : user.toNat < EVM.addressModulus) :
    evalExpr? config frame evm (.storage repayDebtRef) =
      .ok (.int (low128 (healthPositionWord evm id user)).toNat) := by
  rw [evalExpr?]
  simp only [resolveRepayDebt hc hbase hid hu, bind, EvalResult.bind,
    readStorage?_elem (cfg := config) (layout := midnightStorageLayout) rfl
      (repayDebt_layout id user hcanon)]
  congr 2
  exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)

theorem assignRepayDebt {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (value : UInt256) (hc : frame.contract = contract)
    (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hu : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat)))
    (hcanon : user.toNat < EVM.addressModulus) :
    assignStorageRef? config frame evm .storage repayDebtRef (.int value.toNat) =
      .ok (frame, storeLow128 evm (positionSlot id user + ⟨2⟩) value) := by
  have hb : config.storageBackend = solidityStorageBackend midnightStorageLayout := rfl
  have hs : storageLocStore evm (repayDebtLoc id user) (.int value.toNat) =
      some (storeLow128 evm (positionSlot id user + ⟨2⟩) value) :=
    storageLocStore_uint128_low_word ..
  simp only [assignStorageRef?, resolveRepayDebt hc hbase hid hu, hb, solidityStorageBackend,
    solidityWriteStorage?, solidityLeafLoc?_of_leaf (repayDebt_layout id user hcanon), hs,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

def directMarketBalanceRef (i : Fin 3) : StorageRef := { base := "marketState", steps :=
  [.mindex (.var "id"), .field (marketBalanceName i)] }

theorem resolveDirectMarketBalance {frame : Frame} {evm : EVM.State} {id : UInt256} (i : Fin 3)
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    resolveStorageRef? config frame evm (directMarketBalanceRef i) =
      .ok ({ (marketStateRef id) with steps := (marketStateRef id).steps ++
        [.field (marketBalanceName i)] }, .elem (.int packedUInt128Int)) := by
  apply resolveStorageRef?_ok hbase
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [directMarketBalanceRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, hid, EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value,
      pure, bind, hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
    rfl
  · rw [hc]
    rcases i with ⟨i, hi⟩
    interval_cases i <;> rfl

theorem evalDirectMarketBalance {frame : Frame} {evm : EVM.State} {id : UInt256} (i : Fin 3)
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm (.storage (directMarketBalanceRef i)) =
      .ok (.int (marketBalanceWord evm id i).toNat) := by
  rw [evalExpr?]
  simp only [resolveDirectMarketBalance i hc hbase hid, bind, EvalResult.bind,
    readStorage?_elem (cfg := config) (layout := midnightStorageLayout) rfl
      (marketBalance_layout id i), marketBalance_load]

theorem assignDirectMarketBalance {frame : Frame} {evm : EVM.State} {id : UInt256}
    (i : Fin 3) (value : UInt256) (hc : frame.contract = contract)
    (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    assignStorageRef? config frame evm .storage (directMarketBalanceRef i) (.int value.toNat) =
      .ok (frame, marketBalanceStore evm id i value) := by
  have hb : config.storageBackend = solidityStorageBackend midnightStorageLayout := rfl
  simp only [assignStorageRef?, resolveDirectMarketBalance i hc hbase hid, hb,
    solidityStorageBackend, solidityWriteStorage?,
    solidityLeafLoc?_of_leaf (marketBalance_layout id i), marketBalance_store,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
