import Benchmarks.Midnight.SettlementFields
import Benchmarks.Midnight.PositionUpdateStorage

/-! The market's packed total units, withdrawable balance, and continuous-fee credit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketBalanceName (i : Fin 3) : Ident :=
  ["totalUnits", "withdrawable", "continuousFeeCredit"][i.val]'i.isLt

def marketBalanceSlot (id : UInt256) (i : Fin 3) : UInt256 :=
  if i.val = 0 then solcMappingSlot ⟨1⟩ id else solcMappingSlot ⟨1⟩ id + ⟨1⟩

def marketBalanceLoc (id : UInt256) (i : Fin 3) : StorageLoc := {
  slot := marketBalanceSlot id i
  offset := if i.val = 2 then 16 else 0
  size := 16
  hbound := by split <;> decide
  type := .int packedUInt128Int }

def marketBalanceWord (evm : EVM.State) (id : UInt256) (i : Fin 3) : UInt256 :=
  let w := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (marketBalanceSlot id i)
  if i.val = 2 then UInt256.shiftRight w (UInt256.ofNat 128) else low128 w

def marketBalanceStore (evm : EVM.State) (id : UInt256) (i : Fin 3) (value : UInt256) : EVM.State :=
  if i.val = 2 then storeHigh128 evm (marketBalanceSlot id i) value
  else storeLow128 evm (marketBalanceSlot id i) value

theorem marketBalanceWord_lt (evm : EVM.State) (id : UInt256) (i : Fin 3) :
    (marketBalanceWord evm id i).toNat < 2^128 := by
  unfold marketBalanceWord
  split
  · exact shiftRight128_lt _
  · exact low128_lt _

theorem marketBalance_type (i : Fin 3) :
    storageTypeStep? marketStateType (.field (marketBalanceName i)) =
      some (.elem (.int packedUInt128Int)) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> rfl

theorem marketBalance_layout (id : UInt256) (i : Fin 3) :
    midnightStorageLayout { (marketStateRef id) with steps :=
      (marketStateRef id).steps ++ [.field (marketBalanceName i)] } =
      some (.leaf (marketBalanceLoc id i)) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    change some (StorageAddr.leaf {
      slot := _, offset := _, size := 16, hbound := _, type := .int packedUInt128Int }) = _ <;>
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32] <;>
    simp [marketBalanceLoc, marketBalanceSlot, solcMappingSlot]

theorem marketBalance_load (evm : EVM.State) (id : UInt256) (i : Fin 3) :
    storageLocLoad evm (marketBalanceLoc id i) = .int (marketBalanceWord evm id i).toNat := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> dsimp only [marketBalanceLoc, marketBalanceWord, marketBalanceSlot] <;>
    norm_num only
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  · exact storageLocLoad_uint128_high evm _

theorem marketBalance_store (evm : EVM.State) (id : UInt256) (i : Fin 3) (value : UInt256) :
    storageLocStore evm (marketBalanceLoc id i) (.int value.toNat) =
      some (marketBalanceStore evm id i value) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> dsimp only [marketBalanceLoc, marketBalanceStore, marketBalanceSlot] <;>
    norm_num only
  · exact storageLocStore_uint128_low_word ..
  · exact storageLocStore_uint128_low_word ..
  · exact storageLocStore_uint128_high_word ..

theorem evalMarketBalance {frame : Frame} {evm : EVM.State} {id : UInt256} (i : Fin 3)
    (hget : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType)) :
    evalExpr? config frame evm (.storage { base := "_marketState", steps :=
      [.field (marketBalanceName i)] }) = .ok (.int (marketBalanceWord evm id i).toNat) :=
  evalStorageAliasField hget (marketBalance_type i) rfl
    (marketBalance_layout id i) (marketBalance_load evm id i)

theorem assignMarketBalance {frame : Frame} {evm : EVM.State} {id : UInt256}
    (i : Fin 3) (value : UInt256)
    (hget : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType)) :
    assignStorageRef? config frame evm .storage { base := "_marketState", steps :=
      [.field (marketBalanceName i)] } (.int value.toNat) =
      .ok (frame, marketBalanceStore evm id i value) :=
  assignStorageAliasField hget (marketBalance_type i) rfl
    (marketBalance_layout id i) (marketBalance_store evm id i value)

end Benchmarks.Midnight
