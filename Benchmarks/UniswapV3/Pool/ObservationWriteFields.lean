import Benchmarks.UniswapV3.Pool.OracleObservationStorage
import Benchmarks.UniswapV3.Pool.PackedFieldWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

inductive ObservationWriteField where
  | timestamp
  | cumulative
  | secondsPerLiquidity
  | initialized

def ObservationWriteField.name : ObservationWriteField → Ident
  | .timestamp => "blockTimestamp"
  | .cumulative => "tickCumulative"
  | .secondsPerLiquidity => "secondsPerLiquidityCumulativeX128"
  | .initialized => "initialized"

def ObservationWriteField.loc (index : UInt256) : ObservationWriteField → StorageLoc
  | .timestamp =>
    {slot := observationSlot index, offset := 0, size := 4,
      type := .int (.uint ⟨32, by decide⟩), hbound := by decide}
  | .cumulative =>
    {slot := observationSlot index, offset := 4, size := 7,
      type := .int (.sint ⟨56, by decide⟩), hbound := by decide}
  | .secondsPerLiquidity =>
    {slot := observationSlot index, offset := 11, size := 20,
      type := .int (.uint ⟨160, by decide⟩), hbound := by decide}
  | .initialized =>
    {slot := observationSlot index, offset := 31, size := 1,
      type := .bool, hbound := by decide}

def ObservationWriteField.bits : ObservationWriteField → Nat × Nat
  | .timestamp => (0, 32)
  | .cumulative => (32, 56)
  | .secondsPerLiquidity => (88, 160)
  | .initialized => (248, 8)

def ObservationWriteField.value (obs : OracleObservation) : ObservationWriteField → Value
  | .timestamp => .int (Int.ofNat obs.timestamp.toNat)
  | .cumulative => .int obs.tickCumulative
  | .secondsPerLiquidity => .int (Int.ofNat obs.secondsPerLiquidity.toNat)
  | .initialized => .bool obs.initialized

def ObservationWriteField.word (obs : OracleObservation) : ObservationWriteField → UInt256
  | .timestamp => obs.timestamp
  | .cumulative => EVM.wordOfInt obs.tickCumulative
  | .secondsPerLiquidity => obs.secondsPerLiquidity
  | .initialized => obs.initialized.toUInt256

theorem ObservationWriteField.wordValue (obs : OracleObservation) (field : ObservationWriteField) :
    valueToWord (field.value obs) = some (field.word obs) := by
  cases field <;> simp only [ObservationWriteField.value, ObservationWriteField.word, valueToWord,
    wordOfInt_ofNat_toNat, pure]

theorem observationWriteLocate (index : UInt256) (field : ObservationWriteField) :
    storageBackend.locate?
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat)), .field field.name]⟩ =
      some (.leaf (field.loc index)) := by
  cases field
  · change some (StorageAddr.leaf {
      slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1)
      offset := 0, size := 4, type := .int (.uint ⟨32, by decide⟩), hbound := by decide}) = _
    simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, ObservationWriteField.loc,
      observationSlot, show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm]
  · change some (StorageAddr.leaf {
      slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1)
      offset := 4, size := 7, type := .int (.sint ⟨56, by decide⟩), hbound := by decide}) = _
    simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, ObservationWriteField.loc,
      observationSlot, show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm]
  · change some (StorageAddr.leaf {
      slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1)
      offset := 11, size := 20, type := .int (.uint ⟨160, by decide⟩), hbound := by decide}) = _
    simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, ObservationWriteField.loc,
      observationSlot, show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm]
  · change some (StorageAddr.leaf {
      slot := (⟨8⟩ : UInt256) + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 1)
      offset := 31, size := 1, type := .bool, hbound := by decide}) = _
    simp only [keyValueToWord_uint256, Nat.div_one, u256_ofNat_toNat, ObservationWriteField.loc,
      observationSlot, show UInt256.ofNat 8 = (⟨8⟩ : UInt256) from rfl, u256_add_comm]

def observationFieldState (evm : EVM.State) (index : UInt256) (field : ObservationWriteField)
    (obs : OracleObservation) : EVM.State :=
  modifyStorageWord evm (observationSlot index)
    (fun old ↦ packedFieldUpdate old (field.word obs) field.bits.1 field.bits.2)

theorem observationWriteFieldStore (evm : EVM.State) (index : UInt256)
    (field : ObservationWriteField) (obs : OracleObservation) :
    storageLocStore evm (field.loc index) (field.value obs) =
      some (observationFieldState evm index field obs) := by
  have h := storageLocStore_packedValue evm (field.loc index) (field.value obs) (field.word obs)
    (field.wordValue obs) (by cases field <;> rfl)
  cases field <;> exact h

end Benchmarks.UniswapV3.Pool
