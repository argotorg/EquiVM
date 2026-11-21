import Benchmarks.Midnight.NamedPositionSource
import Benchmarks.Midnight.PositionUpdateStorage
import Benchmarks.Midnight.RepayBalanceStorage

/-! Position writes through arbitrary source-local aliases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES assignPositionAliasField to aliases such as buyerPos and sellerPos.
theorem assignNamedPositionField {frame : Frame} {evm : State} {id user : UInt256} {name : Ident}
    (i : Fin 4) (value : UInt256) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? name = some (.storageRef (positionRef id user) positionType)) :
    assignStorageRef? config frame evm .storage
      { base := name, steps := [.field (positionFieldName i)] } (.int value.toNat) =
      .ok (frame, positionFieldStore evm id user i value) :=
  assignStorageAliasField hget (positionField_type i) rfl
    (positionField_layout id user i hcanon) (positionField_store evm id user i value)

-- GENERALIZES assignHealthDebt to arbitrary local position aliases.
theorem assignNamedPositionDebt {frame : Frame} {evm : State} {id user : UInt256} {name : Ident}
    (value : UInt256) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? name = some (.storageRef (positionRef id user) positionType)) :
    assignStorageRef? config frame evm .storage
      { base := name, steps := [.field "debt"] } (.int value.toNat) =
      .ok (frame, storeLow128 evm (positionSlot id user + ⟨2⟩) value) := by
  apply assignStorageAliasField (name := name) (field := "debt")
    (loc := repayDebtLoc id user) (t := .int packedUInt128Int)
    (layout := midnightStorageLayout) hget rfl rfl (repayDebt_layout id user hcanon)
  simpa only [repayDebtLoc, uint128LowLoc, storeLow128] using
    storageLocStore_uint128_low_word evm (positionSlot id user + ⟨2⟩) value

end Benchmarks.Midnight
