import Benchmarks.Midnight.HealthStorage
import Benchmarks.Midnight.PositionUpdateStorage

/-! The upper uint128 bitmap field of a position. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def positionBitmapWord (evm : EVM.State) (id user : UInt256) : UInt256 :=
  UInt256.shiftRight (healthPositionWord evm id user) (UInt256.ofNat 128)

theorem positionBitmapWord_lt (evm : EVM.State) (id user : UInt256) :
    (positionBitmapWord evm id user).toNat < 2^128 := by
  rw [positionBitmapWord, shiftRight_toNat _ _ (by decide)]
  have h := (healthPositionWord evm id user).val.isLt
  change (healthPositionWord evm id user).toNat < 2^256 at h
  change (healthPositionWord evm id user).toNat / 2^128 < 2^128
  omega

theorem assignPositionBitmap {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (value : UInt256) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)) :
    assignStorageRef? config frame evm .storage
      { base := "_position", steps := [.field "collateralBitmap"] } (.int value.toNat) =
      .ok (frame, storeHigh128 evm (positionSlot id user + ⟨2⟩) value) := by
  apply assignStorageAliasField (loc := uint128HighLoc (positionSlot id user + ⟨2⟩)) hget rfl rfl
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot
        (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
        (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨2⟩,
      offset := 16, size := 16, hbound := _, type := .int packedUInt128Int }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
      keyValueToWord_address_of_canonical user hcanon]
    rfl
  · exact storageLocStore_uint128_high_word evm _ value

end Benchmarks.Midnight
