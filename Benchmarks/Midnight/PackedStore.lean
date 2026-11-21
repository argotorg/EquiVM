import Benchmarks.Midnight.PackedWrites

/-! General packed-storage updates through their numeric word representation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

-- GENERALIZES the fixed-offset stores in Reasoning.Storage and Reasoning.PackedStorage.
theorem storageLocStore_packed_of_toNat (evm : EVM.State) (loc : StorageLoc)
    (value : Value) (valueWord result : UInt256)
    (hvalue : valueToWord value = some valueWord) (hbit : loc.bitOffset = none)
    (hresult : result.toNat =
      (EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot).toNat % 256 ^ loc.offset.val +
      256 ^ loc.offset.val * (valueWord.toNat % 256 ^ loc.size.val) +
      256 ^ (loc.offset.val + loc.size.val) *
        ((EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot).toNat /
          256 ^ (loc.offset.val + loc.size.val))) :
    storageLocStore evm loc value =
      some (EVM.storageStore evm evm.executionEnv.codeOwner loc.slot result) := by
  unfold storageLocStore storageLocWriteWord
  simp only [hvalue, hbit, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    (((EVM.Word.toBytesLEWithSizeProof
        (EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot)).1.take loc.offset.val ++
      (EVM.Word.toBytesLEWithSizeProof valueWord).1.take loc.size.val) ++
      (EVM.Word.toBytesLEWithSizeProof
        (EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot)).1.drop
          (loc.offset.val + loc.size.val)) = result.toNat
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, hresult]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot)).2,
    (EVM.Word.toBytesLEWithSizeProof valueWord).2,
    Nat.min_eq_left (show loc.offset.val ≤ 32 by omega),
    Nat.min_eq_left (show loc.size.val ≤ 32 by omega)]
  simp only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]

-- GENERALIZES Reasoning.EVMWord.natLorLowMiddleHigh112_224 to arbitrary widths.
theorem natLorThreeRegions (low middle high offset width : Nat)
    (hlow : low < 2 ^ offset) (hmiddle : middle < 2 ^ width) :
    (low ||| (high * 2 ^ (offset + width))) ||| (middle * 2 ^ offset) =
      low + middle * 2 ^ offset + high * 2 ^ (offset + width) := by
  rw [Nat.or_right_comm]
  change Nat.lor (Nat.lor low (middle * 2 ^ offset)) (high * 2 ^ (offset + width)) = _
  rw [nat_lor_shift_add low middle offset hlow]
  apply nat_lor_shift_add
  rw [Nat.pow_add]
  have hpos : 0 < 2 ^ offset := by positivity
  nlinarith

-- LIBRARY CANDIDATE: an EVM clear-mask and shifted field implement a packed storage update.
theorem packedMaskedWord_toNat (old clearMask field : UInt256) (offset width value : Nat)
    (hbound : offset + width ≤ 256)
    (hmask : clearMask.toNat = (2 ^ offset - 1) ||| (2 ^ 256 - 2 ^ (offset + width)))
    (hfield : field.toNat = value * 2 ^ offset) (hvalue : value < 2 ^ width) :
    (UInt256.lor (UInt256.land old clearMask) field).toNat =
      old.toNat % 2 ^ offset + value * 2 ^ offset +
        (old.toNat / 2 ^ (offset + width)) * 2 ^ (offset + width) := by
  rw [u256_lor_toNat_exact, uland_toNat, hmask, hfield, Nat.and_or_distrib_left]
  change (Nat.land old.toNat (2 ^ offset - 1) |||
    Nat.land old.toNat (2 ^ 256 - 2 ^ (offset + width))) ||| (value * 2 ^ offset) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat (offset + width) hbound old.val.isLt]
  exact natLorThreeRegions _ _ _ offset width (Nat.mod_lt _ (by positivity)) hvalue

end Benchmarks.Midnight
