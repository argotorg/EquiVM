import Benchmarks.UniswapV3.Pool.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

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

-- GENERALIZES the fixed-count SHL lemmas in Reasoning.EVMWord and WordArithmetic.
theorem shiftLeft_toNat_of_noOverflow (word bits : UInt256) (hbits : bits.toNat < 256)
    (hfit : word.toNat * 2 ^ bits.toNat < UInt256.size) :
    (UInt256.shiftLeft word bits).toNat = word.toNat * 2 ^ bits.toNat := by
  unfold UInt256.shiftLeft
  rw [if_neg (show ¬ bits.val ≥ 256 by exact Nat.not_le.mpr hbits)]
  change (word.toNat <<< bits.toNat) % UInt256.size = _
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hfit]

-- LIBRARY CANDIDATE: shifting a clean masked word preserves the shifted mask.
theorem shiftLeft_land_mask (word : UInt256) (width bits : Nat)
    (hbits : bits < 256) (hwidth : width + bits < 256) (hword : word.toNat < 2 ^ width) :
    UInt256.land (UInt256.shiftLeft word (UInt256.ofNat bits))
      (UInt256.ofNat ((2 ^ width - 1) * 2 ^ bits)) =
      UInt256.shiftLeft word (UInt256.ofNat bits) := by
  have hb : (UInt256.ofNat bits).toNat = bits := ulit_toNat' bits (by change bits < 2 ^ 256; omega)
  have hfit : word.toNat * 2 ^ bits < UInt256.size := by
    apply lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hword (by positivity))
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hwidth)
  have hmaskfit : (2 ^ width - 1) * 2 ^ bits < UInt256.size := by
    apply lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by positivity) (by decide))
      (by positivity))
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hwidth)
  apply u256_inj
  rw [uland_toNat, shiftLeft_toNat_of_noOverflow word _ (by rw [hb]; exact hbits)
    (by rw [hb]; exact hfit), hb, ulit_toNat' _ hmaskfit]
  simp only [← Nat.shiftLeft_eq]
  rw [← Nat.shiftLeft_and_distrib]
  change Nat.land word.toNat (2 ^ width - 1) <<< bits = _
  rw [nat_land_mask_eq_mod, Nat.mod_eq_of_lt hword]

end Benchmarks.UniswapV3.Pool
