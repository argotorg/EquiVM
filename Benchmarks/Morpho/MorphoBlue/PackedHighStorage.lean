import Benchmarks.Morpho.MorphoBlue.PackedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: shifting a canonical half-word does not discard any bits.
theorem shiftLeft128_toNat (value : UInt256) (hc : value.toNat < 2 ^ 128) :
    (UInt256.shiftLeft value (UInt256.ofNat 128)).toNat = value.toNat * 2 ^ 128 := by
  have hp : value.toNat * 2 ^ 128 < UInt256.size := by
    change value.toNat * 2 ^ 128 < 2 ^ 256
    omega
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (UInt256.ofNat 128).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftLeft_val, show (UInt256.ofNat 128).val.val = 128 from rfl, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt hp

def setUint128HighWord (old value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old uint128Mask) (UInt256.shiftLeft value (UInt256.ofNat 128))

-- LIBRARY CANDIDATE: storing the upper uint128 preserves the lower half.
theorem storageLocStore_uint128High (evm : EVM.State) (slot value : UInt256)
    (hc : value.toNat < 2 ^ 128) :
    storageLocStore evm (uint128HalfLoc slot true) (.int (Int.ofNat value.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint128HighWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  unfold storageLocStore storageLocWriteWord uint128HalfLoc
  simp only [↓reduceIte, valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 16 ++
    (EVM.Word.toBytesLEWithSizeProof value).1.take 16 ++
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 32) = _
  rw [List.drop_eq_nil_of_le (by rw [(EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]), List.append_nil,
    fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_take_wordLE]
  simp only [setUint128HighWord, u256_lor_toNat_exact, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
  rw [show 256 ^ 16 = (2 : Nat) ^ 128 from rfl, Nat.mod_eq_of_lt hc]
  rw [shiftLeft128_toNat value hc, uland_toNat]
  change _ % 2 ^ 128 + 2 ^ 128 * value.toNat = Nat.lor (Nat.land _ (2 ^ 128 - 1)) (value.toNat * 2 ^ 128)
  rw [nat_land_mask_eq_mod, nat_lor_shift_add _ value.toNat 128 (Nat.mod_lt _ (by decide)), Nat.mul_comm]

end Benchmarks.Morpho.MorphoBlue
