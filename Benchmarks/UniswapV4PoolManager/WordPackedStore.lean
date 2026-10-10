import Benchmarks.UniswapV4PoolManager.ResolvedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: replacement of the low bits of a packed storage word.
def wordLowSet (old value : UInt256) (bits : Nat) : UInt256 :=
  UInt256.lor (UInt256.land (UInt256.ofNat (2^256-2^bits)) old) value

theorem wordLowSet_toNat (old value : UInt256) (bits : Nat) (hb : bits ≤ 256)
    (hv : value.toNat < 2^bits) :
    (wordLowSet old value bits).toNat = value.toNat + old.toNat / 2^bits * 2^bits := by
  rw [wordLowSet, u256_lor_toNat_exact, u256_land_high_mask_toNat old bits hb]
  change Nat.lor (old.toNat / 2^bits * 2^bits) value.toNat = _
  rw [nat_lor_comm, nat_lor_shift_add _ _ _ hv]

-- GENERALIZES storageLocStore_uint8 and storageLocStore_address_offset0 to any packed unsigned width.
theorem storageLocStore_uintOffset0 (evm : EVM.State) (slot value : UInt256)
    (size : Fin 33) (width : BitWidth) (hbound : (0 : Fin 32).val + size.val - 1 < 32)
    (hv : value.toNat < 2^(8*size.val)) :
    storageLocStore evm
      {slot := slot, offset := 0, size := size, hbound := hbound, type := .int (.uint width)}
      (.int (Int.ofNat value.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (wordLowSet (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value (8*size.val))) := by
  have hsize : size.val ≤ 32 := Nat.le_of_lt_succ size.isLt
  have hbits : 8*size.val ≤ 256 := by omega
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 0 ++
    (EVM.Word.toBytesLEWithSizeProof value).1.take size.val ++
    (EVM.Word.toBytesLEWithSizeProof (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop (0+size.val)) = _
  simp only [List.take_zero, List.nil_append, Nat.zero_add]
  rw [fromBytes'_append, fromBytes'_take_wordLE_land_mask value size.val hbits, fromBytes'_drop_wordLE]
  have hclean := u256LandMaskCleanOfToNat value (UInt256.ofNat (2^(8*size.val)-1))
    (UInt256.toNat_ofNat_of_lt (by
      have hp : 2^(8*size.val) ≤ (2^256 : Nat) := Nat.pow_le_pow_right (by decide) hbits
      have hn : 0 < (2:Nat)^(8*size.val) := Nat.pow_pos (by decide)
      change _ < 2^256; omega)) hv
  rw [hclean, wordLowSet_toNat _ _ _ hbits hv]
  simp only [List.length_take, (EVM.Word.toBytesLEWithSizeProof value).2, Nat.min_eq_left hsize]
  rw [show (256:Nat)^size.val = 2^(8*size.val) by rw [Nat.pow_mul]]
  ac_rfl

end Benchmarks.UniswapV4PoolManager
