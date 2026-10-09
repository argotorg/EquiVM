import Benchmarks.Safe.BytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: BYTE 0 is the big-endian value of the first encoded byte.
theorem byteAtZero_toNat (w : UInt256) :
    (UInt256.byteAt ⟨0⟩ w).toNat = fromByteArrayBigEndian (w.toByteArray.extract 0 1) := by
  have hs : (UInt256.shiftRight w ⟨248⟩).toNat = w.toNat / 2 ^ 248 := by
    unfold UInt256.shiftRight UInt256.toNat
    rw [if_neg (by decide)]
    change (w.val >>> (⟨248⟩ : UInt256).val).val = w.val.val / 2 ^ 248
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
    rfl
  have hl : w.toByteArray.data.toList.length = 32 := by
    simpa only [Array.length_toList] using toByteArray_size w
  have hd : w.toNat / 2 ^ 248 = fromByteArrayBigEndian (w.toByteArray.extract 0 1) := by
    rw [← fromByteArrayBigEndian_toByteArray w]
    simp only [fromByteArrayBigEndian, byteArray_toList_eq, ByteArray.data_extract,
      Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
    conv_lhs => rw [← List.take_append_drop 1 w.toByteArray.data.toList]
    rw [show 248 = 8 * (w.toByteArray.data.toList.drop 1).length by
      rw [List.length_drop, hl]]
    exact fromBytesBigEndian_append_div _ _
  have hb : fromByteArrayBigEndian (w.toByteArray.extract 0 1) < 256 := by
    have hh := fromByteArrayBigEndian_lt (w.toByteArray.extract 0 1)
    simpa only [ByteArray.size_extract, toByteArray_size,
      Nat.min_eq_left (by decide : 1 ≤ 32), Nat.sub_zero] using hh
  unfold UInt256.byteAt
  rw [if_neg (by decide)]
  change (UInt256.land (UInt256.shiftRight w ⟨248⟩) ⟨255⟩).toNat = _
  rw [uland_toNat, hs, hd]
  change Nat.land _ (2 ^ 8 - 1) = _
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt hb

-- LIBRARY CANDIDATE: read a byte from a length-prefixed bytes value using MLOAD/BYTE.
theorem BytesMemory.byte {mem bytes : ByteArray} {ptr off : Nat}
    (h : BytesMemory mem ptr bytes) (hin : off < bytes.size)
    (hb : ptr + 32 + off < UInt256.size) :
    UInt256.byteAt ⟨0⟩ (memLoad (UInt256.ofNat (ptr + 32 + off)) mem) =
      UInt256.ofNat (fromByteArrayBigEndian (bytes.extract off (off + 1))) := by
  have hfull : ptr + 32 + off + 32 ≤ mem.size := by have := h.available; omega
  have hread : (memLoad (UInt256.ofNat (ptr + 32 + off)) mem).toByteArray.extract 0 1 =
      bytes.extract off (off + 1) := by
    rw [memLoadReadWord, uInt256OfByteArray_eq, ulit_toNat' _ hb]
    rw [toByteArray_readWord_extract mem (ptr + 32 + off) 0 1 hfull (by decide) (by decide)]
    simpa only [Nat.add_zero, Nat.add_sub_cancel_left] using
      h.slice (start := off) (finish := off + 1) (by omega) (by omega)
  apply u256_inj
  rw [byteAtZero_toNat, hread, ulit_toNat' _]
  have hh := fromByteArrayBigEndian_lt (bytes.extract off (off + 1))
  have hs : (bytes.extract off (off + 1)).size = 1 := by rw [ByteArray.size_extract]; omega
  rw [hs] at hh
  exact lt_trans hh (by decide)

end Benchmarks.Safe
