import Benchmarks.UniswapV4PoolManager.BytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES readWithPadding_eq_extract_unbounded to include empty reads.
theorem readWithPadding_eq_extract_any (src : ByteArray) (off len : Nat)
    (hb : off+len ≤ src.size) :
    src.readWithPadding off len = src.extract off (off+len) := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero, Nat.add_zero, byteArray_extract_empty_of_le src (by omega)]
  · exact readWithPadding_eq_extract_unbounded src off len (by omega) hb

-- LIBRARY CANDIDATE: word rounding expressed using ABI's natural padded size.
def paddedWord (len : UInt256) : UInt256 := UInt256.land (len+⟨31⟩) (UInt256.lnot ⟨31⟩)

theorem paddedWord_toNat (len : UInt256) (hf : len.toNat+31 < UInt256.size) :
    (paddedWord len).toNat = paddedSize len.toNat := by
  rw [paddedWord, longDataCutoff_toNat]
  change (len+UInt256.ofNat 31).toNat / 32 * 32 = paddedSize len.toNat
  rw [uadd_word_ofNat_toNat len 31 hf]
  exact Nat.mul_comm _ _

-- LIBRARY CANDIDATE: appending a possibly empty slice with one zero word of padding.
def copyPadMemory (src base : ByteArray) (srcAddr len : Nat) : ByteArray :=
  writeWord (src.write srcAddr base base.size len) (base.size+len) ⟨0⟩

theorem copyAtEnd_eq (src base : ByteArray) (srcAddr len : Nat)
    (hs : srcAddr+len ≤ src.size) :
    src.write srcAddr base base.size len = base ++ src.extract srcAddr (srcAddr+len) := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_write_len_zero, Nat.add_zero, byteArray_extract_empty_of_le src (by omega),
      ByteArray.append_empty]
  · exact write_at_end_eq_from src base srcAddr len hz hs

theorem copyPadMemory_eq (src base : ByteArray) (srcAddr len : Nat)
    (hs : srcAddr+len ≤ src.size) :
    copyPadMemory src base srcAddr len =
      base ++ src.extract srcAddr (srcAddr+len) ++ (⟨0⟩ : UInt256).toByteArray := by
  have hsize : (src.write srcAddr base base.size len).size = base.size+len := by
    rw [copyAtEnd_eq _ _ _ _ hs, ByteArray.size_append, ByteArray.size_extract]; omega
  unfold copyPadMemory Reasoning.Theory.writeWord
  rw [← hsize, write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size]),
    toByteArray_extract_all, copyAtEnd_eq _ _ _ _ hs]

theorem copyPadMemory_size (src base : ByteArray) (srcAddr len : Nat)
    (hs : srcAddr+len ≤ src.size) :
    (copyPadMemory src base srcAddr len).size = base.size+len+32 := by
  rw [copyPadMemory_eq _ _ _ _ hs, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, toByteArray_size]; omega

theorem copyPadMemory_read (src base : ByteArray) (srcAddr len off head : Nat)
    (hbase : base.size = off+head) (hs : srcAddr+len ≤ src.size) :
    (copyPadMemory src base srcAddr len).readWithPadding off (head+paddedSize len) =
      base.readWithPadding off head ++
      (src.extract srcAddr (srcAddr+len) ++ ByteArray.zeroes (paddedSize len-len)) := by
  have hp := nat_le_paddedSize len
  have hp' := paddedSize_le_add31 len
  have hslice : (src.extract srcAddr (srcAddr+len)).size = len := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract_any _ _ _
    (by rw [copyPadMemory_size _ _ _ _ hs]; omega), copyPadMemory_eq _ _ _ _ hs,
    ByteArray.append_assoc, extract_append_span _ _ _ _ (by omega) (by omega)]
  rw [show off+(head+paddedSize len)-base.size = paddedSize len by omega]
  rw [extract_append_span _ _ _ _ (by omega) (by rw [hslice]; omega),
    byteArray_extract_self, hslice, zero_toByteArray_eq_zeroes32,
    zeroes32_extract_zeroes _ (by omega)]
  rw [hbase, readWithPadding_eq_extract_any base off head (by omega)]

theorem copyPadMemory_read_below (src base : ByteArray) (srcAddr len off size : Nat)
    (hs : srcAddr+len ≤ src.size) (hb : off+size ≤ base.size) :
    (copyPadMemory src base srcAddr len).readWithPadding off size = base.readWithPadding off size := by
  rw [readWithPadding_eq_extract_any _ _ _ (by rw [copyPadMemory_size _ _ _ _ hs]; omega),
    copyPadMemory_eq _ _ _ _ hs, extract_append_left _ _ _ _
      (by rw [ByteArray.size_append]; omega), extract_append_left _ _ _ _ hb,
    readWithPadding_eq_extract_any base off size hb]

theorem copyPadMemory_load_below (src base : ByteArray) (srcAddr len : Nat) (read : UInt256)
    (hs : srcAddr+len ≤ src.size) (hb : read.toNat+32 ≤ base.size) :
    memLoad read (copyPadMemory src base srcAddr len) = memLoad read base := by
  rw [memLoad, memLoad, if_neg (by rw [copyPadMemory_size _ _ _ _ hs]; omega),
    if_neg (by omega), copyPadMemory_read_below _ _ _ _ _ _ hs hb]

end Benchmarks.UniswapV4PoolManager
