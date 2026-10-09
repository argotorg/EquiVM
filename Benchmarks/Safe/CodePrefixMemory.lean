import Benchmarks.Safe.Common
import Benchmarks.Safe.ByteCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES selector_toNat to the three-byte delegated-account prefix.
theorem prefix3_toNat (cd : ByteArray) (h : 3 ≤ cd.size) :
    (UInt256.shiftRight (uInt256OfByteArray (ByteArray.readBytes cd 0 32)) ⟨232⟩).toNat
      = fromBytesBigEndian (cd.data.toList.take 3) := by
  have hlen := readBytes32_len cd
  have hV : fromBytes' (ByteArray.readBytes cd 0 32).data.toList.reverse < 2 ^ 256 := by
    have := fromBytes'_le (bs := (ByteArray.readBytes cd 0 32).data.toList.reverse)
    rwa [List.length_reverse, hlen] at this
  unfold UInt256.shiftRight uInt256OfByteArray
  rw [if_neg (by decide : ¬ ((⟨232⟩ : UInt256).val ≥ 256))]
  show ((UInt256.ofNat _).val >>> (⟨232⟩ : UInt256).val).val = _
  rw [Fin.shiftRight_val]
  show (UInt256.ofNat _).val.val >>> (232 : ℕ) = _
  rw [Nat.shiftRight_eq_div_pow]
  show (fromBytes' _ % UInt256.size) / 2 ^ 232 = _
  rw [show UInt256.size = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hV]
  show fromBytesBigEndian (ByteArray.readBytes cd 0 32).data.toList / 2 ^ 232 = _
  conv_lhs => rw [← List.take_append_drop 3 (ByteArray.readBytes cd 0 32).data.toList]
  rw [show (232 : ℕ) = 8 * ((ByteArray.readBytes cd 0 32).data.toList.drop 3).length from by
        rw [List.length_drop, hlen], fromBytesBigEndian_append_div]
  congr 1
  have h3 : 3 ≤ cd.data.toList.length := by rw [Array.length_toList]; exact h
  rw [readBytes32_toList, List.take_append_of_le_length (by rw [List.length_take]; omega),
      List.take_take, show min 3 32 = 3 from rfl]

-- LIBRARY CANDIDATE: a bounded prefix copy includes zero padding for a short source.
theorem writePrefix_toList (src mem : ByteArray) (n : Nat) (hn : n ≠ 0) (hm : n ≤ mem.size) :
    (src.write 0 mem 0 n).data.toList =
      src.data.toList.take n ++ List.replicate (n - min n src.size) 0 ++ mem.data.toList.drop n :=
        by
  unfold ByteArray.write
  rw [if_neg hn]
  by_cases hz : src.size = 0
  · rw [if_pos (by omega)]
    have hempty : src.data.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hz
    simp [Nat.min_eq_left hm, hempty, hz, ByteArray.data_copySlice,
      Array.toList_extract, List.extract_eq_take_drop, byteArray_zeroes_toList,
      ByteArray_zeroes_size]
  · rw [if_neg (by omega)]
    have hsum : min n (src.size - 0) + (min mem.size (0 + n) - (0 + min n (src.size - 0))) = n := by
      omega
    simp only [hsum, Nat.zero_sub, zeroes_zero (n := 0) (by rfl),
      ByteArray.append_empty, ByteArray.data_copySlice, ByteArray.toList_data_append,
      Array.toList_extract, List.extract_eq_take_drop, List.drop_zero,
      byteArray_zeroes_toList, Nat.zero_add, Nat.sub_zero]
    simp [List.take_append, Nat.min_eq_right hm, List.take_replicate]
    rw [byteArray_zeroes_toList, ByteArray_zeroes_size,
      show min n (src.size + (n - min n src.size)) = n by omega,
      show n - min n src.size = n - src.size by omega]
    simp only [List.take_replicate, Nat.min_self]
    congr 1
    apply List.take_of_length_le
    simpa only [List.length_drop, Array.length_toList] using Nat.le_refl (mem.size - n)

def codePrefix3 (code : ByteArray) : ByteArray :=
  let headBytes := code.extract 0 3
  headBytes ++ ByteArray.mk (Array.replicate (3 - headBytes.size) (0 : UInt8))

theorem codePrefix3_toList (code : ByteArray) :
    (codePrefix3 code).data.toList =
      code.data.toList.take 3 ++ List.replicate (3 - min 3 code.size) 0 := by
  simp [codePrefix3, ByteArray.toList_data_append, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop]

theorem codePrefix3_size (code : ByteArray) : (codePrefix3 code).size = 3 := by
  change (codePrefix3 code).data.size = 3
  rw [← Array.length_toList, codePrefix3_toList, List.length_append,
    List.length_take, List.length_replicate, Array.length_toList]
  change min 3 code.size + (3 - min 3 code.size) = 3
  omega

theorem writePrefix3_toList (src mem : ByteArray) (hm : 3 ≤ mem.size) :
    (src.write 0 mem 0 3).data.toList =
      (codePrefix3 src).data.toList ++ mem.data.toList.drop 3 := by
  rw [writePrefix_toList src mem 3 (by decide) hm, codePrefix3_toList]

theorem writePrefix3_size (src mem : ByteArray) (hm : 3 ≤ mem.size) :
    (src.write 0 mem 0 3).size = mem.size := by
  change (src.write 0 mem 0 3).data.size = mem.data.size
  rw [← Array.length_toList, writePrefix3_toList src mem hm,
    List.length_append, List.length_drop, Array.length_toList, Array.length_toList]
  change (codePrefix3 src).size + (mem.size - 3) = mem.size
  rw [codePrefix3_size]
  omega

theorem writePrefix3_padded (src mem : ByteArray) (hm : 3 ≤ mem.size) :
    src.write 0 mem 0 3 = (codePrefix3 src).write 0 mem 0 3 := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [writePrefix3_toList src mem hm, write0_data _ mem 3 (by decide)
    (by rw [codePrefix3_size])]
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  congr 1
  · symm
    apply List.take_of_length_le
    simpa only [Array.length_toList] using (codePrefix3_size src).le
  · symm
    apply List.take_of_length_le
    simp only [List.length_drop, Array.length_toList]
    exact Nat.le_refl _

theorem writePrefix3_read64 (src mem : ByteArray) (hm : 96 ≤ mem.size) :
    (src.write 0 mem 0 3).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  rw [writePrefix3_padded src mem (by omega)]
  exact copyWindow_read_preserved (codePrefix3 src) mem 0 0 3 64 (by decide)
    (by rw [codePrefix3_size]) (by omega) (by omega) (Or.inr (by decide))

-- GENERALIZES writePrefix3_read64 to every in-bounds read above the copied prefix.
theorem writePrefix3ReadAbove (src mem : ByteArray) (off count : Nat)
    (hm : 3 ≤ mem.size) (hin : off + count ≤ mem.size) (hlo : 3 ≤ off) :
    (src.write 0 mem 0 3).readWithPadding off count = mem.readWithPadding off count := by
  rw [writePrefix3_padded src mem hm]
  exact copyWindowReadAbove (codePrefix3 src) mem 0 0 3 off count
    (by rw [codePrefix3_size]) (by omega) hin (by omega)

theorem codePrefix3_word_bound (src : ByteArray) :
    fromByteArrayBigEndian (codePrefix3 src) < UInt256.size := by
  have h := fromBytesBigEndian_bound (codePrefix3 src).data.toList
  rw [Array.length_toList] at h
  change fromBytesBigEndian (codePrefix3 src).data.toList <
    2 ^ (8 * (codePrefix3 src).size) at h
  rw [codePrefix3_size] at h
  rw [fromByteArrayBigEndian, byteArray_toList_eq]
  exact lt_trans h (by decide)

theorem copiedPrefix3Word (src mem : ByteArray) (hm : 32 ≤ mem.size) :
    UInt256.shiftRight (memLoad ⟨0⟩ (src.write 0 mem 0 3)) (UInt256.ofNat 232) =
      UInt256.ofNat (fromByteArrayBigEndian (codePrefix3 src)) := by
  have hm' : 32 ≤ (src.write 0 mem 0 3).size := by
    rw [writePrefix3_size src mem (by omega)]
    exact hm
  change UInt256.shiftRight (loadedWord (src.write 0 mem 0 3) ⟨0⟩) ⟨232⟩ = _
  rw [loadedWord_zero hm']
  apply u256_inj
  rw [prefix3_toNat _ (by omega), UInt256.toNat_ofNat_of_lt (codePrefix3_word_bound src)]
  rw [writePrefix3_toList src mem (by omega),
    List.take_append_of_le_length (by simpa only [Array.length_toList] using
      (codePrefix3_size src).ge)]
  have hlen : (codePrefix3 src).data.toList.length = 3 := by
    simpa only [Array.length_toList] using codePrefix3_size src
  rw [← hlen, List.take_length]
  rw [fromByteArrayBigEndian, byteArray_toList_eq]

theorem codePrefix3_eq_magic (src : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian (codePrefix3 src)) = UInt256.ofNat 15663360 ↔
      codePrefix3 src = ⟨#[0xef, 0x01, 0x00]⟩ := by
  constructor
  · intro h
    have hn := congrArg UInt256.toNat h
    rw [UInt256.toNat_ofNat_of_lt (codePrefix3_word_bound src),
      UInt256.toNat_ofNat_of_lt (by decide)] at hn
    apply ByteArray.ext
    apply Array.toList_inj.mp
    apply fromBytesBigEndian_inj_of_length
    · simpa only [Array.length_toList] using codePrefix3_size src
    · simpa only [fromByteArrayBigEndian, byteArray_toList_eq] using hn
  · intro h
    rw [h]
    native_decide

theorem copiedPrefix3Check (src mem : ByteArray) (hm : 32 ≤ mem.size) :
    UInt256.eq (UInt256.ofNat 15663360)
        (UInt256.shiftRight (memLoad ⟨0⟩ (src.write 0 mem 0 3)) (UInt256.ofNat 232)) =
      (decide (codePrefix3 src = ⟨#[0xef, 0x01, 0x00]⟩)).toUInt256 := by
  rw [copiedPrefix3Word src mem hm]
  by_cases h : codePrefix3 src = ⟨#[0xef, 0x01, 0x00]⟩
  · rw [(codePrefix3_eq_magic src).mpr h, uInt256_eq_self]
    simp only [h, decide_true]
    rfl
  · rw [uInt256_eq_zero_of_ne (fun he ↦ h ((codePrefix3_eq_magic src).mp
      (uInt256_eq_one_eq he).symm))]
    simp only [h, decide_false]
    rfl

end Benchmarks.Safe
