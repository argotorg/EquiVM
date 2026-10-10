import Benchmarks.UniswapV3.Pool.SignedWords
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.Memory.toByteArray_extract4_32_toList to any suffix.
theorem wordBytes_extract_suffix (w : UInt256) (n : Nat) :
    (w.toByteArray.extract n 32).toList = (EVM.Word.toBytesBE w).drop n := by
  rw [toByteArray_eq_toBytesBE, byteArray_toList_eq, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop]
  rw [List.take_of_length_le]
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp only [List.length_drop, hlen, le_refl]

-- GENERALIZES Reasoning.Memory.fromByteArrayBigEndian_toByteArray_extract4_32.
theorem wordBytes_suffix_value (w : UInt256) (n : Nat) :
    fromBytesBigEndian ((EVM.Word.toBytesBE w).drop n) = w.toNat % 2 ^ (8 * (32 - n)) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  have hb := fromBytesBigEndian_bound ((EVM.Word.toBytesBE w).drop n)
  rw [List.length_drop, hlen] at hb
  have hs := fromBytesBigEndian_append ((EVM.Word.toBytesBE w).take n)
    ((EVM.Word.toBytesBE w).drop n)
  rw [List.take_append_drop, fromBytesBE_word, List.length_drop, hlen] at hs
  rw [hs]
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hb]

-- LIBRARY CANDIDATE: shifting a word by whole bytes moves its suffix into the prefix.
theorem wordBytes_shift_prefix (w : UInt256) (n : Nat) (hn : n < 32) :
    (UInt256.shiftLeft w (UInt256.ofNat (8 * n))).toByteArray.extract 0 (32 - n) =
      w.toByteArray.extract n 32 := by
  have hshift : (UInt256.shiftLeft w (UInt256.ofNat (8 * n))).toNat =
      (w.toNat % 2 ^ (8 * (32 - n))) * 2 ^ (8 * n) := by
    have hs : (UInt256.ofNat (8 * n)).toNat = 8 * n :=
      ulit_toNat' _ (by change _ < 2 ^ 256; omega)
    unfold UInt256.shiftLeft
    rw [if_neg (by change ¬ (UInt256.ofNat (8 * n)).toNat ≥ 256; rw [hs]; omega)]
    change (w.val <<< (UInt256.ofNat (8 * n)).val).val = _
    rw [Fin.shiftLeft_val]
    change (w.toNat <<< (UInt256.ofNat (8 * n)).toNat) % UInt256.size = _
    rw [hs, Nat.shiftLeft_eq]
    have he : UInt256.size = 2 ^ (8 * (32 - n)) * 2 ^ (8 * n) := by
      rw [← Nat.pow_add, show 8 * (32 - n) + 8 * n = 256 by omega]
      rfl
    rw [he, Nat.mul_mod_mul_right]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · simp only [byteArray_toList_eq, Array.length_toList]
    change (_ : ByteArray).size = (_ : ByteArray).size
    simp only [ByteArray.size_extract, toByteArray_size]
    omega
  · rw [bytesBE_extract_high _ _ (by omega), wordBytes_extract_suffix, wordBytes_suffix_value,
      show 32 - (32 - n) = n by omega, hshift, Nat.mul_div_left _ (by positivity)]

-- LIBRARY CANDIDATE: packed encoding of a normalized signed scalar.
theorem encodePacked_sintCast (width : ABI.BitWidth) (w : UInt256) :
    encodePackedValue? (.elem (.int (.sint width)))
      (.int (normalizeInt (.sint width) (Int.ofNat w.toNat))) =
      some ((EVM.Word.toBytesBE (EVM.wordOfInt
        (normalizeInt (.sint width) (Int.ofNat w.toNat)))).drop (32 - width.val / 8)) := by
  have hb := normalizeSint_bounds width (Int.ofNat w.toNat)
  simp only [encodePackedValue?, encodeABIWord?,
    if_neg (Nat.ne_of_gt width.property.1), if_pos hb, bind, Option.bind]

end Benchmarks.UniswapV3.Pool
