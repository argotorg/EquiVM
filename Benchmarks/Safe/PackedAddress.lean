import Benchmarks.Safe.Common
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: the numeric value of a big-endian word's suffix.
theorem wordBytesBE_drop_value (w : UInt256) (n : Nat) :
    fromBytesBigEndian ((EVM.Word.toBytesBE w).drop n) = w.toNat % 256 ^ (32 - n) := by
  have hr : (EVM.Word.toBytesBE w).reverse = (EVM.Word.toBytesLEWithSizeProof w).1 := by
    simp [EVM.Word.toBytesBE, EVM.Word.toBytesLEWithSizeProof, toBytesBigEndian]
  change fromBytes' ((EVM.Word.toBytesBE w).drop n).reverse = _
  rw [List.reverse_drop, word_toBytesBE_length_32, hr, fromBytes'_take_wordLE]

-- LIBRARY CANDIDATE: SHL 96 places an address's packed encoding at the start of a word.
theorem packedAddress_shifted_word (a : AccountAddress) :
    ((UInt256.shiftLeft (UInt256.ofNat a.val) ⟨96⟩).toByteArray.extract 0 20).toList =
      (EVM.word a.val).toBytesBE.drop 12 := by
  have ha : (UInt256.ofNat a.val).toNat = a.val :=
    ulit_toNat' _ (lt_trans a.isLt (by decide))
  apply fromBytesBigEndian_inj_of_length
  · simp only [byteArray_toList_eq, Array.length_toList, ByteArray.size_data,
      ByteArray.size_extract, toByteArray_size, List.length_drop, word_toBytesBE_length_32]
    decide
  · rw [bytesBE_extract_high _ 20 (by decide),
      shiftLeft96_toNat_of_lt_160 _ (by rw [ha]; exact a.isLt),
      wordBytesBE_drop_value]
    change (UInt256.ofNat a.val).toNat * 2 ^ 96 / 2 ^ 96 =
      (UInt256.ofNat a.val).toNat % 2 ^ 160
    rw [Nat.mul_div_cancel _ (by decide), ha]
    exact (Nat.mod_eq_of_lt a.isLt).symm

end Benchmarks.Safe
