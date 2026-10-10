import Benchmarks.UniswapV4PoolManager.IntWordABI
import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: packed signed ABI encoding is the corresponding word suffix.
theorem encodePackedSignedWord (bits : BitWidth) (w : UInt256)
    (hw : -Int.ofNat (EVM.twoPow (bits.val-1)) ≤ EVM.signed w ∧
      EVM.signed w < Int.ofNat (EVM.twoPow (bits.val-1))) :
    encodePackedValue? (.elem (.int (.sint bits))) (.int (EVM.signed w)) =
      some ((EVM.Word.toBytesBE w).drop (32-bits.val/8)) := by
  have hz : bits.val ≠ 0 := Nat.ne_of_gt bits.property.1
  simp only [encodePackedValue?, encodeABIWord?, if_neg hz, if_pos hw, bind, Option.bind,
    wordOfInt_signed, pure]

-- LIBRARY CANDIDATE: addresses occupy the final twenty bytes of their word.
theorem encodePackedAddressWord (owner : AccountAddress) :
    encodePackedValue? abiAddress (.address owner) = some ((EVM.Word.toBytesBE (accountWord owner)).drop 12) := rfl

-- LIBRARY CANDIDATE: byte-array and list views of any suffix of a word.
theorem wordSuffix_toList (w : UInt256) (start : Nat) :
    (w.toByteArray.extract start 32).toList = (EVM.Word.toBytesBE w).drop start := by
  rw [byteArray_extract_toList, ← word_toBytesBE_eq_toByteArray_toList]
  exact List.take_of_length_le (by rw [List.length_drop, word_toBytesBE_length_32])

end Benchmarks.UniswapV4PoolManager
