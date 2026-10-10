import Benchmarks.UniswapV4PoolManager.SignedArithmetic
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES encodeABIValue_uint256 to every ABI unsigned width.
theorem encodeUnsignedWord (bits : BitWidth) (w : UInt256) (hw : w.toNat < EVM.twoPow bits.val) :
    encodeABIValue? (.elem (.int (.uint bits))) (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  have hz : bits.val ≠ 0 := Nat.ne_of_gt bits.property.1
  have hr : 0 ≤ (Int.ofNat w.toNat) ∧ (Int.ofNat w.toNat) < Int.ofNat (EVM.twoPow bits.val) :=
    ⟨Int.ofNat_nonneg _, Int.ofNat_lt.mpr hw⟩
  simp only [encodeABIValue?, encodeABIWord?, if_neg hz, if_pos hr, bind, Option.bind]
  rw [show EVM.word (Int.ofNat w.toNat).toNat = w from u256_ofNat_toNat w]

-- LIBRARY CANDIDATE: ABI encoding of a signed word at any width for which it fits.
theorem encodeSignedWord (bits : BitWidth) (w : UInt256)
    (hw : -Int.ofNat (EVM.twoPow (bits.val-1)) ≤ EVM.signed w ∧
      EVM.signed w < Int.ofNat (EVM.twoPow (bits.val-1))) :
    encodeABIValue? (.elem (.int (.sint bits))) (.int (EVM.signed w)) =
      some (EVM.Word.toBytesBE w) := by
  have hz : bits.val ≠ 0 := Nat.ne_of_gt bits.property.1
  simp only [encodeABIValue?, encodeABIWord?, if_neg hz, if_pos hw, bind, Option.bind,
    wordOfInt_signed]

end Benchmarks.UniswapV4PoolManager
