import Solm.Examples.UniswapV2Pair.Common
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

theorem uniswapUint256PairReturnEncoding (word0 word1 : UInt256) :
    encodeReturnValues? [uint256, uint256]
      [.int (Int.ofNat word0.toNat), .int (Int.ofNat word1.toNat)] =
      some (word0.toByteArray ++ word1.toByteArray) := by
  have henc (word : UInt256) : encodeABIValue? uint256 (.int (Int.ofNat word.toNat)) = some (EVM.Word.toBytesBE word) := by
    have hword : EVM.word word.toNat = word := u256_ofNat_toNat word
    have hlt : word.toNat < EVM.twoPow 256 := word.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hhead : abiTupleHeadSize? [uint256, uint256] = some 64 := by native_decide
  have hdyn : isDynamicABIType uint256 = false := by native_decide
  rw [toByteArray_eq_toBytesBE word0, toByteArray_eq_toBytesBE word1]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, hhead, henc,
    hdyn, bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

end UniswapV2Pair
