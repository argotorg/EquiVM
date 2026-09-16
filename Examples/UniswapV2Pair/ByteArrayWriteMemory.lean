import Reasoning.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace UniswapV2Pair

-- LIBRARY CANDIDATE: size preservation for an arbitrary in-bounds prefix write.
theorem byteArray_write_size_of_inBounds (src base : ByteArray) (dest len : Nat)
    (hsrc : len ≤ src.size) (hin : dest + len ≤ base.size) :
    (src.write 0 base dest len).size = base.size := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_len_zero]
  · rw [write_eq_gen src base dest len hz hsrc hin,
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract]
    omega

end UniswapV2Pair
