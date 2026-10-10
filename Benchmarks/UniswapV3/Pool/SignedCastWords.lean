import Benchmarks.UniswapV3.Pool.SourceSignedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a nonnegative word below a signed type's sign bit is unchanged by casting.
theorem normalizeSint_word_of_lt (width : ABI.BitWidth) (word : UInt256)
    (hb : word.toNat < 2 ^ (width.val - 1)) :
    normalizeInt (.sint width) (Int.ofNat word.toNat) = Int.ofNat word.toNat := by
  apply normalizeSint_eq_self
  · exact le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
  · exact Int.ofNat_lt.mpr hb

end Benchmarks.UniswapV3.Pool
