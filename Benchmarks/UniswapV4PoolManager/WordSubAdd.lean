import Benchmarks.UniswapV4PoolManager.WordIntegerArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: EVM word subtraction associates through wrapping addition.
theorem wordSubSub (x y z : UInt256) :
    UInt256.sub (UInt256.sub x y) z = UInt256.sub x (y+z) := by
  have h := congrArg EVM.wordOfInt
    (show (Int.ofNat x.toNat - Int.ofNat y.toNat) - Int.ofNat z.toNat =
      Int.ofNat x.toNat - (Int.ofNat y.toNat + Int.ofNat z.toNat) by omega)
  simpa only [wordOfIntSub, wordOfIntAdd, wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] using h

end Benchmarks.UniswapV4PoolManager
