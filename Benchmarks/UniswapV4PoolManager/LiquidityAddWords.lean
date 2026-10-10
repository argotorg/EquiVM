import Benchmarks.UniswapV4PoolManager.LiquidityAddSource
import Benchmarks.UniswapV4PoolManager.WordSignedRepresentation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def liquidityAddResultWord (liquidity : UInt256) (delta : Int) : UInt256 :=
  EVM.wordOfInt (Int.ofNat liquidity.toNat+delta)

-- LIBRARY CANDIDATE: a checked uint128 sum is represented exactly by its EVM word.
theorem liquidityAddResultWord_value {liquidity : UInt256} {delta : Int} (hf : liquidityAddFits liquidity delta) :
    Int.ofNat (liquidityAddResultWord liquidity delta).toNat = Int.ofNat liquidity.toNat+delta := by
  rw [liquidityAddResultWord, wordOfIntResidue]
  apply Int.emod_eq_of_lt hf.1
  have hh : Int.ofNat liquidity.toNat+delta < (2^128 : Int) := hf.2
  change Int.ofNat liquidity.toNat+delta < (2^256 : Int)
  omega

theorem liquidityAddResultWord_bound {liquidity : UInt256} {delta : Int} (hf : liquidityAddFits liquidity delta) :
    (liquidityAddResultWord liquidity delta).toNat < 2^128 := by
  have he := liquidityAddResultWord_value hf
  have hh : Int.ofNat liquidity.toNat+delta < (2^128 : Int) := hf.2
  simp only [Int.ofNat_eq_natCast] at he hh
  omega

end Benchmarks.UniswapV4PoolManager
