import Benchmarks.UniswapV4PoolManager.SignedArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: every word's signed interpretation lies in the int256 range.
theorem signedWord_fits (word : UInt256) : int256Fits (EVM.signed word) := by
  have hw : word.toNat < 2^256 := word.val.isLt
  change -(2^255 : Int) ≤ EVM.signed word ∧ EVM.signed word < 2^255
  change -(2^255 : Int) ≤ (if word.toNat < 2^255 then (word.toNat : Int) else word.toNat - (2^256 : Int)) ∧
    (if word.toNat < 2^255 then (word.toNat : Int) else word.toNat - (2^256 : Int)) < 2^255
  split_ifs <;> constructor <;> omega

end Benchmarks.UniswapV4PoolManager
