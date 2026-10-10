import Benchmarks.UniswapV4PoolManager.SignedRangeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: signed normalization always produces a value in its target range.
theorem normalizeSigned_fits (bits : BitWidth) (n : Int) :
    signedFits bits (normalizeInt (.sint bits) n) := by
  have hbits : bits.val = bits.val-1+1 := by have := bits.property.1; omega
  have hp : (2 : Int)^bits.val = (2 : Int)^(bits.val-1) + (2 : Int)^(bits.val-1) := by
    conv_lhs => rw [hbits, pow_succ]
    ring
  have hpos : (0 : Int) < 2^(bits.val-1) := pow_pos (by decide) _
  have hlo := Int.emod_nonneg n (ne_of_gt (pow_pos (by decide : (0 : Int) < 2) bits.val))
  have hhi := Int.emod_lt_of_pos n (pow_pos (by decide : (0 : Int) < 2) bits.val)
  simp only [signedFits, normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int]
  split_ifs <;> constructor <;> omega

-- LIBRARY CANDIDATE: equality with a signed cast is exactly the signed range check.
theorem normalizeSigned_eq_self_iff (bits : BitWidth) (n : Int) :
    normalizeInt (.sint bits) n = n ↔ signedFits bits n := by
  constructor
  · intro he
    rw [← he]
    exact normalizeSigned_fits bits n
  · exact normalizeSigned_of_fits

end Benchmarks.UniswapV4PoolManager
