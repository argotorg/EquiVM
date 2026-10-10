import Benchmarks.UniswapV4PoolManager.NarrowWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem int24Canonical_natAbs_le {w : UInt256} (hc : int24Canonical w) :
    (EVM.signed w).natAbs ≤ 2^23 := by
  have hw : w.toNat < 2^256 := w.val.isLt
  have hb : -(2^23 : Int) ≤ EVM.signed w ∧ EVM.signed w < (2^23 : Int) := by
    unfold int24Canonical at hc
    simp only [EVM.signed, EVM.signBit, EVM.wordModulus, EVM.twoPow,
      UInt256.toNat, Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat] at *
    split <;> omega
  cases he : EVM.signed w <;> simp only [he] at hb ⊢ <;> omega

end Benchmarks.UniswapV4PoolManager
