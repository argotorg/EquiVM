import Benchmarks.UniswapV4PoolManager.FullMathWords
open Ethereum Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the lowest-bit mask of a positive bounded natural is nonzero.
theorem natLowBit_ne {n k : Nat} (hpos : 0 < n) (hlt : n < 2^k) :
    (2^k-n) &&& n ≠ 0 := by
  induction k generalizing n with
  | zero => simp only [Nat.pow_zero] at hlt; omega
  | succ k ih =>
    rw [Nat.pow_succ] at hlt ⊢
    intro hz
    by_cases he : n % 2 = 0
    · have hn : 0 < n/2 := by omega
      have hb : n/2 < 2^k := by omega
      have hd : (2^k*2-n)/2 = 2^k-n/2 := by omega
      apply ih hn hb
      have hx := congrArg (fun x => x/2) hz
      simpa only [Nat.and_div_two, hd, Nat.zero_div] using hx
    · have hn : n%2 = 1 := by omega
      have hd : (2^k*2-n)%2 = 1 := by omega
      have hx := congrArg (fun x => x%2) hz
      change ((2^k*2-n) &&& n) % 2^1 = 0 at hx
      rw [Nat.and_mod_two_pow] at hx
      change ((2^k*2-n)%2 &&& n%2) = 0 at hx
      rw [hd, hn] at hx
      contradiction

-- LIBRARY CANDIDATE: a nonzero EVM word has a nonzero lowest-bit mask.
theorem wordLowBit_ne (w : UInt256) (hw : w ≠ ⟨0⟩) :
    UInt256.land (UInt256.sub ⟨0⟩ w) w ≠ ⟨0⟩ := by
  have hpos : 0 < w.toNat := by
    by_contra h
    apply hw
    apply u256_inj
    change w.toNat = 0
    omega
  intro hz
  have hn := congrArg UInt256.toNat hz
  rw [uland_toNat, usub_toNat_underflow (a := ⟨0⟩) (b := w) hpos] at hn
  change (2^256-w.toNat) &&& w.toNat = 0 at hn
  exact natLowBit_ne (k := 256) hpos w.val.isLt hn
end Benchmarks.UniswapV4PoolManager
