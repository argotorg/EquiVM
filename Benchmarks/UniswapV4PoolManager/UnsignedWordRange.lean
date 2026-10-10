import Benchmarks.UniswapV4PoolManager.UnsignedRangeSource
import Benchmarks.UniswapV4PoolManager.WordSignedRepresentation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES the uint160 shift guard to arbitrary widths below 256.
theorem wordShiftRight_zero_iff (w : UInt256) {n : Nat} (hn : n < 256) :
    UInt256.shiftRight w (UInt256.ofNat n) = ⟨0⟩ ↔ w.toNat < 2^n := by
  have hs := wordShiftRightNat w hn
  constructor
  · intro hz
    have h := congrArg UInt256.toNat hz
    rw [hs] at h
    change w.toNat / 2^n = 0 at h
    exact (Nat.div_eq_zero_iff.mp h).resolve_left (Nat.ne_of_gt (Nat.pow_pos (by decide)))
  · intro hw
    apply u256_inj
    rw [hs]
    exact Nat.div_eq_of_lt hw

-- LIBRARY CANDIDATE: a shift tests the unsigned range of an encoded signed integer.
theorem wordOfInt_unsignedRange {n : Int} (bits : BitWidth) (hb : bits.val < 256)
    (hn : int256Fits n) :
    UInt256.shiftRight (EVM.wordOfInt n) (UInt256.ofNat bits.val) = ⟨0⟩ ↔ unsignedFits bits n := by
  rw [wordShiftRight_zero_iff _ hb]
  have hr := wordOfIntResidue n
  have hp : (2 : Int)^bits.val ≤ 2^255 := pow_le_pow_right₀ (by decide) (by omega)
  have hcast : (Int.ofNat (2^bits.val)) = (2 : Int)^bits.val := by simp
  have hlo := hn.1
  have hhi := hn.2
  unfold unsignedFits
  simp only [Int.ofNat_eq_natCast] at hr hcast
  change -(2^255 : Int) ≤ n at hlo
  change n < (2^255 : Int) at hhi
  omega

end Benchmarks.UniswapV4PoolManager
