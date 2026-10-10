import Benchmarks.UniswapV4PoolManager.WordAbsolute
import Benchmarks.UniswapV4PoolManager.WordIntegerArithmetic
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def absDiffWord (a b : UInt256) : UInt256 :=
  if b.toNat ≤ a.toNat then UInt256.sub a b else UInt256.sub b a

-- LIBRARY CANDIDATE: the SAR/ADD/XOR idiom computes the absolute difference of nonnegative signed words.
theorem absDiffWord_compiled {a b : UInt256} (ha : a.toNat < 2^255) (hb : b.toNat < 2^255) :
    UInt256.xor (UInt256.sar (UInt256.ofNat 255) (UInt256.sub a b) + UInt256.sub a b)
      (UInt256.sar (UInt256.ofNat 255) (UInt256.sub a b)) = absDiffWord a b := by
  rw [wordAbsolute, ← wordOfInt_sub_natCasts]
  have hf : int256Fits (Int.ofNat a.toNat - Int.ofNat b.toNat) := by
    simp only [int256Fits, Int.ofNat_eq_natCast]
    constructor <;> omega
  rw [signed_wordOfInt hf]
  simp only [Int.ofNat_eq_natCast]
  apply u256_inj
  unfold absDiffWord
  split
  · rw [usub_toNat (by assumption)]
    have hn := Int.natAbs_of_nonneg (a := (a.toNat : Int) - (b.toNat : Int)) (by omega)
    change ((a.toNat : Int) - (b.toNat : Int)).natAbs % 2^256 = _
    omega
  · rw [usub_toNat (by omega)]
    have hn := Int.ofNat_natAbs_of_nonpos (a := (a.toNat : Int) - (b.toNat : Int)) (by omega)
    change ((a.toNat : Int) - (b.toNat : Int)).natAbs % 2^256 = _
    omega
end Benchmarks.UniswapV4PoolManager
