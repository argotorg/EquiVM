import Benchmarks.UniswapV4PoolManager.FullMathRoundWords
import Benchmarks.UniswapV4PoolManager.DivRoundWords
import Benchmarks.UniswapV4PoolManager.WordFieldPacking

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

def amount0Lo (a b : UInt256) : UInt256 := if b.toNat < a.toNat then b else a
def amount0Hi (a b : UInt256) : UInt256 := if b.toNat < a.toNat then a else b
def amount0Numerator1 (liquidity : UInt256) : UInt256 := UInt256.shiftLeft liquidity (UInt256.ofNat 96)
def amount0Numerator2 (lo hi : UInt256) : UInt256 := UInt256.sub hi lo
def amount0CoreFits (lo hi liquidity : UInt256) (roundUp : Bool) : Prop :=
  lo ≠ ⟨0⟩ ∧ if roundUp then
    fullMathRoundFits (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi
  else fullMathFits (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi
instance (lo hi liquidity : UInt256) (roundUp : Bool) : Decidable (amount0CoreFits lo hi liquidity roundUp) :=
  inferInstanceAs (Decidable (_ ∧ _))
def amount0CoreWord (lo hi liquidity : UInt256) (roundUp : Bool) : UInt256 :=
  if roundUp then divRoundWord
    (fullMathRoundWord (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi) lo
  else UInt256.div (fullMathWord (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi) lo
def amount0Fits (a b liquidity : UInt256) (roundUp : Bool) : Prop :=
  amount0CoreFits (amount0Lo a b) (amount0Hi a b) liquidity roundUp
instance (a b liquidity : UInt256) (roundUp : Bool) : Decidable (amount0Fits a b liquidity roundUp) :=
  inferInstanceAs (Decidable (amount0CoreFits _ _ _ _))
def amount0Word (a b liquidity : UInt256) (roundUp : Bool) : UInt256 :=
  amount0CoreWord (amount0Lo a b) (amount0Hi a b) liquidity roundUp

theorem amount0_ordered (a b : UInt256) : (amount0Lo a b).toNat ≤ (amount0Hi a b).toNat := by
  unfold amount0Lo amount0Hi
  split <;> omega

theorem amount0_bounds {a b : UInt256} (ha : a.toNat < 2^160) (hb : b.toNat < 2^160) :
    (amount0Lo a b).toNat < 2^160 ∧ (amount0Hi a b).toNat < 2^160 := by
  unfold amount0Lo amount0Hi
  split <;> exact ⟨by assumption, by assumption⟩

theorem amount0Numerator2_bound {lo hi : UInt256} (ho : lo.toNat ≤ hi.toNat)
    (hh : hi.toNat < 2^160) : (amount0Numerator2 lo hi).toNat < 2^160 := by
  rw [amount0Numerator2, usub_toNat ho]
  omega

theorem amount0Numerator1_clean {liquidity : UInt256} (hl : liquidity.toNat < 2^128) :
    UInt256.land (UInt256.shiftLeft liquidity (UInt256.ofNat 96))
      (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880) =
      amount0Numerator1 liquidity := by
  rw [u256_land_comm]
  apply shiftedMaskClean (bits := 128) _ _ (by decide) hl
  · have h := Nat.mul_lt_mul_of_pos_right hl (by decide : 0 < 2^96)
    exact lt_trans h (by decide)
  · decide +kernel

end Benchmarks.UniswapV4PoolManager
