import Benchmarks.UniswapV4PoolManager.FullMath96Words
import Benchmarks.UniswapV4PoolManager.FullMathRoundWords
import Benchmarks.UniswapV4PoolManager.DivRoundWords

open Ethereum Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

def nextAmount1Quotient (liquidity amount : UInt256) (add : Bool) : UInt256 :=
  if amount.toNat < 2^160 then
    if add then UInt256.div (UInt256.shiftLeft amount (UInt256.ofNat 96)) liquidity
    else divRoundWord (UInt256.shiftLeft amount (UInt256.ofNat 96)) liquidity
  else if add then fullMathWord amount fullMathQ96 liquidity
    else fullMathRoundWord amount fullMathQ96 liquidity

def nextAmount1QuotientFits (liquidity amount : UInt256) (add : Bool) : Prop :=
  if amount.toNat < 2^160 then True
  else if add then fullMathFits amount fullMathQ96 liquidity
    else fullMathRoundFits amount fullMathQ96 liquidity
instance (liquidity amount : UInt256) (add : Bool) : Decidable (nextAmount1QuotientFits liquidity amount add) := by
  unfold nextAmount1QuotientFits
  infer_instance

def nextAmount1Fits (price liquidity amount : UInt256) (add : Bool) : Prop :=
  nextAmount1QuotientFits liquidity amount add ∧
    if add then price.toNat + (nextAmount1Quotient liquidity amount add).toNat < 2^160
    else (nextAmount1Quotient liquidity amount add).toNat < price.toNat
instance (price liquidity amount : UInt256) (add : Bool) : Decidable (nextAmount1Fits price liquidity amount add) := by
  unfold nextAmount1Fits
  infer_instance

def nextAmount1Word (price liquidity amount : UInt256) (add : Bool) : UInt256 :=
  if add then price + nextAmount1Quotient liquidity amount add
  else UInt256.sub price (nextAmount1Quotient liquidity amount add)

theorem nextAmount1Word_canonical {price liquidity amount : UInt256} {add : Bool}
    (hp : price.toNat < 2^160) (hf : nextAmount1Fits price liquidity amount add) :
    (nextAmount1Word price liquidity amount add).toNat < 2^160 := by
  have hb := hf.2
  cases add with
  | false =>
    simp only [nextAmount1Word, Bool.false_eq_true, if_false] at hb ⊢
    rw [usub_toNat (Nat.le_of_lt hb)]
    omega
  | true =>
    simp only [nextAmount1Word, if_true] at hb ⊢
    have h256 : price.toNat+(nextAmount1Quotient liquidity amount true).toNat < UInt256.size := by
      change _ < 2^256
      omega
    rw [uadd_toNat, Nat.mod_eq_of_lt h256]
    exact hb

end Benchmarks.UniswapV4PoolManager
