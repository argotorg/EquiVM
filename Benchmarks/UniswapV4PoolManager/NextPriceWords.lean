import Benchmarks.UniswapV4PoolManager.NextAmount0Words
import Benchmarks.UniswapV4PoolManager.NextAmount1Words

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

def nextPriceCalcFits (price liquidity amount : UInt256) (use0 add : Bool) : Prop :=
  if use0 then nextAmount0Fits price liquidity amount add else nextAmount1Fits price liquidity amount add
instance (price liquidity amount : UInt256) (use0 add : Bool) :
    Decidable (nextPriceCalcFits price liquidity amount use0 add) := by
  unfold nextPriceCalcFits
  infer_instance

def nextPriceCalcWord (price liquidity amount : UInt256) (use0 add : Bool) : UInt256 :=
  if use0 then nextAmount0Word price liquidity amount add else nextAmount1Word price liquidity amount add

def nextPriceValid (price liquidity : UInt256) : Prop := price ≠ ⟨0⟩ ∧ liquidity ≠ ⟨0⟩
instance (price liquidity : UInt256) : Decidable (nextPriceValid price liquidity) :=
  inferInstanceAs (Decidable (_ ∧ _))

def nextPriceFits (price liquidity amount : UInt256) (input zeroForOne : Bool) : Prop :=
  nextPriceValid price liquidity ∧
    nextPriceCalcFits price liquidity amount (if zeroForOne then input else !input) input
instance (price liquidity amount : UInt256) (input zeroForOne : Bool) :
    Decidable (nextPriceFits price liquidity amount input zeroForOne) :=
  inferInstanceAs (Decidable (_ ∧ _))

def nextPriceWord (price liquidity amount : UInt256) (input zeroForOne : Bool) : UInt256 :=
  nextPriceCalcWord price liquidity amount (if zeroForOne then input else !input) input

theorem nextPriceCalcWord_canonical {price liquidity amount : UInt256} {use0 add : Bool}
    (hp : price.toNat < 2^160) (hf : nextPriceCalcFits price liquidity amount use0 add) :
    (nextPriceCalcWord price liquidity amount use0 add).toNat < 2^160 := by
  cases use0 with
  | false =>
    simp only [nextPriceCalcFits, nextPriceCalcWord, Bool.false_eq_true, if_false] at hf ⊢
    exact nextAmount1Word_canonical hp hf
  | true =>
    simp only [nextPriceCalcFits, nextPriceCalcWord, if_true] at hf ⊢
    exact nextAmount0Word_canonical hp hf

theorem nextPriceWord_canonical {price liquidity amount : UInt256} {input zeroForOne : Bool}
    (hp : price.toNat < 2^160) (hf : nextPriceFits price liquidity amount input zeroForOne) :
    (nextPriceWord price liquidity amount input zeroForOne).toNat < 2^160 :=
  nextPriceCalcWord_canonical hp hf.2

end Benchmarks.UniswapV4PoolManager
