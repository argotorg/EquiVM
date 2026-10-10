import Benchmarks.UniswapV4PoolManager.Amount0Words

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

def nextAmount0Product (price amount : UInt256) : UInt256 := UInt256.mul amount price
def nextAmount0Direct (price liquidity amount : UInt256) : Prop :=
  UInt256.div (nextAmount0Product price amount) amount = price ∧
    (amount0Numerator1 liquidity).toNat ≤ (amount0Numerator1 liquidity+nextAmount0Product price amount).toNat
instance (price liquidity amount : UInt256) : Decidable (nextAmount0Direct price liquidity amount) :=
  inferInstanceAs (Decidable (_ ∧ _))
def nextAmount0SubGuard (price liquidity amount : UInt256) : Prop :=
  UInt256.div (nextAmount0Product price amount) amount = price ∧
    (nextAmount0Product price amount).toNat < (amount0Numerator1 liquidity).toNat
instance (price liquidity amount : UInt256) : Decidable (nextAmount0SubGuard price liquidity amount) :=
  inferInstanceAs (Decidable (_ ∧ _))

def nextAmount0RoundFits (n price d : UInt256) (checked : Bool) : Prop :=
  fullMathRoundFits n price d ∧ if checked then (fullMathRoundWord n price d).toNat < 2^160 else True
instance (n price d : UInt256) (checked : Bool) : Decidable (nextAmount0RoundFits n price d checked) :=
  inferInstanceAs (Decidable (_ ∧ _))
def nextAmount0RoundWord (n price d : UInt256) (checked : Bool) : UInt256 :=
  if checked then fullMathRoundWord n price d else UInt256.land (fullMathRoundWord n price d) solcAddrMask

def nextAmount0FallbackFits (price liquidity amount : UInt256) : Prop :=
  (UInt256.div (amount0Numerator1 liquidity) price).toNat+amount.toNat < UInt256.size
instance (price liquidity amount : UInt256) : Decidable (nextAmount0FallbackFits price liquidity amount) :=
  inferInstanceAs (Decidable (_ < _))
def nextAmount0FallbackWord (price liquidity amount : UInt256) : UInt256 :=
  UInt256.land (divRoundWord (amount0Numerator1 liquidity)
    (UInt256.div (amount0Numerator1 liquidity) price+amount)) solcAddrMask

def nextAmount0CoreFits (price liquidity amount : UInt256) (add : Bool) : Prop :=
  if add then
    if nextAmount0Direct price liquidity amount then
      nextAmount0RoundFits (amount0Numerator1 liquidity) price
        (amount0Numerator1 liquidity+nextAmount0Product price amount) false
    else nextAmount0FallbackFits price liquidity amount
  else nextAmount0SubGuard price liquidity amount ∧
    nextAmount0RoundFits (amount0Numerator1 liquidity) price
      (UInt256.sub (amount0Numerator1 liquidity) (nextAmount0Product price amount)) true
instance (price liquidity amount : UInt256) (add : Bool) : Decidable (nextAmount0CoreFits price liquidity amount add) := by
  unfold nextAmount0CoreFits
  infer_instance
def nextAmount0CoreWord (price liquidity amount : UInt256) (add : Bool) : UInt256 :=
  if add then
    if nextAmount0Direct price liquidity amount then
      nextAmount0RoundWord (amount0Numerator1 liquidity) price
        (amount0Numerator1 liquidity+nextAmount0Product price amount) false
    else nextAmount0FallbackWord price liquidity amount
  else nextAmount0RoundWord (amount0Numerator1 liquidity) price
    (UInt256.sub (amount0Numerator1 liquidity) (nextAmount0Product price amount)) true

def nextAmount0Fits (price liquidity amount : UInt256) (add : Bool) : Prop :=
  amount = ⟨0⟩ ∨ nextAmount0CoreFits price liquidity amount add
instance (price liquidity amount : UInt256) (add : Bool) : Decidable (nextAmount0Fits price liquidity amount add) :=
  inferInstanceAs (Decidable (_ ∨ _))
def nextAmount0Word (price liquidity amount : UInt256) (add : Bool) : UInt256 :=
  if amount = ⟨0⟩ then price else nextAmount0CoreWord price liquidity amount add

theorem nextAmount0RoundWord_canonical {n price d : UInt256} {checked : Bool}
    (hf : nextAmount0RoundFits n price d checked) : (nextAmount0RoundWord n price d checked).toNat < 2^160 := by
  cases checked with
  | false => exact u256LandMaskToNatLtOfToNat _ solcAddrMask (bits := 160) rfl
  | true => exact hf.2

theorem nextAmount0FallbackWord_canonical (price liquidity amount : UInt256) :
    (nextAmount0FallbackWord price liquidity amount).toNat < 2^160 :=
  u256LandMaskToNatLtOfToNat _ solcAddrMask (bits := 160) rfl

theorem nextAmount0CoreWord_canonical {price liquidity amount : UInt256} {add : Bool}
    (hf : nextAmount0CoreFits price liquidity amount add) :
    (nextAmount0CoreWord price liquidity amount add).toNat < 2^160 := by
  cases add with
  | false =>
    simp only [nextAmount0CoreFits, nextAmount0CoreWord, Bool.false_eq_true, if_false] at hf ⊢
    exact nextAmount0RoundWord_canonical (n := amount0Numerator1 liquidity) (price := price)
      (d := UInt256.sub (amount0Numerator1 liquidity) (nextAmount0Product price amount))
      (checked := true) hf.2
  | true =>
    by_cases hd : nextAmount0Direct price liquidity amount
    · simp only [nextAmount0CoreFits, nextAmount0CoreWord, if_true, hd] at hf ⊢
      exact nextAmount0RoundWord_canonical (n := amount0Numerator1 liquidity) (price := price)
        (d := amount0Numerator1 liquidity+nextAmount0Product price amount) (checked := false) hf
    · simp only [nextAmount0CoreWord, if_true, hd, if_false]
      exact nextAmount0FallbackWord_canonical _ _ _

theorem nextAmount0Word_canonical {price liquidity amount : UInt256} {add : Bool}
    (hp : price.toNat < 2^160) (hf : nextAmount0Fits price liquidity amount add) :
    (nextAmount0Word price liquidity amount add).toNat < 2^160 := by
  by_cases hz : amount = ⟨0⟩
  · simpa only [nextAmount0Word, if_pos hz] using hp
  · simpa only [nextAmount0Word, if_neg hz] using
      nextAmount0CoreWord_canonical (price := price) (liquidity := liquidity) (amount := amount)
        (add := add) (hf.resolve_left hz)

end Benchmarks.UniswapV4PoolManager
