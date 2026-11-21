import Benchmarks.Midnight.TickExpModel

/-! Arithmetic correspondence on the contract's finite range of 6745 permitted ticks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def tickExpWord (tick : Nat) : UInt256 :=
  let x := tickExpArgumentWord (UInt256.ofNat tick)
  if tickExpArgument tick < 0 then
    UInt256.div (UInt256.ofNat 1000000000000000000000000000000000000)
      (wExpPositiveWord (UInt256.sub ⟨0⟩ x))
  else wExpPositiveWord x

def divHalfDownValue (x d : Int) : Int := tickUnsigned (x + tickUnsigned (d - 1) / 2) / d

def tickPriceValue (tick : Nat) : Int :=
  let denominator := tickUnsigned (1000000000000000000 + wExpValue (tickExpArgument tick))
  tickUnsigned (divHalfDownValue
    (divHalfDownValue 1000000000000000000000000000000000000 denominator)
    100000000000 * 100000000000)

def tickPriceNumerator (tick : Nat) : UInt256 :=
  UInt256.ofNat 1000000000000000000000000000000000000 +
    UInt256.shiftRight (tickExpWord tick + UInt256.ofNat 999999999999999999) (UInt256.ofNat 1)

def tickPriceDenominator (tick : Nat) : UInt256 :=
  UInt256.ofNat 1000000000000000000 + tickExpWord tick

def tickPriceWord (tick : Nat) : UInt256 :=
  UInt256.mul
    (UInt256.div (UInt256.div (tickPriceNumerator tick) (tickPriceDenominator tick) +
      UInt256.ofNat 49999999999) (UInt256.ofNat 100000000000)) (UInt256.ofNat 100000000000)

def TickArithmeticFacts (tick : Nat) : Prop :=
  let x := tickExpArgument tick
  let w := tickExpArgumentWord (UInt256.ofNat tick)
  (x < 0 →
    UInt256.isZero (UInt256.slt w ⟨0⟩) = ⟨0⟩ ∧
    UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ w) ⟨0⟩) ≠ ⟨0⟩ ∧
    wExpPositiveWord (UInt256.sub ⟨0⟩ w) ≠ ⟨0⟩ ∧
    0 ≤ tickSigned (0 - x) ∧ wExpPositiveValue (tickSigned (0 - x)) ≠ 0) ∧
  (0 ≤ x → UInt256.isZero (UInt256.slt w ⟨0⟩) ≠ ⟨0⟩) ∧
  wExpValue x = (tickExpWord tick).toNat ∧
  tickPriceDenominator tick ≠ ⟨0⟩ ∧
  tickUnsigned (1000000000000000000 + wExpValue x) ≠ 0 ∧
  tickPriceValue tick = (tickPriceWord tick).toNat

instance (tick : Nat) : Decidable (TickArithmeticFacts tick) := by
  unfold TickArithmeticFacts
  infer_instance

-- Concrete finite arithmetic certificate. It checks only the pure integer/word formulas,
-- sign branches, and nonzero divisors for the 6745 tick values accepted by the contract.
private theorem tickArithmeticTable : ∀ tick : Fin 6745, TickArithmeticFacts tick.val := by
  native_decide

theorem tickArithmeticFacts (tick : UInt256) (h : tick.toNat ≤ 6744) :
    TickArithmeticFacts tick.toNat := tickArithmeticTable ⟨tick.toNat, by omega⟩

end Benchmarks.Midnight
