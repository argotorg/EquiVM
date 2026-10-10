import Benchmarks.UniswapV4PoolManager.TickLiquidityWords
import Benchmarks.UniswapV4PoolManager.LiquidityAddSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickGrossAfterInt (packed : UInt256) (delta : Int) : Int := Int.ofNat (tickGrossWord packed).toNat+delta
def tickFlipped (packed : UInt256) (delta : Int) : Bool :=
  decide (tickGrossAfterInt packed delta = 0) != decide (Int.ofNat (tickGrossWord packed).toNat = 0)

-- LIBRARY CANDIDATE: EVM's zero test is the Boolean word for equality to zero.
theorem wordIsZero_fromBool (w : UInt256) :
    UInt256.isZero w = UInt256.fromBool (decide (w = ⟨0⟩)) := by
  by_cases hz : w = ⟨0⟩
  · rw [hz]; rfl
  · rw [isZero_eq_zero_of_ne hz, decide_eq_false hz]; rfl

-- LIBRARY CANDIDATE: compare two zero tests and retain a canonical Boolean word.
theorem wordZeroTestsDiffer (a b : UInt256) :
    UInt256.isZero (UInt256.eq (UInt256.isZero a) (UInt256.isZero b)) =
      UInt256.fromBool (decide (a = ⟨0⟩) != decide (b = ⟨0⟩)) := by
  rw [wordIsZero_fromBool a, wordIsZero_fromBool b]
  cases decide (a = ⟨0⟩) <;> cases decide (b = ⟨0⟩) <;> decide +kernel

theorem tickGrossAfter_value {packed : UInt256} {delta : Int}
    (hf : liquidityAddFits (tickGrossWord packed) delta) :
    Int.ofNat (EVM.wordOfInt (tickGrossAfterInt packed delta)).toNat = tickGrossAfterInt packed delta := by
  rw [wordOfIntResidue]
  apply Int.emod_eq_of_lt (show 0 ≤ tickGrossAfterInt packed delta from hf.1)
  change tickGrossAfterInt packed delta < (2^256 : Int)
  have hh : tickGrossAfterInt packed delta < (2^128 : Int) := hf.2
  omega

theorem tickGrossAfter_bound {packed : UInt256} {delta : Int}
    (hf : liquidityAddFits (tickGrossWord packed) delta) :
    (EVM.wordOfInt (tickGrossAfterInt packed delta)).toNat < 2^128 := by
  have he := tickGrossAfter_value hf
  have hh : tickGrossAfterInt packed delta < (2^128 : Int) := hf.2
  simp only [Int.ofNat_eq_natCast] at he
  omega

theorem tickFlipped_compiled {packed : UInt256} {delta : Int}
    (hf : liquidityAddFits (tickGrossWord packed) delta) :
    UInt256.isZero (UInt256.eq (UInt256.isZero (EVM.wordOfInt (tickGrossAfterInt packed delta)))
      (UInt256.isZero (tickGrossWord packed))) = UInt256.fromBool (tickFlipped packed delta) := by
  have hzero (w : UInt256) : w = ⟨0⟩ ↔ Int.ofNat w.toNat = 0 := by
    constructor
    · rintro rfl; rfl
    · intro he
      apply uint256_toNat_eq_zero
      simp only [Int.ofNat_eq_natCast] at he
      omega
  rw [wordZeroTestsDiffer]
  simp only [hzero, tickGrossAfter_value hf, tickFlipped]

end Benchmarks.UniswapV4PoolManager
