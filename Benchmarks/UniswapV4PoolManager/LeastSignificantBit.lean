import Benchmarks.UniswapV4PoolManager.WordLowBitPower
import Benchmarks.UniswapV4PoolManager.WordShiftSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def lsbLowBit (x : UInt256) : UInt256 := UInt256.land (UInt256.sub ⟨0⟩ x) x
def lsbMultiplier : UInt256 := UInt256.ofNat 0xb6db6db6ddddddddd34d34d349249249210842108c6318c639ce739cffffffff
def lsbHighTable : UInt256 := UInt256.ofNat 0x8040405543005266443200005020610674053026020000107506200176117077
def lsbLowTable : UInt256 := UInt256.ofNat 0x001f0d1e100c1d070f090b19131c1706010e11080a1a141802121b1503160405
def lsbIndex (low : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.shiftRight (UInt256.mul low lsbMultiplier) (UInt256.ofNat 250)) (UInt256.ofNat 2)
def lsbHigh (low : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.shiftRight (UInt256.shiftLeft lsbHighTable (lsbIndex low)) (UInt256.ofNat 252)) (UInt256.ofNat 5)
def lsbDenominator (low : UInt256) : UInt256 := UInt256.shiftRight low (lsbHigh low)
def lsbLowIndex (low : UInt256) : UInt256 :=
  UInt256.land (UInt256.div (UInt256.ofNat 0xd76453e0) (lsbDenominator low)) (UInt256.ofNat 31)
def lsbResult (low : UInt256) : UInt256 :=
  UInt256.lor (UInt256.byteAt (lsbLowIndex low) lsbLowTable) (lsbHigh low)
def leastSignificantBit (x : UInt256) : UInt256 := lsbResult (lsbLowBit x)

def lsbCompiledIndex (low : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight (UInt256.mul low lsbMultiplier) (UInt256.ofNat 248)) (UInt256.ofNat 252)
def lsbCompiledHigh (low : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight (UInt256.shiftLeft lsbHighTable (lsbCompiledIndex low)) (UInt256.ofNat 247)) (UInt256.ofNat 480)
def lsbCompiledResult (low : UInt256) : UInt256 :=
  UInt256.lor (UInt256.byteAt
    (UInt256.land (UInt256.div (UInt256.ofNat 0xd76453e0) (UInt256.shiftRight low (lsbCompiledHigh low))) (UInt256.ofNat 31))
    lsbLowTable) (lsbCompiledHigh low)

-- Concrete lookup tables, checked at all 256 possible isolated bit values.
theorem lsbTables : ∀ j : Fin 256,
    (lsbIndex (UInt256.ofNat (2^j.val))).toNat < 256 ∧
    lsbDenominator (UInt256.ofNat (2^j.val)) ≠ ⟨0⟩ ∧
    lsbResult (UInt256.ofNat (2^j.val)) = UInt256.ofNat j.val ∧
    lsbCompiledResult (UInt256.ofNat (2^j.val)) = UInt256.ofNat j.val := by
  native_decide

theorem lsbIndex_lt {x : UInt256} (hx : x ≠ ⟨0⟩) : (lsbIndex (lsbLowBit x)).toNat < 256 := by
  obtain ⟨j, he⟩ := wordLowBit_power x hx
  change lsbLowBit x = _ at he
  rw [he]
  exact (lsbTables j).1

theorem lsbDenominator_ne {x : UInt256} (hx : x ≠ ⟨0⟩) : lsbDenominator (lsbLowBit x) ≠ ⟨0⟩ := by
  obtain ⟨j, he⟩ := wordLowBit_power x hx
  change lsbLowBit x = _ at he
  rw [he]
  exact (lsbTables j).2.1

theorem leastSignificantBit_lt_256 {x : UInt256} (hx : x ≠ ⟨0⟩) :
    (leastSignificantBit x).toNat < 256 := by
  obtain ⟨j, he⟩ := wordLowBit_power x hx
  change lsbLowBit x = _ at he
  rw [leastSignificantBit, he, (lsbTables j).2.2.1,
    UInt256.toNat_ofNat_of_lt (show j.val < UInt256.size by have := j.isLt; change j.val < 2^256; omega)]
  exact j.isLt

theorem lsbCompiledResult_eq {x : UInt256} (hx : x ≠ ⟨0⟩) :
    lsbCompiledResult (lsbLowBit x) = leastSignificantBit x := by
  obtain ⟨j, he⟩ := wordLowBit_power x hx
  change lsbLowBit x = _ at he
  rw [leastSignificantBit, he, (lsbTables j).2.2.1, (lsbTables j).2.2.2]

end Benchmarks.UniswapV4PoolManager
