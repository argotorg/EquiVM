import Benchmarks.UniswapV4PoolManager.FullMathWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def fullMathFits (a b d : UInt256) : Prop := (fullMathHigh a b).toNat < d.toNat
instance (a b d : UInt256) : Decidable (fullMathFits a b d) := inferInstanceAs (Decidable (_ < _))
def fullMathRemainder (a b d : UInt256) : UInt256 := UInt256.mulMod a b d
def fullMathReducedLow (a b d : UInt256) : UInt256 :=
  UInt256.sub (fullMathLow a b) (fullMathRemainder a b d)
def fullMathReducedHigh (a b d : UInt256) : UInt256 :=
  UInt256.sub (fullMathHigh a b) (UInt256.gt (fullMathRemainder a b d) (fullMathLow a b))
def fullMathTwos (d : UInt256) : UInt256 := UInt256.land (UInt256.sub ⟨0⟩ d) d
def fullMathOdd (d : UInt256) : UInt256 := UInt256.div d (fullMathTwos d)
def fullMathTwosInverse (d : UInt256) : UInt256 :=
  UInt256.div (UInt256.sub ⟨0⟩ (fullMathTwos d)) (fullMathTwos d) + ⟨1⟩
def fullMathWide (a b d : UInt256) : UInt256 :=
  UInt256.lor (UInt256.div (fullMathReducedLow a b d) (fullMathTwos d))
    (UInt256.mul (fullMathReducedHigh a b d) (fullMathTwosInverse d))
def fullMathInverseStep (d inv : UInt256) : UInt256 :=
  UInt256.mul (UInt256.sub ⟨2⟩ (UInt256.mul d inv)) inv
def fullMathInverseIter (d inv : UInt256) : Nat → UInt256
  | 0 => inv
  | n+1 => fullMathInverseIter d (fullMathInverseStep d inv) n
def fullMathInverse (d : UInt256) : UInt256 :=
  fullMathInverseIter d (UInt256.xor (UInt256.mul ⟨3⟩ d) ⟨2⟩) 6
def fullMathWord (a b d : UInt256) : UInt256 :=
  if fullMathHigh a b = ⟨0⟩ then UInt256.div (fullMathLow a b) d
  else UInt256.mul (fullMathWide a b d) (fullMathInverse (fullMathOdd d))

theorem fullMathInverse_one : fullMathInverse ⟨1⟩ = ⟨1⟩ := by decide +kernel

theorem fullMathFits_ne {a b d : UInt256} (h : fullMathFits a b d) : d ≠ ⟨0⟩ := by
  intro hz
  unfold fullMathFits at h
  rw [hz] at h
  exact Nat.not_lt_zero _ h

end Benchmarks.UniswapV4PoolManager
