import Benchmarks.UniswapV4PoolManager.FullMathGeneralWords

open Ethereum
namespace Benchmarks.UniswapV4PoolManager

def fullMathRoundFits (a b d : UInt256) : Prop :=
  fullMathFits a b d ∧
    (fullMathRemainder a b d = ⟨0⟩ ∨ fullMathWord a b d + ⟨1⟩ ≠ ⟨0⟩)
instance (a b d : UInt256) : Decidable (fullMathRoundFits a b d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def fullMathRoundWord (a b d : UInt256) : UInt256 :=
  if fullMathRemainder a b d = ⟨0⟩ then fullMathWord a b d else fullMathWord a b d + ⟨1⟩

end Benchmarks.UniswapV4PoolManager
