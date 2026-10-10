import Benchmarks.UniswapV4PoolManager.WordSignextend16
import Benchmarks.UniswapV4PoolManager.WordSignextend24
import Benchmarks.UniswapV4PoolManager.SignedNormalizeRange
import Benchmarks.UniswapV4PoolManager.WordNarrowCast

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickPositionWord (tick : UInt256) : UInt256 :=
  UInt256.signextend (UInt256.ofNat 1) (UInt256.sar (UInt256.ofNat 8) (UInt256.signextend (UInt256.ofNat 2) tick))
def tickPositionBit (tick : UInt256) : UInt256 := UInt256.land tick (UInt256.ofNat 255)
def tickPositionValues (tick : UInt256) : List Value :=
  [.int (EVM.signed (tickPositionWord tick)), .int (Int.ofNat (tickPositionBit tick).toNat)]

theorem tickPositionWord_fits (tick : UInt256) : signedFits ⟨16, by decide⟩ (EVM.signed (tickPositionWord tick)) := by
  rw [tickPositionWord, ← normalizeSigned16Word]
  exact normalizeSigned_fits _ _

theorem tickPositionBit_fits (tick : UInt256) : (tickPositionBit tick).toNat < 256 :=
  u256LandMaskToNatLtOfToNat _ (UInt256.ofNat 255) (bits := 8) rfl

theorem tickPositionValues_signextend (tick : UInt256) :
    tickPositionValues (UInt256.signextend (UInt256.ofNat 2) tick) = tickPositionValues tick := by
  simp only [tickPositionValues, tickPositionWord, tickPositionBit, signextend24_idempotent, signextend24_lowByte]

end Benchmarks.UniswapV4PoolManager
