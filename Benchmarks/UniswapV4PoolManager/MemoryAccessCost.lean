import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: telescope the expansion costs of an arbitrary sequence of memory accesses.
def memoryAccessWords (aw : UInt256) : List (UInt256 × UInt256) → UInt256
  | [] => aw
  | (off, len) :: rest => memoryAccessWords (M aw off len) rest

def memoryAccessCost (aw : UInt256) : List (UInt256 × UInt256) → Nat
  | [] => 0
  | (off, len) :: rest => memExpansionCost aw off len + memoryAccessCost (M aw off len) rest

theorem memoryAccessCost_covers (aw : UInt256) (accesses : List (UInt256 × UInt256)) :
    Cₘ (memoryAccessWords aw accesses) ≤ Cₘ aw + memoryAccessCost aw accesses := by
  induction accesses generalizing aw with
  | nil => exact Nat.le_refl _
  | cons access rest ih =>
    rcases access with ⟨off, len⟩
    have hi := ih (M aw off len)
    have hs : Cₘ (M aw off len) ≤ Cₘ aw + memExpansionCost aw off len := by
      dsimp only [memExpansionCost]
      omega
    change Cₘ (memoryAccessWords (M aw off len) rest) ≤
      Cₘ aw + (memExpansionCost aw off len + memoryAccessCost (M aw off len) rest)
    omega

end Benchmarks.UniswapV4PoolManager
