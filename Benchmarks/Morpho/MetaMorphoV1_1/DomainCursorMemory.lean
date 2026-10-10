import Benchmarks.Morpho.MetaMorphoV1_1.DomainCacheRoutines

/-! Memory cursor facts for both branches of the EIP-712 domain cache. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

def domainSeparatorCursor (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) (free : Nat) : Nat :=
  if domainCacheValid v I then free else free + 192

theorem domainSeparatorCursor_bounds (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (free : Nat) :
    free ≤ domainSeparatorCursor v I free ∧ domainSeparatorCursor v I free ≤ free + 192 := by
  unfold domainSeparatorCursor
  split <;> omega

theorem domainSeparatorMemory_free (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) :
    memLoad (UInt256.ofNat 64) (domainSeparatorMemory v I mem free) =
      UInt256.ofNat (domainSeparatorCursor v I free) := by
  unfold domainSeparatorMemory domainSeparatorCursor
  split
  · exact hfree
  · exact domainHashMemory_free _ _ _ _

theorem domainSeparatorMemory_size (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) (hsize : 96 ≤ mem.size) :
    96 ≤ (domainSeparatorMemory v I mem free).size := by
  unfold domainSeparatorMemory
  split
  · exact hsize
  · have := domainHashMemory_size v I mem free
    omega

end Benchmarks.Morpho.MetaMorphoV1_1
