import Benchmarks.Safe.SetupEventMemory
import Benchmarks.Safe.CalldataBufferMemory
import Benchmarks.Safe.SetupCalldataFacts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def setupEventInitialMemory (cd : ByteArray) (n : Nat) : ByteArray :=
  setupEventMemory solcFreePtrMem 128 (calldataWords cd (setupOwnersStart cd) n)
    (calldataWord cd 36) (calldataWord cd 68) (calldataWord cd 132)

def setupOwnersAllocatedMemory (cd : ByteArray) (n : Nat) : ByteArray :=
  calldataBufferMemory cd (setupEventInitialMemory cd n) (setupOwnersStart cd)
    128 (32 * n) n (160 + 32 * n)

theorem setupEventInitialMemory_size (cd : ByteArray) (n : Nat) :
    (setupEventInitialMemory cd n).size = 288 + 32 * n := by
  rw [setupEventInitialMemory, setupEventMemory_size _ _ _ _ _ _
    (by rw [solcFreePtrMem_size]; decide), calldataWords_length]

theorem setupEventInitialMemory_free (cd : ByteArray) (n : Nat) :
    memLoad ⟨64⟩ (setupEventInitialMemory cd n) = ⟨128⟩ := by
  rw [setupEventInitialMemory, setupEventMemory_load _ _ _ _ _ _ _
    (by rw [solcFreePtrMem_size]; decide) (by decide)
    (.inl (by rw [solcFreePtrMem_size]; decide))]
  exact solcFreePtrMem_mload64

theorem setupEventInitialMemory_zero (cd : ByteArray) (n : Nat) :
    memLoad ⟨96⟩ (setupEventInitialMemory cd n) = ⟨0⟩ := by
  rw [setupEventInitialMemory, setupEventMemory_load _ _ _ _ _ _ _
    (by rw [solcFreePtrMem_size]; decide) (by decide)
    (.inr (by rw [solcFreePtrMem_size]; decide))]
  apply memLoad_of_wordRead
  rw [readPastMemory _ _ _ (by rw [solcFreePtrMem_size]; decide)]
  decide +kernel

theorem setupOwnersAllocatedMemory_size {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    (setupOwnersAllocatedMemory cd n).size = 288 + 32 * n := by
  rw [setupOwnersAllocatedMemory, calldataBufferMemory_size _ _ _ _ _ _ _
    (by rw [setupEventInitialMemory_size]; omega) hs, setupEventInitialMemory_size]
  omega

theorem setupOwnersAllocatedMemory_free {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    memLoad ⟨64⟩ (setupOwnersAllocatedMemory cd n) = UInt256.ofNat (160 + 32 * n) :=
  calldataBufferMemory_free _ _ _ _ _ _ _
    (by rw [setupEventInitialMemory_size]; omega) (by decide) hs

theorem setupOwnersAllocatedMemory_zero {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    memLoad ⟨96⟩ (setupOwnersAllocatedMemory cd n) = ⟨0⟩ := by
  have hp := calldataBufferMemory_preserved cd (setupEventInitialMemory cd n)
    (setupOwnersStart cd) 128 (32 * n) n (160 + 32 * n)
    (by rw [setupEventInitialMemory_size]; omega) hs
  have he : memLoad ⟨96⟩ (setupOwnersAllocatedMemory cd n) =
      memLoad ⟨96⟩ (setupEventInitialMemory cd n) := by
    rw [memLoadReadWord, memLoadReadWord]
    exact congrArg uInt256OfByteArray (hp.read 96 32 (by decide) (by decide)
      (by rw [setupEventInitialMemory_size]; omega))
  exact he.trans (setupEventInitialMemory_zero cd n)

theorem setupOwnersAllocatedMemory_words {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    WordArrayBuffer (setupOwnersAllocatedMemory cd n) 128
      (calldataWords cd (setupOwnersStart cd) n) :=
  calldataBufferMemory_words _ _ _ _ _ _ (by rw [setupEventInitialMemory_size]; omega) hs

end Benchmarks.Safe
