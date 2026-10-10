import Benchmarks.Morpho.MetaMorphoV1_1.DomainHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.PackedWordsMemory

/-! The allocated five-word preimage used when the domain cache is stale. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

def domainHashMemory (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) (mem : ByteArray)
    (free : Nat) : ByteArray :=
  writeWord (writeWord (wordSequenceMemory mem (free + 32) (domainWords v I)) free ⟨160⟩)
    64 (UInt256.ofNat (free + 192))

theorem domainHashMemory_eq (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) :
    domainHashMemory v I mem free = packedWordsMemory mem free (domainWords v I) := by
  simp only [domainHashMemory, packedWordsMemory, domainWords, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]
  rfl

theorem domainHashMemory_size (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) : free + 192 ≤ (domainHashMemory v I mem free).size := by
  rw [domainHashMemory_eq]
  simpa only [domainWords, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceMul, Nat.add_assoc] using
    packedWordsMemory_size mem free (domainWords v I) (by simp [domainWords])

theorem domainHashMemory_free (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) :
    memLoad (UInt256.ofNat 64) (domainHashMemory v I mem free) = UInt256.ofNat (free + 192) :=
  memLoad_write_same _ _ _ _ rfl

theorem domainHashMemory_length (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) (hlo : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (domainHashMemory v I mem free) = ⟨160⟩ := by
  unfold domainHashMemory
  rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
    (by rw [UInt256.toNat_ofNat_of_lt hfit, writeWord_sparse_size]; omega)
    (.inr (by rw [UInt256.toNat_ofNat_of_lt hfit]; exact hlo))]
  exact memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt hfit)

theorem domainHashMemory_read (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) (hlo : 96 ≤ free) :
    (domainHashMemory v I mem free).readWithPadding (free + 32) 160 =
      wordBytes (domainWords v I) := by
  rw [domainHashMemory_eq]
  exact packedWordsMemory_read mem free (domainWords v I) hlo (by simp [domainWords])

end Benchmarks.Morpho.MetaMorphoV1_1
