import Benchmarks.EAS.Attester.StructAllocMemory

/-! A byte-length header, packed words, and the allocator cursor used by hash preimages. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def packedWordsMemory (mem : ByteArray) (free : Nat) (words : List UInt256) : ByteArray :=
  writeWord (writeWord (wordSequenceMemory mem (free + 32) words)
    free (UInt256.ofNat (32 * words.length))) 64 (UInt256.ofNat (free + 32 + 32 * words.length))

theorem packedWordsMemory_size (mem : ByteArray) (free : Nat) (words : List UInt256)
    (hne : words ≠ []) : free + 32 + 32 * words.length ≤ (packedWordsMemory mem free words).size :=
      by
  rw [packedWordsMemory, writeWord_sparse_size, writeWord_sparse_size,
    wordSequenceMemory_size_nonempty _ _ _ hne]
  omega

theorem packedWordsMemory_free (mem : ByteArray) (free : Nat) (words : List UInt256) :
    memLoad (UInt256.ofNat 64) (packedWordsMemory mem free words) =
      UInt256.ofNat (free + 32 + 32 * words.length) :=
  memLoad_write_same _ _ _ _ rfl

theorem packedWordsMemory_length (mem : ByteArray) (free : Nat) (words : List UInt256)
    (hlo : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (packedWordsMemory mem free words) =
      UInt256.ofNat (32 * words.length) := by
  unfold packedWordsMemory
  rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
    (by rw [UInt256.toNat_ofNat_of_lt hfit, writeWord_sparse_size]; omega)
    (.inr (by rw [UInt256.toNat_ofNat_of_lt hfit]; exact hlo))]
  exact memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt hfit)

theorem packedWordsMemory_read (mem : ByteArray) (free : Nat) (words : List UInt256)
    (hlo : 96 ≤ free) (hne : words ≠ []) :
    (packedWordsMemory mem free words).readWithPadding (free + 32) (32 * words.length) =
      wordBytes words := by
  have hs : free + 32 + 32 * words.length ≤ (wordSequenceMemory mem (free + 32) words).size := by
    rw [wordSequenceMemory_size_nonempty _ _ _ hne]
    exact Nat.le_max_right _ _
  rw [packedWordsMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (.inr (by omega)),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hs (.inr (by omega))]
  exact wordSequenceMemory_read mem (free + 32) words

end Benchmarks.Morpho.MetaMorphoV1_1
