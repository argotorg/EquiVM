import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsMemory
import Benchmarks.EAS.Attester.WordSequenceMemory

/-! A short prefix followed by packed words, including overlapping prefix stores. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def wordPrefixMemory (mem : ByteArray) (ptr : Nat) (headWord : UInt256) (width : Nat)
    (words : List UInt256) : ByteArray :=
  wordSequenceMemory (writeWord mem ptr headWord) (ptr + width) words

theorem wordPrefixMemory_size (mem : ByteArray) (ptr : Nat) (headWord : UInt256)
    {width : Nat} {words : List UInt256} (hwidth : width ≤ 32) (hne : words ≠ []) :
    (wordPrefixMemory mem ptr headWord width words).size =
      max mem.size (ptr + width + 32 * words.length) := by
  rw [wordPrefixMemory, wordSequenceMemory_size words (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_size]
  have hlen : 0 < words.length := List.length_pos_iff.mpr hne
  omega

theorem wordPrefixMemory_read (mem : ByteArray) (ptr : Nat) (headWord : UInt256)
    {width : Nat} (hpos : 0 < width) (hwidth : width ≤ 32) (words : List UInt256) :
    (wordPrefixMemory mem ptr headWord width words).readWithPadding ptr
      (width + 32 * words.length) = headWord.toByteArray.extract 0 width ++ wordBytes words := by
  have hmem : ptr + width ≤ (writeWord mem ptr headWord).size := by
    rw [writeWord_sparse_size]; omega
  unfold wordPrefixMemory
  rw [readWithPadding_split _ _ _ _ (by rw [wordSequenceMemory_size words hmem]; omega),
    wordSequenceMemory_read_below_unbounded _ _ _ _ _ hmem (le_refl _),
    wordSequenceMemory_read]
  congr 1
  simpa only [Nat.add_zero, Nat.zero_add] using
    writeWord_sparse_read_window mem ptr 0 width headWord (by omega) hpos (by omega)

theorem wordPrefixMemory_prefix (mem : ByteArray) (ptr : Nat) (headWord : UInt256)
    (width : Nat) (words : List UInt256) :
    MemoryPrefix mem (wordPrefixMemory mem ptr headWord width words) ptr :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
    ((wordSequenceMemory_prefix _ _ _).mono (by omega))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
