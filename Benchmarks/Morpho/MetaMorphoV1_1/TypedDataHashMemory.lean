import Benchmarks.Morpho.MetaMorphoV1_1.TypedDataHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.WordPrefixMemory

/-! The two-byte EIP-712 envelope written immediately before its two words. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def typedDataPrefixWord : UInt256 := UInt256.shiftLeft ⟨6401⟩ ⟨240⟩

def typedDataHashMemory (mem : ByteArray) (ptr : Nat) (domain structHash : UInt256) : ByteArray :=
  SourceMemory.wordPrefixMemory mem ptr typedDataPrefixWord 2 [domain, structHash]

theorem typedDataHashMemory_read (mem : ByteArray) (ptr : Nat) (domain structHash : UInt256) :
    (typedDataHashMemory mem ptr domain structHash).readWithPadding ptr 66 =
      typedDataPreimage domain structHash := by
  have hp : typedDataPrefixWord.toByteArray.extract 0 2 =
      ([25, 1] : List UInt8).toByteArray := by native_decide
  simpa only [typedDataHashMemory, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceMul, hp, wordBytes, ByteArray.append_empty, typedDataPreimage,
    ByteArray.append_assoc] using
    SourceMemory.wordPrefixMemory_read mem ptr typedDataPrefixWord (width := 2)
      (by decide) (by decide) [domain, structHash]

theorem typedDataHashMemory_free (mem : ByteArray) (ptr : Nat) (domain structHash : UInt256)
    (hlo : 96 ≤ ptr) (hsize : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (typedDataHashMemory mem ptr domain structHash) = memLoad ⟨64⟩ mem := by
  simp only [typedDataHashMemory, SourceMemory.wordPrefixMemory, wordSequenceMemory]
  rw [memLoad_write_above _ _ _ _
      (by rw [writeWord_sparse_size, writeWord_sparse_size]; exact le_trans hsize (by omega))
      (by exact le_trans hlo (by omega)),
    memLoad_write_above _ _ _ _
      (by rw [writeWord_sparse_size]; exact le_trans hsize (by omega))
      (by exact le_trans hlo (by omega))]
  exact memLoad_write_above mem ⟨64⟩ ptr typedDataPrefixWord hsize hlo

end Benchmarks.Morpho.MetaMorphoV1_1
