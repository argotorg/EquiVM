import Benchmarks.Morpho.MetaMorphoV1_1.ShortStringSource
import Benchmarks.Morpho.MetaMorphoV1_1.MemoryArrayData
import Benchmarks.EAS.Attester.UnboundedMemory

/-! The allocated length word and payload of an immutable short string. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def shortStringInitMemory (mem calldata : ByteArray) (free : Nat) : ByteArray :=
  calldata.write calldata.size
    (writeWord (writeWord mem 64 (UInt256.ofNat (free + 64))) free ⟨32⟩) (free + 32) 32

def shortStringMemory (mem calldata : ByteArray) (free : Nat) (word : UInt256) : ByteArray :=
  writeWord (writeWord (shortStringInitMemory mem calldata free) free (shortStringLength word))
    (free + 32) word

theorem shortStringInitMemory_size (mem calldata : ByteArray) (free : Nat) :
    (shortStringInitMemory mem calldata free).size = max (max mem.size 96) (free + 32) := by
  rw [shortStringInitMemory, writeOutsideSource_size _ _ _ _ _ (le_refl _),
    writeWord_sparse_size, writeWord_sparse_size]

theorem shortStringMemory_size (mem calldata : ByteArray) (free : Nat) (word : UInt256) :
    (shortStringMemory mem calldata free word).size = max (max mem.size 96) (free + 64) := by
  rw [shortStringMemory, writeWord_sparse_size, writeWord_sparse_size, shortStringInitMemory_size]
  omega

theorem shortStringMemory_length (mem calldata : ByteArray) (free : Nat) (word : UInt256)
    (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (shortStringMemory mem calldata free word) =
      shortStringLength word := by
  unfold shortStringMemory Reasoning.Theory.writeWord
  rw [memLoad_write_disjoint _ _ _ _
    (by rw [UInt256.toNat_ofNat_of_lt hfit, wordWrite_size]; omega)
    (.inl (by rw [UInt256.toNat_ofNat_of_lt hfit]))]
  exact memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt hfit)

theorem shortStringMemory_read (mem calldata : ByteArray) (free : Nat) (word : UInt256)
    (hvalid : shortStringValid word) :
    (shortStringMemory mem calldata free word).readWithPadding
      (free + 32) (shortStringLength word).toNat = shortStringBytes word := by
  have hlen : (shortStringLength word).toNat ≤ 31 := hvalid
  by_cases hz : (shortStringLength word).toNat = 0
  · simp only [hz, shortStringBytes, byteArray_readWithPadding_zero,
      byteArray_extract_empty_of_le _ (Nat.le_refl 0)]
  · simpa only [Nat.add_zero, Nat.zero_add] using writeWord_sparse_read_window
      (writeWord (shortStringInitMemory mem calldata free) free (shortStringLength word))
      (free + 32) 0 (shortStringLength word).toNat word (by omega) (by omega)
      (by omega)

theorem shortStringMemory_free_read (mem calldata : ByteArray) (free : Nat) (word : UInt256)
    (hlo : 96 ≤ free) :
    (shortStringMemory mem calldata free word).readWithPadding 64 32 =
      (UInt256.ofNat (free + 64)).toByteArray := by
  rw [shortStringMemory, writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
      rw [writeWord_sparse_size, shortStringInitMemory_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hlo, by
      rw [shortStringInitMemory_size]; omega⟩),
    shortStringInitMemory, writeOutsideSource_read _ _ _ _ _ _ (le_refl _)
      (by rw [writeWord_sparse_size, writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hlo, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_back]

theorem shortStringMemory_free (mem calldata : ByteArray) (free : Nat) (word : UInt256)
    (hlo : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (shortStringMemory mem calldata free word) =
      UInt256.ofNat (free + 64) := by
  apply loadedWord_of_read
  · rw [shortStringMemory_size]; change 96 ≤ _; omega
  · exact shortStringMemory_free_read mem calldata free word hlo

theorem shortStringMemory_prefix (mem calldata : ByteArray) (free : Nat) (word : UInt256) :
    MemoryPrefix mem (shortStringMemory mem calldata free word) free := by
  refine ⟨by rw [shortStringMemory_size]; omega, ?_⟩
  intro read hlo hhi hin
  rw [shortStringMemory, writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
      rw [writeWord_sparse_size, shortStringInitMemory_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hhi, by
      rw [shortStringInitMemory_size]; omega⟩),
    shortStringInitMemory, writeOutsideSource_read _ _ _ _ _ _ (le_refl _)
      (by rw [writeWord_sparse_size, writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hhi, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (.inr ⟨hlo, hin⟩)]

end Benchmarks.Morpho.MetaMorphoV1_1
