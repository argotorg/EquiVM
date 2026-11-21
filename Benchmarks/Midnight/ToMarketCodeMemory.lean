import Benchmarks.Midnight.ToMarketMemory
import Benchmarks.Midnight.CodeStorage
import Benchmarks.Midnight.ReturnData
import Benchmarks.Midnight.MemoryBytes

/-! The bytes header and payload copied from the account that stores a market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def toMarketCodeFreePtr (len : UInt256) : UInt256 :=
  returnDataPtr ⟨1088⟩ len.toNat

def toMarketCodeBase (id len : UInt256) : ByteArray :=
  writeWord (writeWord (toMarketInitialMemory id) 64 (toMarketCodeFreePtr len)) 1088 len

def toMarketCodeMemory (accounts : AccountMap) (id : UInt256) : ByteArray :=
  toMarketCodeBase id (extCodeSizeWord accounts id) ++ externalCodePrefix accounts id

theorem toMarketCodeBase_properties (id len : UInt256) :
    (toMarketCodeBase id len).size = 1120 ∧
    memLoad (UInt256.ofNat 1088) (toMarketCodeBase id len) = len ∧
    memLoad (UInt256.ofNat 64) (toMarketCodeBase id len) = toMarketCodeFreePtr len ∧
    memLoad (UInt256.ofNat 800) (toMarketCodeBase id len) = ⟨0⟩ := by
  rcases toMarketInitialMemory_properties id with ⟨hs, hz, _, _⟩
  have hs0 : (writeWord (toMarketInitialMemory id) 64 (toMarketCodeFreePtr len)).size = 1088 := by
    rw [writeWord_sparse_size, hs]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMarketCodeBase, writeWord_sparse_size, hs0]; rfl
  · exact memLoad_writeWord _ (UInt256.ofNat 1088) len
  · rw [toMarketCodeBase, memLoad_writeWord_preserved _ _ _ _ (by rw [hs0]; decide)
      (Or.inl (by decide))]
    exact memLoad_writeWord _ (UInt256.ofNat 64) _
  · rw [toMarketCodeBase, memLoad_writeWord_preserved _ _ _ _ (by rw [hs0]; decide)
      (Or.inl (by decide)), memLoad_writeWord_preserved _ _ _ _ (by rw [hs]; decide)
      (Or.inr (by decide)), hz]

theorem toMarketCodeCopy_eq (accounts : AccountMap) (id : UInt256) :
    (externalCode accounts id).write 0 (toMarketCodeBase id (extCodeSizeWord accounts id))
      1120 (extCodeSizeWord accounts id).toNat = toMarketCodeMemory accounts id := by
  have hs := (toMarketCodeBase_properties id (extCodeSizeWord accounts id)).1
  by_cases hzero : (extCodeSizeWord accounts id).toNat = 0
  · have he : (externalCode accounts id).extract 0 0 = ByteArray.empty := by
      apply ByteArray.ext; simp
    simp only [toMarketCodeMemory, externalCodePrefix, hzero, ByteArray.write, if_true,
      he, ByteArray.append_empty]
  · rw [← hs, write_at_end_eq_from _ _ 0 _ hzero (by
      rw [Nat.zero_add, extCodeSizeWord_externalCode]; exact Nat.mod_le _ _)]
    simp only [Nat.zero_add, toMarketCodeMemory, externalCodePrefix]

theorem toMarketCodeMemory_size (accounts : AccountMap) (id : UInt256) :
    (toMarketCodeMemory accounts id).size = 1120 + (extCodeSizeWord accounts id).toNat := by
  rw [toMarketCodeMemory, ByteArray.size_append, (toMarketCodeBase_properties id _).1,
    externalCodePrefix_size]

theorem toMarketCodeMemory_properties (accounts : AccountMap) (id : UInt256) :
    memLoad (UInt256.ofNat 1088) (toMarketCodeMemory accounts id) = extCodeSizeWord accounts id ∧
    memLoad (UInt256.ofNat 64) (toMarketCodeMemory accounts id) =
      toMarketCodeFreePtr (extCodeSizeWord accounts id) ∧
    memLoad (UInt256.ofNat 800) (toMarketCodeMemory accounts id) = ⟨0⟩ := by
  rcases toMarketCodeBase_properties id (extCodeSizeWord accounts id) with ⟨hs, hl, hf, hz⟩
  unfold toMarketCodeMemory
  exact ⟨(memLoad_append_left _ _ _ (by rw [hs]; decide)).trans hl,
    (memLoad_append_left _ _ _ (by rw [hs]; decide)).trans hf,
    (memLoad_append_left _ _ _ (by rw [hs]; decide)).trans hz⟩

theorem toMarketCodeMemory_bytes (accounts : AccountMap) (id : UInt256)
    (hb : (extCodeSizeWord accounts id).toNat < 2^64) :
    MemoryBytes (toMarketCodeMemory accounts id) 1120 (externalCodePrefix accounts id) := by
  have hs := (toMarketCodeBase_properties id (extCodeSizeWord accounts id)).1
  simpa only [hs] using MemoryBytes.append (toMarketCodeBase id (extCodeSizeWord accounts id))
    (externalCodePrefix accounts id) (by rw [hs, externalCodePrefix_size]; change _ < 2^256; omega)

end Benchmarks.Midnight
