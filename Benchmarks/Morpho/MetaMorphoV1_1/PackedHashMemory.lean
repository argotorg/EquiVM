import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Reasoning.HeapMemory

/-! Memory facts for the two-word packed buffers used in Morpho storage-slot hashes. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: packed two-word buffers, including their length and allocation cursor.
def packedPairMem (mem : ByteArray) (ptr first second : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem (ptr + ⟨32⟩).toNat first)
    (ptr + ⟨64⟩).toNat second) ptr.toNat ⟨64⟩

def packedPairAllocMem (mem : ByteArray) (ptr first second : UInt256) : ByteArray :=
  writeWord (packedPairMem mem ptr first second) 64 (ptr + ⟨96⟩)

theorem packedPairMem_size (mem : ByteArray) (ptr first second : UInt256)
    (hfit : ptr.toNat + 64 < UInt256.size) :
    (packedPairMem mem ptr first second).size = max mem.size (ptr.toNat + 96) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 hfit
  simp only [packedPairMem, writeWord_sparse_size, h32, h64]
  omega

theorem packedPairMem_length (mem : ByteArray) (ptr first second : UInt256) :
    (packedPairMem mem ptr first second).readWithPadding ptr.toNat 32 =
      (⟨64⟩ : UInt256).toByteArray :=
  writeWord_sparse_read_back _ _ _

theorem packedPairMem_first (mem : ByteArray) (ptr first second : UInt256)
    (hfit : ptr.toNat + 64 < UInt256.size) :
    (packedPairMem mem ptr first second).readWithPadding (ptr + ⟨32⟩).toNat 32 =
      first.toByteArray := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 hfit
  rw [packedPairMem, writeWord_sparse_read_preserved _ _ _ _ (Or.inr
    ⟨by rw [h32], by simp only [writeWord_sparse_size, h32, h64]; omega⟩)]
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨by rw [h32, h64], by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem packedPairMem_second (mem : ByteArray) (ptr first second : UInt256)
    (hfit : ptr.toNat + 64 < UInt256.size) :
    (packedPairMem mem ptr first second).readWithPadding (ptr + ⟨64⟩).toNat 32 =
      second.toByteArray := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 hfit
  rw [packedPairMem, writeWord_sparse_read_preserved _ _ _ _ (Or.inr
    ⟨by rw [h64]; omega, by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem packedPairMem_free (mem : ByteArray) (ptr first second : UInt256)
    (hin : 96 ≤ mem.size) (hlower : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 64 < UInt256.size) :
    (packedPairMem mem ptr first second).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 hfit
  rw [packedPairMem, writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨hlower, by simp only [writeWord_sparse_size]; omega⟩)]
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨by rw [h64]; omega, by rw [writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by rw [h32]; omega, hin⟩)

theorem packedPairAllocMem_size (mem : ByteArray) (ptr first second : UInt256)
    (hfit : ptr.toNat + 64 < UInt256.size) :
    (packedPairAllocMem mem ptr first second).size = max mem.size (ptr.toNat + 96) := by
  rw [packedPairAllocMem, writeWord_sparse_size, packedPairMem_size _ _ _ _ hfit]
  omega

theorem packedPairAllocMem_read (mem : ByteArray) (ptr first second : UInt256)
    (hfit : ptr.toNat + 64 < UInt256.size) (read : Nat)
    (hlower : 96 ≤ read) (hin : read + 32 ≤ ptr.toNat + 96) :
    (packedPairAllocMem mem ptr first second).readWithPadding read 32 =
      (packedPairMem mem ptr first second).readWithPadding read 32 := by
  apply writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨hlower, ?_⟩)
  rw [packedPairMem_size _ _ _ _ hfit]
  exact le_trans hin (Nat.le_max_right _ _)

theorem packedPairAllocMem_length (mem : ByteArray) (ptr first second : UInt256)
    (hlower : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 64 < UInt256.size) :
    memLoad ptr (packedPairAllocMem mem ptr first second) = ⟨64⟩ := by
  apply loadedWord_of_read
  · rw [packedPairAllocMem_size _ _ _ _ hfit]; omega
  · rw [packedPairAllocMem_read _ _ _ _ hfit _ hlower (by omega), packedPairMem_length]

theorem packedPairAllocMem_free (mem : ByteArray) (ptr first second : UInt256) :
    memLoad ⟨64⟩ (packedPairAllocMem mem ptr first second) = ptr + ⟨96⟩ := by
  apply loadedWord_of_read
  · change 64 + 32 ≤ (writeWord _ 64 _).size
    rw [writeWord_sparse_size]
    exact Nat.le_max_right _ _
  · exact writeWord_sparse_read_back _ _ _

attribute [local irreducible] packedPairMem packedPairAllocMem

theorem packedPairAllocMem_hash (mem : ByteArray) (ptr first second : UInt256)
    (hlower : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 64 < UInt256.size) :
    keccakWord (ptr + ⟨32⟩) ⟨64⟩ (packedPairAllocMem mem ptr first second) =
      solcMappingSlot second first := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 hfit
  have hf : (packedPairAllocMem mem ptr first second).readWithPadding (ptr + ⟨32⟩).toNat 32 =
      first.toByteArray := by
    rw [packedPairAllocMem_read mem ptr first second hfit (ptr + ⟨32⟩).toNat
      (by rw [h32]; omega) (by rw [h32]; omega)]
    exact packedPairMem_first mem ptr first second hfit
  have hs : (packedPairAllocMem mem ptr first second).readWithPadding (ptr + ⟨64⟩).toNat 32 =
      second.toByteArray := by
    rw [packedPairAllocMem_read mem ptr first second hfit (ptr + ⟨64⟩).toNat
      (by rw [h64]; omega) (by rw [h64])]
    exact packedPairMem_second mem ptr first second hfit
  rw [h32] at hf
  rw [h64] at hs
  have hread : (packedPairAllocMem mem ptr first second).readWithPadding (ptr + ⟨32⟩).toNat
      64 = first.toByteArray ++ second.toByteArray := by
    rw [h32, byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide)
      (by rw [packedPairAllocMem_size _ _ _ _ hfit]; omega), hf]
    simpa only [Nat.add_assoc] using congrArg (fun tail ↦ first.toByteArray ++ tail) hs
  unfold keccakWord
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((packedPairAllocMem mem ptr first second).readWithPadding (ptr + ⟨32⟩).toNat 64))) = _
  rw [hread]
  exact mappingSlot_single first second

end Benchmarks.Morpho.MetaMorphoV1_1
