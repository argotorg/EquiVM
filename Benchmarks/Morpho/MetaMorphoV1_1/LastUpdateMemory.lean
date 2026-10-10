import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSlotRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesMemoryPrefix

/-! The last-update reader's argument array and preservation of the earlier heap. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

theorem lastUpdateArrayMem_view (mem calldata : ByteArray) (ptr id : UInt256)
    (hlo : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 160 < 2 ^ 64) :
    (ptr + ⟨96⟩).toNat + 64 ≤ (lastUpdateArrayMem mem calldata ptr id).size ∧
      memLoad (ptr + ⟨96⟩) (lastUpdateArrayMem mem calldata ptr id) = ⟨1⟩ ∧
      memLoad ((ptr + ⟨96⟩) + ⟨32⟩) (lastUpdateArrayMem mem calldata ptr id) =
        lastUpdateSlot id ∧
      memLoad ⟨64⟩ (lastUpdateArrayMem mem calldata ptr id) = nextCursor ptr ⟨160⟩ := by
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat ptr 96
      (lt_trans (by omega : ptr.toNat + 96 < 2 ^ 64) (by decide))
  have hsmall : (ptr + ⟨96⟩).toNat + 32 < UInt256.size := by
    rw [h96]
    exact lt_trans (by omega : ptr.toNat + 96 + 32 < 2 ^ 64) (by decide)
  have hsize : (ptr + ⟨96⟩).toNat + 64 ≤ (lastUpdateArrayMem mem calldata ptr id).size := by
    rw [lastUpdateArrayMem, morphoArrayMem_size _ _ _ _ hsmall]
    omega
  refine ⟨hsize, ?_, ?_, ?_⟩
  · exact loadedWord_of_read (by omega) (morphoArrayMem_length _ _ _ _ hsmall)
  · apply loadedWord_of_read
    · rw [show ((ptr + ⟨96⟩) + ⟨32⟩).toNat = (ptr + ⟨96⟩).toNat + 32 from
        uadd_word_ofNat_toNat _ _ hsmall]
      omega
    · exact morphoArrayMem_value _ _ _ _
  · have hread := morphoArrayMem_free (packedPairAllocMem mem ptr id ⟨3⟩) calldata
      (ptr + ⟨96⟩) (lastUpdateSlot id) (by rw [h96]; omega) hsmall
    rw [u256_add_assoc] at hread
    exact loadedWord_of_read (by change 64 + 32 ≤ _; rw [h96] at hsize; omega) hread

theorem lastUpdateArrayMem_prefix (mem calldata : ByteArray) (ptr id : UInt256)
    (hfit : ptr.toNat + 128 < UInt256.size) :
    MemoryPrefix mem (lastUpdateArrayMem mem calldata ptr id) ptr.toNat := by
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat ptr 96 (by omega)
  exact (packedPairAllocMem_prefix _ _ _ _ (by omega)).trans
    ((morphoArrayMem_prefix _ _ _ _ (by rw [h96]; omega)).mono (by rw [h96]; omega))

theorem lastUpdateReadMemory_prefix (mem calldata out : ByteArray) (ptr id : UInt256)
    (hfit : ptr.toNat + 160 < 2 ^ 64)
    (hraw : (nextCursor ptr ⟨160⟩).toNat ≤
      (nextCursor (nextCursor ptr ⟨160⟩) (UInt256.ofNat out.size)).toNat) :
    MemoryPrefix mem
      (extSloadsDecodedMem
        (extSloadsBufferMem
          (extSloadsCallMem (lastUpdateArrayMem mem calldata ptr id)
            (nextCursor ptr ⟨160⟩).toNat (lastUpdateSlot id))
          (nextCursor ptr ⟨160⟩) out)
        (nextCursor (nextCursor ptr ⟨160⟩) (UInt256.ofNat out.size)) out) ptr.toNat := by
  have hn : (nextCursor ptr ⟨160⟩).toNat = ptr.toNat + 160 :=
    uadd_word_ofNat_toNat ptr 160 (lt_trans hfit (by decide))
  exact (lastUpdateArrayMem_prefix _ _ _ _ (by change _ < 2 ^ 256; omega)).trans
    (((extSloadsCallMem_prefix _ _ _).mono (by rw [hn]; omega)).trans
      (((extSloadsBufferMem_prefix _ _ _ (by rw [extSloadsCallMem_size]; omega)).mono
        (by rw [hn]; omega)).trans
        ((extSloadsDecodedMem_prefix _ _ _).mono (by rw [hn] at hraw; omega))))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
