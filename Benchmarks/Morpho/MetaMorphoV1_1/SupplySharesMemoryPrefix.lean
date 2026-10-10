import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationSetup
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodedMemory

/-! The allocated supply-share reader preserves previously allocated heap words. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem packedPairAllocMem_prefix (mem : ByteArray) (ptr first second : UInt256)
    (hfit : ptr.toNat + 64 < UInt256.size) :
    MemoryPrefix mem (packedPairAllocMem mem ptr first second) ptr.toNat := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 hfit
  unfold packedPairAllocMem packedPairMem
  exact (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by rw [h32]; omega))).trans
    ((memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by rw [h64]; omega))).trans
      ((memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
        (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide)))))

theorem positionSlotArrayMem_prefix (mem calldata : ByteArray) (ptr id user : UInt256)
    (hfit : ptr.toNat + 224 < UInt256.size) :
    MemoryPrefix mem (positionSlotArrayMem mem calldata ptr id user) ptr.toNat := by
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat ptr 96 (by omega)
  have h192 : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
    uadd_word_ofNat_toNat ptr 192 (by omega)
  exact (packedPairAllocMem_prefix _ _ _ _ (by omega)).trans
    (((packedPairAllocMem_prefix _ _ _ _ (by rw [h96]; omega)).mono
      (by rw [h96]; omega)).trans
      ((morphoArrayMem_prefix _ _ _ _ (by rw [h192]; omega)).mono (by rw [h192]; omega)))

theorem extSloadsCallMem_prefix (mem : ByteArray) (ptr : Nat) (slot : UInt256) :
    MemoryPrefix mem (extSloadsCallMem mem ptr slot) ptr := by
  apply memoryPrefix_sparse_cascade
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> exact .inl (by omega)

theorem extSloadsBufferMem_prefix (mem out : ByteArray) (ptr : UInt256)
    (hmem : ptr.toNat ≤ mem.size) :
    MemoryPrefix mem (extSloadsBufferMem mem ptr out) ptr.toNat := by
  have hcopy : MemoryPrefix mem (out.write 0 mem ptr.toNat out.size) ptr.toNat := by
    by_cases hz : out.size = 0
    · rw [hz, byteArray_write_len_zero]
      exact .refl _ _
    · exact copyWindow_prefix _ _ _ _ _ _ hz (by omega) hmem (.inl (le_refl _))
  exact hcopy.trans (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide)))

theorem extSloadsDecodedMem_prefix (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    MemoryPrefix mem (extSloadsDecodedMem mem ptr out) ptr.toNat :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide))).trans
    ((memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
      ((wordSequenceMemory_prefix _ _ _).mono (by omega)))

theorem supplySharesReadMemory_prefix (mem calldata out : ByteArray) (ptr id user : UInt256)
    (hfit : ptr.toNat + 256 < 2 ^ 64)
    (hraw : (nextCursor ptr ⟨256⟩).toNat ≤
      (nextCursor (nextCursor ptr ⟨256⟩) (UInt256.ofNat out.size)).toNat) :
    MemoryPrefix mem
      (extSloadsDecodedMem
        (extSloadsBufferMem
          (extSloadsCallMem (positionSlotArrayMem mem calldata ptr id user)
            (nextCursor ptr ⟨256⟩).toNat
            (positionSupplySharesSlot id (AccountAddress.ofNat user.toNat)))
          (nextCursor ptr ⟨256⟩) out)
        (nextCursor (nextCursor ptr ⟨256⟩) (UInt256.ofNat out.size)) out) ptr.toNat := by
  have hn : (nextCursor ptr ⟨256⟩).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (lt_trans hfit (by decide))
  exact (positionSlotArrayMem_prefix _ _ _ _ _ (by change _ < 2 ^ 256; omega)).trans
    (((extSloadsCallMem_prefix _ _ _).mono (by rw [hn]; omega)).trans
      (((extSloadsBufferMem_prefix _ _ _ (by rw [extSloadsCallMem_size]; omega)).mono
        (by rw [hn]; omega)).trans
        ((extSloadsDecodedMem_prefix _ _ _).mono (by rw [hn] at hraw; omega))))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
