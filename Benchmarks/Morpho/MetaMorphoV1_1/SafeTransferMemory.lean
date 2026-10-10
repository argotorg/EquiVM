import Benchmarks.Morpho.MetaMorphoV1_1.TwoWordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferABI
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnMemory

/-! The length-prefixed transfer request and its free-memory cursor update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def safeTransferRequestMemory (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) : ByteArray :=
  writeWord (twoWordCallMem mem (ptr.toNat + 32) safeTransferSelectorWord
    (UInt256.ofNat recipient.toNat) amount) ptr.toNat ⟨68⟩

def safeTransferCallMemory (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) : ByteArray :=
  writeWord (safeTransferRequestMemory mem ptr recipient amount) 64 (nextCursor ptr ⟨100⟩)

theorem safeTransferRequestMemory_size (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) :
    (safeTransferRequestMemory mem ptr recipient amount).size =
      max mem.size (ptr.toNat + 100) := by
  rw [safeTransferRequestMemory, writeWord_sparse_size, twoWordCallMem_size]
  omega

theorem safeTransferCallMemory_size (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) :
    (safeTransferCallMemory mem ptr recipient amount).size =
      max (max mem.size (ptr.toNat + 100)) 96 := by
  rw [safeTransferCallMemory, writeWord_sparse_size, safeTransferRequestMemory_size]

theorem safeTransferCallMemory_free (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) :
    memLoad ⟨64⟩ (safeTransferCallMemory mem ptr recipient amount) = nextCursor ptr ⟨100⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem safeTransferCallMemory_length (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) (hlo : 96 ≤ ptr.toNat) :
    memLoad ptr (safeTransferCallMemory mem ptr recipient amount) = ⟨68⟩ := by
  rw [safeTransferCallMemory, Reasoning.Theory.writeWord, memLoad_write_disjoint _ 64 ptr _
    (by rw [safeTransferRequestMemory_size]; omega) (.inr hlo)]
  exact memLoad_write_same _ _ _ _ rfl

theorem safeTransferCallMemory_read (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat < 2 ^ 64) :
    (safeTransferCallMemory mem ptr recipient amount).readWithPadding
      (ptr + UInt256.ofNat 32).toNat 68 = safeTransferCalldata recipient amount := by
  have hu := lt_usize 0 (by decide)
  have hb : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
  rw [uadd_word_ofNat_toNat ptr 32 hb, safeTransferCallMemory,
    writeWord_read_preserved_len _ 64 _ 68 _
      (by rw [safeTransferRequestMemory_size]; omega)
      (.inr ⟨by omega, by rw [safeTransferRequestMemory_size]; omega⟩)
      (by decide) (by decide), safeTransferRequestMemory,
    writeWord_read_preserved_len _ ptr.toNat _ 68 _
      (by rw [twoWordCallMem_size]; omega)
      (.inr ⟨by omega, by rw [twoWordCallMem_size]; omega⟩)
      (by decide) (by decide), twoWordCallMem_read]
  rw [show safeTransferSelectorWord.toByteArray.extract 0 4 = safeTransferSelector from
    by decide +kernel]
  rfl

theorem safeTransferCallMemory_prefix (mem : ByteArray) (ptr : UInt256)
    (recipient : AccountAddress) (amount : UInt256) :
    MemoryPrefix mem (safeTransferCallMemory mem ptr recipient amount) ptr.toNat := by
  have hdata : MemoryPrefix mem (twoWordCallMem mem (ptr.toNat + 32)
      safeTransferSelectorWord (UInt256.ofNat recipient.toNat) amount) ptr.toNat := by
    apply memoryPrefix_sparse_cascade
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> exact .inl (by omega)
  exact hdata.trans ((memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))))

theorem safeTransferCursor_bound (ptr : UInt256) (hfit : allocationFits ptr ⟨100⟩) :
    (nextCursor ptr ⟨100⟩).toNat = ptr.toNat + 128 ∧ ptr.toNat + 128 < 2 ^ 64 := by
  have hr : roundedSize ⟨100⟩ = ⟨128⟩ := by decide
  have hb := (allocationFits_iff_sum_lt ptr ⟨100⟩).mp hfit
  rw [hr] at hb
  change ptr.toNat + 128 < 2 ^ 64 at hb
  refine ⟨?_, hb⟩
  rw [nextCursor, hr]
  exact uadd_word_ofNat_toNat ptr 128 (by change _ < 2 ^ 256; omega)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
