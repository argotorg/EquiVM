import Benchmarks.Morpho.MorphoBlue.SafeTransferABI
import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferCallSize (isFrom : Bool) : Nat := if isFrom then 100 else 68
def safeTransferCallAllocation (isFrom : Bool) : Nat := if isFrom then 160 else 128

def safeTransferCallPayload (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  staticWordCallMem (safeTransferSelectorWord isFrom) (safeTransferCallWords isFrom sender recipient value)
    mem (ptr.toNat + 32)

def safeTransferCallMem (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord (safeTransferCallPayload isFrom sender recipient value mem ptr) ptr.toNat
    (UInt256.ofNat (safeTransferCallSize isFrom))) 64 (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom))

-- LIBRARY CANDIDATE: writing a contiguous word sequence preserves earlier allocated memory.
theorem writeReturnWords_prefix (ws : List UInt256) (mem : ByteArray) (off limit : Nat)
    (hbelow : limit ≤ off) : MemoryPrefix mem (writeCascade mem (returnWordWrites off ws)) limit := by
  induction ws generalizing mem off with
  | nil => exact .refl _ _
  | cons w ws ih =>
    exact (memoryPrefix_sparse_writeWord mem off limit w (Or.inl hbelow)).trans
      (ih _ _ (by omega))

-- LIBRARY CANDIDATE: selector and static argument writes preserve earlier allocated memory.
theorem staticWordCallMem_prefix (selector : UInt256) (ws : List UInt256) (mem : ByteArray)
    (off limit : Nat) (hbelow : limit ≤ off) : MemoryPrefix mem (staticWordCallMem selector ws mem off) limit :=
  (memoryPrefix_sparse_writeWord mem off limit selector (Or.inl hbelow)).trans
    (writeReturnWords_prefix ws _ _ _ (by omega))

theorem safeTransferCallPayload_size (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) (hin : ptr.toNat ≤ mem.size) :
    (safeTransferCallPayload isFrom sender recipient value mem ptr).size =
      max mem.size (ptr.toNat + 32 + safeTransferCallSize isFrom) := by
  have hg : ptr.toNat + 32 - mem.size < USize.size := by
    have hu := lt_usize 32 (by decide); omega
  rw [safeTransferCallPayload, staticWordCallMem_size _ _ _ _
    (by cases isFrom <;> simp [safeTransferCallWords]) hg]
  cases isFrom <;> rfl

theorem safeTransferCallMem_properties (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) (hl : 128 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size) :
    (safeTransferCallMem isFrom sender recipient value mem ptr).size =
      max mem.size (ptr.toNat + 32 + safeTransferCallSize isFrom) ∧
    memLoad (UInt256.ofNat 64) (safeTransferCallMem isFrom sender recipient value mem ptr) =
      ptr + UInt256.ofNat (safeTransferCallAllocation isFrom) ∧
    memLoad ptr (safeTransferCallMem isFrom sender recipient value mem ptr) = UInt256.ofNat (safeTransferCallSize isFrom) ∧
    (safeTransferCallMem isFrom sender recipient value mem ptr).readWithPadding
      (ptr.toNat + 32) (safeTransferCallSize isFrom) = safeTransferCalldata isFrom sender recipient value := by
  let m0 := safeTransferCallPayload isFrom sender recipient value mem ptr
  let m1 := writeWord m0 ptr.toNat (UInt256.ofNat (safeTransferCallSize isFrom))
  have hs0 : m0.size = max mem.size (ptr.toNat + 32 + safeTransferCallSize isFrom) :=
    safeTransferCallPayload_size isFrom sender recipient value mem ptr hin
  have hu := USize.size_pos
  have hg0 : ptr.toNat - m0.size < USize.size := by rw [hs0]; omega
  have hs1 : m1.size = m0.size := by
    rw [writeWord_size _ _ _ hg0, hs0]; omega
  have hg1 : 64 - m1.size < USize.size := by rw [hs1, hs0]; omega
  have hs : (safeTransferCallMem isFrom sender recipient value mem ptr).size = m0.size := by
    change (writeWord m1 64 _).size = _
    rw [writeWord_size _ _ _ hg1, hs1, hs0]; omega
  refine ⟨hs.trans hs0, ?_, ?_, ?_⟩
  · exact memLoad_writeWord_self_of_offset m1 64 _ (UInt256.ofNat 64) hg1 rfl
  · change memLoad ptr (writeWord m1 64 _) = _
    rw [memLoad_writeWord_disjoint _ _ _ _ hg1 (by rw [hs1, hs0]; omega) (Or.inr (by omega))]
    exact memLoad_writeWord_self_of_offset m0 ptr.toNat _ ptr hg0 rfl
  · have hlen : 0 < safeTransferCallSize isFrom ∧ safeTransferCallSize isFrom < 2 ^ 64 := by
      cases isFrom <;> decide
    change (writeWord m1 64 _).readWithPadding _ _ = _
    rw [writeWord_read_preserved_len m1 64 _ _ _ hg1
      (Or.inr ⟨by omega, by rw [hs1, hs0]; omega⟩) hlen.1 hlen.2]
    change (writeWord m0 ptr.toNat _).readWithPadding _ _ = _
    rw [writeWord_read_preserved_len m0 ptr.toNat _ _ _ hg0
      (Or.inr ⟨le_rfl, by rw [hs0]; omega⟩) hlen.1 hlen.2]
    exact safeTransferCalldata_read isFrom sender recipient value mem (ptr.toNat + 32)
      (by have hu := lt_usize 32 (by decide); omega)

theorem safeTransferCallMem_prefix (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) :
    MemoryPrefix mem (safeTransferCallMem isFrom sender recipient value mem ptr) ptr.toNat :=
  (staticWordCallMem_prefix _ _ mem (ptr.toNat + 32) ptr.toNat (by omega)).trans
    ((memoryPrefix_sparse_writeWord _ ptr.toNat ptr.toNat _ (Or.inl le_rfl)).trans
      (memoryPrefix_sparse_writeWord _ 64 ptr.toNat _ (Or.inr (by decide))))

theorem safeTransferCallMem_heap (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) (hl : 128 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size)
    (hf : ptr.toNat + safeTransferCallAllocation isFrom < 2 ^ 64) :
    MorphoHeap (safeTransferCallMem isFrom sender recipient value mem ptr)
      (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom)) 0 := by
  have hs := safeTransferCallMem_properties isFrom sender recipient value mem ptr hl hin
  have hp := uadd_word_ofNat_toNat ptr (safeTransferCallAllocation isFrom)
    (by change _ < 2 ^ 256; omega)
  refine ⟨by rw [hs.1]; omega, hs.2.1, ?_, ?_, ?_⟩
  · rw [hp]; omega
  · rw [hp, hs.1]
    have hu := lt_usize 28 (by decide)
    cases isFrom <;> simp only [safeTransferCallAllocation, safeTransferCallSize, ↓reduceIte,
      Bool.false_eq_true] <;> omega
  · rw [hp]; omega

end Benchmarks.Morpho.MorphoBlue
