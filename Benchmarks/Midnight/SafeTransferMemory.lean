import Benchmarks.Midnight.SafeTransferABI
import Benchmarks.Midnight.MemoryPrefix

/-! Memory occupied by a safe-transfer calldata buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def safeTransferCallSize (isFrom : Bool) : Nat := if isFrom then 100 else 68

def safeTransferCallAllocation (isFrom : Bool) : Nat := if isFrom then 160 else 128

def staticWordCallMem (selector : UInt256) (words : List UInt256)
    (mem : ByteArray) (off : Nat) : ByteArray :=
  writeWordArray (writeWord mem off selector) (off + 4) words

theorem staticWordCallMem_size (selector : UInt256) (words : List UInt256)
    (mem : ByteArray) (off : Nat) (hne : words ≠ []) :
    (staticWordCallMem selector words mem off).size = max mem.size (off + 4 + 32 * words.length) := by
  have hlen := List.length_pos_of_ne_nil hne
  rw [staticWordCallMem, writeWordArray_size _ _ _ (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_size]
  omega

theorem staticWordCallMem_read (selector : UInt256) (words : List UInt256)
    (mem : ByteArray) (off : Nat) (hne : words ≠ []) :
    (staticWordCallMem selector words mem off).readWithPadding off (4 + 32 * words.length) =
      selector.toByteArray.extract 0 4 ++ wordArrayBytes words := by
  have hlen := List.length_pos_of_ne_nil hne
  have hs := staticWordCallMem_size selector words mem off hne
  have hin : off + 4 ≤ (writeWord mem off selector).size := by rw [writeWord_sparse_size]; omega
  rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega) (by rw [hs]; omega)]
  rw [staticWordCallMem, writeWordArray_read_below_len _ _ _ _ _ hin le_rfl (by decide) (by decide),
    writeWordArray_read _ _ _ hin]
  have hw := writeWord_sparse_read_window mem off 0 4 selector (by decide) (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add] using
    congrArg (fun bytes ↦ bytes ++ wordArrayBytes words) hw

theorem staticWordCallMem_prefix (selector : UInt256) (words : List UInt256)
    (mem : ByteArray) (off limit : Nat) (hbelow : limit ≤ off) :
    MemoryPrefix mem (staticWordCallMem selector words mem off) limit :=
  (memoryPrefix_writeWord mem off limit selector (Or.inl hbelow)).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))

def safeTransferCallPayload (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  staticWordCallMem (safeTransferSelectorWord isFrom)
    (safeTransferCallWords isFrom sender recipient value) mem (ptr.toNat + 32)

def safeTransferCallMem (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord (safeTransferCallPayload isFrom sender recipient value mem ptr) ptr.toNat
    (UInt256.ofNat (safeTransferCallSize isFrom))) 64
      (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom))

theorem safeTransferCallPayload_size (isFrom : Bool) (sender recipient : AccountAddress)
    (value : UInt256) (mem : ByteArray) (ptr : UInt256) :
    (safeTransferCallPayload isFrom sender recipient value mem ptr).size =
      max mem.size (ptr.toNat + 32 + safeTransferCallSize isFrom) := by
  rw [safeTransferCallPayload, staticWordCallMem_size _ _ _ _
    (by cases isFrom <;> simp [safeTransferCallWords])]
  cases isFrom <;> simp [safeTransferCallWords, safeTransferCallSize, Nat.add_assoc]

theorem safeTransferCallPayload_read (isFrom : Bool) (sender recipient : AccountAddress)
    (value : UInt256) (mem : ByteArray) (ptr : UInt256) :
    (safeTransferCallPayload isFrom sender recipient value mem ptr).readWithPadding
      (ptr.toNat + 32) (safeTransferCallSize isFrom) =
      safeTransferCalldata isFrom sender recipient value := by
  have hr := staticWordCallMem_read (safeTransferSelectorWord isFrom)
    (safeTransferCallWords isFrom sender recipient value) mem (ptr.toNat + 32)
    (by cases isFrom <;> simp [safeTransferCallWords])
  rw [safeTransferSelectorWord_bytes] at hr
  cases isFrom <;> exact hr

theorem safeTransferCallMem_properties (isFrom : Bool) (sender recipient : AccountAddress)
    (value : UInt256) (mem : ByteArray) (ptr : UInt256) (hl : 96 ≤ ptr.toNat) :
    (safeTransferCallMem isFrom sender recipient value mem ptr).size =
      max mem.size (ptr.toNat + 32 + safeTransferCallSize isFrom) ∧
    memLoad (UInt256.ofNat 64) (safeTransferCallMem isFrom sender recipient value mem ptr) =
      ptr + UInt256.ofNat (safeTransferCallAllocation isFrom) ∧
    memLoad ptr (safeTransferCallMem isFrom sender recipient value mem ptr) =
      UInt256.ofNat (safeTransferCallSize isFrom) ∧
    (safeTransferCallMem isFrom sender recipient value mem ptr).readWithPadding
      (ptr.toNat + 32) (safeTransferCallSize isFrom) =
      safeTransferCalldata isFrom sender recipient value := by
  let m0 := safeTransferCallPayload isFrom sender recipient value mem ptr
  let m1 := writeWord m0 ptr.toNat (UInt256.ofNat (safeTransferCallSize isFrom))
  have hs0 : m0.size = max mem.size (ptr.toNat + 32 + safeTransferCallSize isFrom) :=
    safeTransferCallPayload_size isFrom sender recipient value mem ptr
  have hs1 : m1.size = m0.size := by
    dsimp only [m1]
    rw [writeWord_sparse_size, hs0]
    omega
  have hs : (safeTransferCallMem isFrom sender recipient value mem ptr).size = m0.size := by
    change (writeWord m1 64 _).size = _
    rw [writeWord_sparse_size, hs1, hs0]
    omega
  refine ⟨hs.trans hs0, memLoad_writeWord _ (UInt256.ofNat 64) _, ?_, ?_⟩
  · change memLoad ptr (writeWord m1 64 _) = _
    rw [memLoad_writeWord_preserved _ _ _ _ (by rw [hs1, hs0]; omega) (Or.inr hl)]
    exact memLoad_writeWord m0 ptr _
  · have hlen : 0 < safeTransferCallSize isFrom ∧ safeTransferCallSize isFrom < 2 ^ 64 := by
      cases isFrom <;> decide
    change (writeWord m1 64 _).readWithPadding _ _ = _
    rw [writeWord_sparse_read_preserved_len m1 64 _ _ _ (by rw [hs1, hs0]; omega)
      (Or.inr (by omega)) hlen.1 hlen.2]
    change (writeWord m0 ptr.toNat _).readWithPadding _ _ = _
    rw [writeWord_sparse_read_preserved_len m0 ptr.toNat _ _ _ (by rw [hs0]; omega)
      (Or.inr le_rfl) hlen.1 hlen.2]
    exact safeTransferCallPayload_read isFrom sender recipient value mem ptr

theorem safeTransferCallMem_prefix (isFrom : Bool) (sender recipient : AccountAddress)
    (value : UInt256) (mem : ByteArray) (ptr : UInt256) :
    MemoryPrefix mem (safeTransferCallMem isFrom sender recipient value mem ptr) ptr.toNat :=
  (staticWordCallMem_prefix _ _ mem (ptr.toNat + 32) ptr.toNat (by omega)).trans
    ((memoryPrefix_writeWord _ ptr.toNat ptr.toNat _ (Or.inl le_rfl)).trans
      (memoryPrefix_writeWord _ 64 ptr.toNat _ (Or.inr (by decide))))

end Benchmarks.Midnight
