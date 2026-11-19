import Benchmarks.Midnight.LockSource
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.MemoryPrefix

/-! The transient-lock key encoded at an arbitrary free-memory pointer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def dynamicLockHashMemory (mem : ByteArray) (root id user : UInt256) : ByteArray :=
  writeWord (writeWordArray mem (root.toNat + 32) [id, user, liquidationLockBase]) root.toNat ⟨96⟩

def dynamicLockMemory (mem : ByteArray) (root id user : UInt256) : ByteArray :=
  writeWord (dynamicLockHashMemory mem root id user) 64 (root + UInt256.ofNat 128)

theorem dynamicLockHashMemory_size (mem : ByteArray) (root id user : UInt256) :
    (dynamicLockHashMemory mem root id user).size = max mem.size (root.toNat + 128) := by
  simp only [dynamicLockHashMemory, writeWordArray, writeWord_sparse_size]
  omega

theorem dynamicLockMemory_prefix (mem : ByteArray) (root id user : UInt256) :
    MemoryPrefix mem (dynamicLockMemory mem root id user) root.toNat :=
  ((memoryPrefix_writeWordArray _ _ _ _ (by omega)).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inr (by decide)))

theorem dynamicLockMemory_free (mem : ByteArray) (root id user : UInt256) :
    memLoad (UInt256.ofNat 64) (dynamicLockMemory mem root id user) =
      root + UInt256.ofNat 128 := memLoad_writeWord _ _ _

theorem dynamicLockMemory_length (mem : ByteArray) {root : UInt256} (id user : UInt256)
    (hroot : 96 ≤ root.toNat) :
    memLoad root (dynamicLockMemory mem root id user) = ⟨96⟩ := by
  rw [dynamicLockMemory, memLoad_writeWord_preserved _ _ _ _
    (by rw [dynamicLockHashMemory_size]; omega) (Or.inr hroot)]
  exact memLoad_writeWord _ _ _

theorem dynamicLockMemory_words (mem : ByteArray) {root : UInt256} (id user : UInt256)
    (hroot : 96 ≤ root.toNat) (hbound : root.toNat + 128 < UInt256.size) :
    MemoryWords (dynamicLockMemory mem root id user) (root.toNat + 32)
      [id, user, liquidationLockBase] :=
  ((MemoryWords.of_writeWordArray mem (root.toNat + 32) [id, user, liquidationLockBase]
    (by simpa using hbound) (by simp)).writeWord ⟨96⟩ (Or.inr le_rfl)).writeWord
    (root + UInt256.ofNat 128) (Or.inr (by omega))

theorem dynamicLockMemory_hash (mem : ByteArray) {root : UInt256} (id user : UInt256)
    (hroot : 96 ≤ root.toNat) (hbound : root.toNat + 128 < UInt256.size) :
    keccakWord (root + UInt256.ofNat 32) ⟨96⟩ (dynamicLockMemory mem root id user) =
      lockSlot liquidationLockBase id user := by
  have hr := (dynamicLockMemory_words mem id user hroot hbound).read
  change (dynamicLockMemory mem root id user).readWithPadding (root.toNat + 32) 96 = _ at hr
  unfold keccakWord
  rw [uadd_word_ofNat_toNat root 32 (by omega)]
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((dynamicLockMemory mem root id user).readWithPadding (root.toNat + 32) 96))) = _
  rw [hr]
  simpa [wordArrayBytes, ByteArray.append_assoc, lockSlot] using
    (uInt256OfByteArray_eq
      (KEC (id.toByteArray ++ user.toByteArray ++ liquidationLockBase.toByteArray))).symm

end Benchmarks.Midnight
