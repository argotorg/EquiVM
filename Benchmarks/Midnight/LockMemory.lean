import Benchmarks.Midnight.LockSource
import Benchmarks.Midnight.WordArray

/-! Memory encoding used to hash a transient lock key. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def lockHashMemory (id user : UInt256) : ByteArray :=
  writeWord (writeWordArray midnightEntryMemory 864 [id, user, liquidationLockBase]) 832 ⟨96⟩

theorem lockHashMemory_size (id user : UInt256) : (lockHashMemory id user).size = 960 := by
  simp only [lockHashMemory, writeWordArray, writeWord_sparse_size, midnightEntryMemory_size]
  rfl

theorem lockHashMemory_length (id user : UInt256) :
    memLoad (UInt256.ofNat 832) (lockHashMemory id user) = ⟨96⟩ :=
  memLoad_writeWord _ _ _

theorem lockHashMemory_bytes (id user : UInt256) :
    (lockHashMemory id user).readWithPadding 864 96 =
      id.toByteArray ++ user.toByteArray ++ liquidationLockBase.toByteArray := by
  have hsize : (writeWordArray midnightEntryMemory 864 [id, user, liquidationLockBase]).size =
      960 := by
    simp only [writeWordArray, writeWord_sparse_size, midnightEntryMemory_size]
    rfl
  unfold lockHashMemory Reasoning.Theory.writeWord
  rw [write32_read_above_len _ _ 832 864 96 (by rw [toByteArray_size])
    (by rw [hsize]; decide) (by decide) (by rw [hsize]) (by decide) (by decide)]
  have hr := wordArray_read_of_reads
    (writeWordArray midnightEntryMemory 864 [id, user, liquidationLockBase]) 864
    [id, user, liquidationLockBase] (by rw [hsize]; simp)
    (writeWordArray_read_index _ _ _)
  simpa [wordArrayBytes, ByteArray.append_assoc] using hr

def lockReturnMemory (id user : UInt256) : ByteArray :=
  writeWord (lockHashMemory id user) 64 ⟨960⟩

theorem lockReturnMemory_size (id user : UInt256) : (lockReturnMemory id user).size = 960 := by
  rw [lockReturnMemory, writeWord_sparse_size, lockHashMemory_size]
  rfl

theorem lockReturnMemory_freePtr (id user : UInt256) :
    memLoad (UInt256.ofNat 64) (lockReturnMemory id user) = ⟨960⟩ :=
  memLoad_writeWord _ _ _

theorem lockReturnMemory_length (id user : UInt256) :
    memLoad (UInt256.ofNat 832) (lockReturnMemory id user) = ⟨96⟩ := by
  rw [lockReturnMemory, memLoad_writeWord_preserved _ _ _ _
    (by rw [lockHashMemory_size]; decide) (Or.inr (by decide)), lockHashMemory_length]

theorem lockReturnMemory_hash (id user : UInt256) :
    keccakWord (UInt256.ofNat 864) (UInt256.ofNat 96) (lockReturnMemory id user) =
      lockSlot liquidationLockBase id user := by
  unfold keccakWord lockReturnMemory Reasoning.Theory.writeWord
  simp only [show (UInt256.ofNat 864).toNat = 864 from rfl,
    show (UInt256.ofNat 96).toNat = 96 from rfl]
  rw [write32_read_above_len _ _ 64 864 96 (by rw [toByteArray_size])
    (by rw [lockHashMemory_size]; decide) (by decide)
    (by rw [lockHashMemory_size]) (by decide) (by decide), lockHashMemory_bytes]
  exact (uInt256OfByteArray_eq _).symm

-- LIBRARY CANDIDATE: the full transient word, without a storage-byte mask, is tested for zero.
theorem fullBoolWordReturnEncoding (word : UInt256) :
    encodeReturnValue? (.elem .bool) (wordToElem .bool word) =
      some (UInt256.isZero (UInt256.isZero word)).toByteArray := by
  by_cases hw : word = ⟨0⟩
  · subst word
    exact boolFalseReturnEncoding
  · rw [wordToElemBool, decide_eq_false hw, isZero_eq_zero_of_ne hw]
    exact boolTrueReturnEncoding

end Benchmarks.Midnight
