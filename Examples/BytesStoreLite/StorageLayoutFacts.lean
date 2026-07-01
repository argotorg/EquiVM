import Examples.BytesStoreLite.StorageFacts
import Examples.BytesStoreLite.CoreSetOldLong

/-!
# BytesStoreLite storage-layout loop facts

Derived facts about compiler-generated loops over Solidity dynamic-bytes storage regions.  The
trusted symbolic Keccak assumptions remain in `StorageFacts`; this file packages their loop-shaped
corollaries so runtime proofs do not repeat the same slot algebra.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace BytesStoreLite

theorem bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase (baseSlot : UInt256) :
    ∀ i, BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) i =
      solidityBytesDataSlot baseSlot i
  | 0 => by
      simp [BytesStoreLiteCore.longDataWordsLoopSlot, solidityBytesDataSlot,
        bytesLikeDataBase, solidityBytesDataBaseSlot]
      rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
      exact (BytesStoreLiteCore.uint256_add_zero_right
        (uInt256OfByteArray (ffi.KEC baseSlot.toByteArray))).symm
  | i + 1 => by
      rw [BytesStoreLiteCore.longDataWordsLoopSlot,
        bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot i]
      simp [solidityBytesDataSlot, solidityBytesDataBaseSlot,
        BytesStoreLiteCore.u256_base_one_add_ofNat]

theorem bytesStoreLiteChunkClearDataLoopSlot_ne_length
    (chunkIndex start : UInt256) (fuel : Nat) :
    (start + bytesLikeDataBase (chunksDataBase + chunkIndex)) +
        BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel ≠ (⟨1⟩ : UInt256) := by
  let base := bytesLikeDataBase (chunksDataBase + chunkIndex)
  let idx := BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel
  have h := bytesStoreLiteChunkDataWordSlot_ne_length chunkIndex (start + idx)
  intro hbad
  apply h
  calc
    bytesLikeDataBase (chunksDataBase + chunkIndex) + (start + idx)
        = (bytesLikeDataBase (chunksDataBase + chunkIndex) + start) + idx := by
          rw [← u256_add_assoc]
    _ = (start + bytesLikeDataBase (chunksDataBase + chunkIndex)) + idx := by
          rw [u256_add_comm (bytesLikeDataBase (chunksDataBase + chunkIndex)) start]
    _ = (⟨1⟩ : UInt256) := hbad

theorem bytesStoreLiteChunkLongDataLoopSlot_ne_length (chunkIndex : UInt256) (fuel : Nat) :
    BytesStoreLiteCore.longDataWordsLoopSlot
        (bytesLikeDataBase (chunksDataBase + chunkIndex)) fuel ≠ (⟨1⟩ : UInt256) := by
  rw [bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase]
  simpa [solidityBytesDataSlot, solidityBytesDataBaseSlot, bytesLikeDataBase] using
    bytesStoreLiteChunkDataWordSlot_ne_length chunkIndex (UInt256.ofNat fuel)

theorem bytesStoreLiteChunkDataSlot_ne_length (chunkIndex idx : UInt256) :
    bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ ≠
      (⟨1⟩ : UInt256) :=
  bytesStoreLiteChunkDataWordSlot_ne_length chunkIndex (UInt256.div idx ⟨32⟩)

end BytesStoreLite
