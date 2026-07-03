import Examples.BytesStoreLite.Spec
import Examples.BytesStoreLite.CoreSetOldLong

/-!
# BytesStoreLite storage-loop algebra

Pure algebraic facts about compiler-generated storage loops.  These facts do not use symbolic
Keccak separation assumptions.
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

end BytesStoreLite
