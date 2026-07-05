import Examples.BytesStore.Spec
import Examples.StringStoreLite.SetLong
import Examples.BytesStore.StorageReadbackFacts

/-!
# BytesStore storage-loop algebra

Pure algebraic facts about compiler-generated storage loops.  These facts do not use symbolic
Keccak separation assumptions.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace BytesStore

theorem accountMapEquiv_setBytesShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {baseSlot oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase baseSlot) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        baseSlot storedWord)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          baseSlot 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner baseSlot (solidityShortBytesWord value)).accountMap := by
  have hdivNat :
      (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩).toNat =
        (oldLen.toNat + 31) / 32 :=
    StringStoreLite.u256_div_add31_toNat_of_lt_sign (x := oldLen) holdLenLt
  have hshift :
      UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩ =
        UInt256.div (oldLen + ⟨31⟩) ⟨32⟩ := by
    apply u256_inj
    simp [UInt256.shiftRight, UInt256.div, UInt256.toNat, Nat.shiftRight_eq_div_pow]
    norm_num [UInt256.size]
  have hcountNat :
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat =
        (oldLen.toNat + 31) / 32 := by
    rw [hshift, StringStoreLite.uint256_sub_zero_right]
    exact hdivNat
  have hbase :
      ((⟨0⟩ : UInt256) + bytesLikeDataBase baseSlot) =
        solidityBytesDataBaseSlot baseSlot := by
    rw [u256_add_comm (⟨0⟩ : UInt256) (bytesLikeDataBase baseSlot)]
    rw [StringStoreLite.uint256_add_zero_right]
    rfl
  have hclear :
      accountMapEquiv
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase baseSlot) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          baseSlot 0 ((oldLen.toNat + 31) / 32)).accountMap := by
    simpa [initState, clearSolidityBytesDataWordsFrom_accountMap, hcountNat, hbase] using
      accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
        (solidityBytesDataBaseSlot baseSlot) ⟨0⟩
        ((oldLen.toNat + 31) / 32) hAccounts
  simpa [hstored] using
    accountMapEquiv_bytesHeaderStore I.codeOwner baseSlot
      (solidityShortBytesWord value) hclear

theorem bytesStoreLongDataWordsLoopSlot_bytesLikeDataBase (baseSlot : UInt256) :
    ∀ i, StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) i =
      solidityBytesDataSlot baseSlot i
  | 0 => by
      simp [StringStoreLite.longDataWordsLoopSlot, solidityBytesDataSlot,
        bytesLikeDataBase, solidityBytesDataBaseSlot]
      rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
      exact (StringStoreLite.uint256_add_zero_right
        (uInt256OfByteArray (ffi.KEC baseSlot.toByteArray))).symm
  | i + 1 => by
      rw [StringStoreLite.longDataWordsLoopSlot,
        bytesStoreLongDataWordsLoopSlot_bytesLikeDataBase baseSlot i]
      simp [solidityBytesDataSlot, solidityBytesDataBaseSlot,
        StringStoreLite.u256_base_one_add_ofNat]

end BytesStore
