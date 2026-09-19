import Solm.Benchmarks.Auction.InitializerBegin

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the non-wrapping form of the word bitwise OR.
theorem lor_toNat (a b : UInt256) : (UInt256.lor a b).toNat = a.toNat ||| b.toNat := by
  rw [u256_lor_toNat]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 256) a.val.isLt b.val.isLt)

theorem initializerHighWord_toNat (old : UInt256) :
    (UInt256.land old (UInt256.lnot ⟨65535⟩)).toNat = old.toNat / 65536 * 65536 := by
  rw [u256_land_comm]
  exact u256_land_high_mask_toNat old 16 (by decide)

theorem initializerBeginWord_toNat (old : UInt256) :
    (initializerBeginWord old).toNat = 257 + old.toNat / 65536 * 65536 := by
  rw [initializerBeginWord, lor_toNat, initializerHighWord_toNat, Nat.or_comm]
  exact nat_lor_shift_add 257 (old.toNat / 65536) 16 (by decide)

theorem initializerEndWord_toNat (old : UInt256) :
    (initializerEndWord old).toNat = old.toNat % 256 + old.toNat / 65536 * 65536 := by
  rw [initializerEndWord, uland_toNat]
  have hm : (UInt256.lnot (⟨65280⟩ : UInt256)).toNat =
      255 ||| (2 ^ 256 - 2 ^ 16) := by decide
  rw [hm, Nat.and_or_distrib_left]
  change Nat.lor (Nat.land old.toNat (2 ^ 8 - 1))
    (Nat.land old.toNat (2 ^ 256 - 2 ^ 16)) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat 16 (by decide) old.val.isLt]
  exact nat_lor_shift_add (old.toNat % 256) (old.toNat / 65536) 16
    (by have := Nat.mod_lt old.toNat (by decide : 0 < 256); omega)

def setInitializingWord (old : UInt256) (value : Bool) : UInt256 :=
  UInt256.ofNat (old.toNat % 256 + 256 * value.toNat + old.toNat / 65536 * 65536)

theorem setInitializingWord_toNat (old : UInt256) (value : Bool) :
    (setInitializingWord old value).toNat =
      old.toNat % 256 + 256 * value.toNat + old.toNat / 65536 * 65536 := by
  apply ulit_toNat'
  have h := old.val.isLt
  have hlow := Nat.mod_lt old.toNat (by decide : 0 < 256)
  cases value <;> change _ < 2 ^ 256 <;> change old.toNat < 2 ^ 256 at h <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] <;> omega

theorem setInitializingWord_false (old : UInt256) :
    setInitializingWord old false = initializerEndWord old := by
  apply u256_inj
  rw [setInitializingWord_toNat, initializerEndWord_toNat]
  rfl

theorem setInitializingThenInitialized (old : UInt256) :
    UInt256.lor (UInt256.land (setInitializingWord old true) (UInt256.lnot ⟨255⟩)) ⟨1⟩ =
      initializerBeginWord old := by
  apply u256_inj
  rw [packedSetTrueWord_toNat, setInitializingWord_toNat, initializerBeginWord_toNat]
  have hlow := Nat.mod_lt old.toNat (by decide : 0 < 256)
  simp only [Bool.toNat_true, Nat.mul_one]
  omega

-- GENERALIZES the offset-zero bool write to the initializer's second storage byte.
theorem storageLocStore_initializing (evm : EVM.State) (slot : UInt256) (value : Bool) :
    storageLocStore evm (auctionBoolLocAt slot 1) (.bool value) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setInitializingWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value))
          := by
  unfold storageLocStore storageLocWriteWord auctionBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof value.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 2) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setInitializingWord_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof value.toUInt256).2]
  cases value <;> simp [Bool.toUInt256, Nat.mul_comm] <;> decide

theorem storedWord_sstore_present (σ : AccountMap) (I : ExecutionEnv)
    {acc : Account} (ha : σ.find? I.codeOwner = some acc) (slot value : UInt256) :
    storedWord (sstoreAccountMap I.codeOwner σ slot value) I slot = value := by
  unfold storedWord sstoreAccountMap
  rw [ha]
  simp only [Option.option, accountMap_find_insert_self]
  by_cases hz : value = (default : UInt256)
  · subst value
    simpa using storage_findD_erase_self acc.storage slot ⟨0⟩
  · simpa [hz] using storage_findD_insert_self acc.storage slot value ⟨0⟩

theorem initializingBeginWord (old : UInt256) :
    UInt256.land (UInt256.div (initializerBeginWord old) ⟨256⟩) ⟨255⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uland_toNat]
  change Nat.land ((initializerBeginWord old).toNat / 256) (2 ^ 8 - 1) = 1
  rw [nat_land_mask_eq_mod, initializerBeginWord_toNat]
  omega

theorem initializerEntered_ready (σ : AccountMap) (I : ExecutionEnv) :
    InitializerReady (initializerEntered σ I) I := by
  by_cases hi : initializingWord σ I = ⟨0⟩
  · rw [initializerEntered, if_pos hi]
    cases ha : σ.find? I.codeOwner with
    | none =>
      rw [sstoreAccountMap_absent_same ha]
      exact Or.inr ha
    | some acc =>
      left
      rw [initializingWord, storedWord_sstore_present σ I ha, initializingBeginWord]
      decide
  · rw [initializerEntered, if_neg hi]
    exact Or.inl hi

end Auction
