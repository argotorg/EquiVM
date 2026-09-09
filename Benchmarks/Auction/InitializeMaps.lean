import Benchmarks.Auction.InitializeBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

def auctionInitializeSetStatusMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩

def auctionInitializeSetTopFlagsMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩
    (setBoolOffset0Word (auctionSetBoolOffset1TrueWord (auctionSlotWord ⟨0⟩ σ I)) ⟨1⟩)

def auctionInitializeSetAddressMap
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ slot (setAddressOffset0Word (auctionSlotWord slot σ I) val)

def auctionInitializeSetUint256Map
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ slot val

def auctionInitializeSetMinBidMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨205⟩
    (auctionSetUint8Offset0Word (auctionSlotWord ⟨205⟩ σ I)
      (auctionInitializeMinBidIncrementPercentageWord I))

def auctionInitializeSetInitializingFalseMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (auctionSetBoolOffset1FalseWord (auctionSlotWord ⟨0⟩ σ I))

def auctionInitializeArgsPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let s5 := auctionInitializeSetAddressMap σ I ⟨201⟩ (auctionInitializeNounsWord I)
  let s6 := auctionInitializeSetAddressMap s5 I ⟨202⟩ (auctionInitializeWethWord I)
  let s7 := auctionInitializeSetUint256Map s6 I ⟨203⟩ (auctionInitializeTimeBufferWord I)
  let s8 := auctionInitializeSetUint256Map s7 I ⟨204⟩ (auctionInitializeReservePriceWord I)
  let s9 := auctionInitializeSetMinBidMap s8 I
  auctionInitializeSetUint256Map s9 I ⟨206⟩ (auctionInitializeDurationWord I)

def auctionInitializeCorePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let s1 := auctionUnpausePostMap σ I
  let s2 := auctionInitializeSetStatusMap s1 I
  let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
  let s4 := auctionPausePostMap s3 I
  auctionInitializeArgsPostMap s4 I

def auctionInitializeTopPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  auctionInitializeSetInitializingFalseMap
    (auctionInitializeCorePostMap (auctionInitializeSetTopFlagsMap σ I) I) I

private theorem auctionInitializingByte_setFlags (old : UInt256) :
    UInt256.land
      (UInt256.div (setBoolOffset0Word (auctionSetBoolOffset1TrueWord old) ⟨1⟩) ⟨256⟩)
      ⟨255⟩ = ⟨1⟩ := by
  have hflags : (setBoolOffset0Word (auctionSetBoolOffset1TrueWord old) ⟨1⟩).toNat =
      1 + 256 * (1 + 256 * (old.toNat / 65536)) := by
    unfold setBoolOffset0Word
    rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ by decide,
      packedSetTrueWord_toNat]
    unfold auctionSetBoolOffset1TrueWord
    rw [ulit_toNat' _ (auctionSetBoolOffset1TrueNat_lt_size old)]
    have hlow : old.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
    omega
  apply u256_inj
  rw [u256_land_toNat, udiv_toNat, hflags]
  change Nat.land ((1 + 256 * (1 + 256 * (old.toNat / 65536))) / 256)
    (2 ^ 8 - 1) % UInt256.size = 1
  rw [nat_land_mask_eq_mod]
  norm_num [UInt256.size]
  omega

theorem auctionSlotWord_store_same_present {σ : AccountMap} {I : ExecutionEnv} {acc : Account}
    (haccount : σ.find? I.codeOwner = some acc) (slot val : UInt256) :
    auctionSlotWord slot (sstoreAccountMap I.codeOwner σ slot val) I = val := by
  unfold auctionSlotWord sstoreAccountMap
  rw [haccount]
  simp only [Option.option]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    rw [if_pos hzero, accountMap_find_insert_self]
    simp only [storage_findD_erase_self]
    exact hval.symm
  · rw [if_neg hzero, accountMap_find_insert_self]
    simp only [storage_findD_insert_self]

theorem auctionSlotWord_of_absent {σ : AccountMap} {I : ExecutionEnv}
    (hmissing : σ.find? I.codeOwner = none) (slot : UInt256) :
    auctionSlotWord slot σ I = ⟨0⟩ := by
  unfold auctionSlotWord
  rw [hmissing]
  rfl

theorem auctionSlotWord_store_ne {σ : AccountMap} {I : ExecutionEnv}
    {readSlot writeSlot val : UInt256} (hne : readSlot ≠ writeSlot) :
    auctionSlotWord readSlot (sstoreAccountMap I.codeOwner σ writeSlot val) I =
      auctionSlotWord readSlot σ I :=
  sstoreAccountMap_storage_findD_ne σ I.codeOwner readSlot writeSlot val hne

theorem auctionInitializePrePausePausedZero {σ : AccountMap} {I : ExecutionEnv} :
    let s1 := auctionUnpausePostMap σ I
    let s2 := auctionInitializeSetStatusMap s1 I
    let s3 := auctionSetOwnerPostMap s2 I (auctionSourceWord I)
    auctionPausedWord s3 I = ⟨0⟩ := by
  dsimp only
  unfold auctionSetOwnerPostMap auctionInitializeSetStatusMap auctionPausedWord
  rw [auctionSlotWord_store_ne (by decide : (⟨51⟩ : UInt256) ≠ ⟨151⟩),
    auctionSlotWord_store_ne (by decide : (⟨51⟩ : UInt256) ≠ ⟨101⟩)]
  unfold auctionUnpausePostMap
  cases haccount : σ.find? I.codeOwner with
  | none =>
      rw [sstoreAccountMap_absent_same haccount, auctionSlotWord_of_absent haccount]
      rfl
  | some acc =>
      rw [auctionSlotWord_store_same_present haccount]
      exact auctionPausedClearedWord_low_zero _

theorem auctionInitializingGuard_ne_sstore_ne {σ I} {slot val : UInt256}
    (hne : (⟨0⟩ : UInt256) ≠ slot)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩) :
    UInt256.land
        (UInt256.div (auctionSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σ slot val) I) ⟨256⟩)
        ⟨255⟩ ≠ ⟨0⟩ := by
  rw [auctionSlotWord_store_ne hne]
  exact hnz

theorem auctionInitializeSetTopFlagsMap_initializing_ne {σ : AccountMap} {I : ExecutionEnv}
    (haccount : ∃ acc, σ.find? I.codeOwner = some acc) :
    UInt256.land
      (UInt256.div (auctionSlotWord ⟨0⟩ (auctionInitializeSetTopFlagsMap σ I) I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩ := by
  obtain ⟨acc, haccount⟩ := haccount
  unfold auctionInitializeSetTopFlagsMap
  rw [auctionSlotWord_store_same_present haccount, auctionInitializingByte_setFlags]
  decide


private theorem unpause_map_state (evm : EVM.State) :
    (auctionUnpausePostState evm).accountMap =
      auctionUnpausePostMap evm.accountMap evm.executionEnv := by
  simp only [auctionUnpausePostState, auctionUnpausePostMap, storageStore_accountMap,
    auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]

private theorem unpause_state_env (evm : EVM.State) :
    (auctionUnpausePostState evm).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

private theorem pause_map_state (evm : EVM.State) :
    (auctionPausePostState evm).accountMap =
      auctionPausePostMap evm.accountMap evm.executionEnv := by
  simp only [auctionPausePostState, auctionPausePostMap, storageStore_accountMap,
    auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]

private theorem pause_state_env (evm : EVM.State) :
    (auctionPausePostState evm).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

private theorem status_map_state (evm : EVM.State) :
    (auctionInitializeSetStatusState evm).accountMap =
      auctionInitializeSetStatusMap evm.accountMap evm.executionEnv := by
  exact storageStore_accountMap _ _ _ _

private theorem status_state_env (evm : EVM.State) :
    (auctionInitializeSetStatusState evm).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

private theorem address_map_state (evm : EVM.State) (slot val : UInt256) :
    (auctionInitializeSetAddressState evm slot val).accountMap =
      auctionInitializeSetAddressMap evm.accountMap evm.executionEnv slot val := by
  simp only [auctionInitializeSetAddressState, auctionInitializeSetAddressMap, storageStore_accountMap,
    auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]

private theorem address_state_env (evm : EVM.State) (slot val : UInt256) :
    (auctionInitializeSetAddressState evm slot val).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

private theorem uint_map_state (evm : EVM.State) (slot val : UInt256) :
    (auctionInitializeSetUint256State evm slot val).accountMap =
      auctionInitializeSetUint256Map evm.accountMap evm.executionEnv slot val := by
  exact storageStore_accountMap _ _ _ _

private theorem uint_state_env (evm : EVM.State) (slot val : UInt256) :
    (auctionInitializeSetUint256State evm slot val).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

private theorem minBid_map_state (evm : EVM.State) (I : ExecutionEnv)
    (hI : evm.executionEnv = I) :
    (auctionInitializeSetMinBidState evm I).accountMap =
      auctionInitializeSetMinBidMap evm.accountMap I := by
  simp only [auctionInitializeSetMinBidState, auctionInitializeSetMinBidMap,
    storageStore_accountMap, hI, auctionSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

private theorem minBid_state_env (evm : EVM.State) (I : ExecutionEnv) :
    (auctionInitializeSetMinBidState evm I).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

private theorem ownerMap_eq_addressMap (σ : AccountMap) (I : ExecutionEnv) (val : UInt256) :
    auctionSetOwnerPostMap σ I val = auctionInitializeSetAddressMap σ I ⟨151⟩ val := rfl

set_option maxHeartbeats 1000000 in
theorem auctionInitializeCorePostMap_accountMap_state (evm : EVM.State) (I : ExecutionEnv)
    (hI : evm.executionEnv = I) :
    auctionInitializeCorePostMap evm.accountMap I =
      (auctionInitializeCorePostState evm I).accountMap := by
  simp only [auctionInitializeCorePostMap, auctionInitializeArgsPostMap,
    auctionInitializeCorePostState, uint_map_state,
    uint_state_env, minBid_state_env, address_state_env, pause_state_env, status_state_env,
    unpause_state_env, hI, ownerMap_eq_addressMap]
  rw [minBid_map_state _ I (by
    simp only [uint_state_env, address_state_env, pause_state_env, status_state_env,
      unpause_state_env, hI])]
  simp only [uint_map_state, address_map_state, pause_map_state, status_map_state,
    unpause_map_state, uint_state_env, address_state_env, pause_state_env, status_state_env,
    unpause_state_env, hI]


theorem auctionInitializeCorePostMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionInitializeCorePostMap σ I)
      (auctionInitializeCorePostState (initState cA gh bl σ σ₀ g A I) I).accountMap := by
  rw [← auctionInitializeCorePostMap_accountMap_state (initState cA gh bl σ σ₀ g A I) I rfl]
  exact accountMapEquiv_refl _

theorem auctionInitializeCorePostState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (auctionInitializeCorePostState evm I).executionEnv = evm.executionEnv := by
  simp only [auctionInitializeCorePostState, auctionInitializeSetStatusState,
    auctionInitializeSetAddressState, auctionInitializeSetUint256State,
    auctionInitializeSetMinBidState, auctionUnpausePostState, auctionPausePostState,
    storageStore_executionEnv]

private theorem initializeFlags_equiv (evm : EVM.State) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (setBoolOffset0Word (auctionSetBoolOffset1TrueWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) ⟨1⟩))
      (auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm)) := by
  unfold auctionInitializeSetInitializedTrueState auctionInitializeSetInitializingTrueState
  refine ⟨?_, ?_, ?_⟩
  · simp only [storageStore_executionEnv]
  · simp only [storageStore_createdAccounts]
  · simp only [storageStore_executionEnv]
    cases haccount : evm.accountMap.find? evm.executionEnv.codeOwner with
    | none =>
        rw [storageStore_absent evm _ haccount, storageStore_absent evm _ haccount,
          storageStore_absent evm _ haccount]
        exact accountMapEquiv_refl _
    | some acc =>
        rw [storageLoad_storageStore_same_present evm _ haccount]
        simp only [storageStore_accountMap]
        exact accountMapEquiv_sstoreAccountMap_self_update _ _ _ _ _

private theorem initializeClearMap_eq_state (evm : EVM.State) (I : ExecutionEnv)
    (hI : evm.executionEnv = I) :
    auctionInitializeSetInitializingFalseMap evm.accountMap I =
      (auctionInitializeSetInitializingFalseState evm).accountMap := by
  simp only [auctionInitializeSetInitializingFalseMap, auctionInitializeSetInitializingFalseState,
    storageStore_accountMap, hI, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage]

private theorem initializeClear_equiv {s t : EVM.State} (h : EVMStateEquiv s t) :
    EVMStateEquiv (auctionInitializeSetInitializingFalseState s)
      (auctionInitializeSetInitializingFalseState t) :=
  h.storageStore_codeOwner ⟨0⟩
    (congrArg auctionSetBoolOffset1FalseWord (h.storageLoad_codeOwner ⟨0⟩))

set_option maxHeartbeats 1000000 in
theorem auctionInitializeTopPostMap_accountMap_state (evm : EVM.State) (I : ExecutionEnv)
    (hI : evm.executionEnv = I) :
    accountMapEquiv (auctionInitializeTopPostMap evm.accountMap I)
      (auctionInitializeTopPostState evm I).accountMap := by
  let compact := Solm.EVM.storageStore evm I.codeOwner ⟨0⟩
    (setBoolOffset0Word (auctionSetBoolOffset1TrueWord
      (auctionSlotWord ⟨0⟩ evm.accountMap I)) ⟨1⟩)
  have henv : compact.executionEnv = I := (storageStore_executionEnv _ _ _ _).trans hI
  have hmap : compact.accountMap = auctionInitializeSetTopFlagsMap evm.accountMap I :=
    storageStore_accountMap _ _ _ _
  have hflags : EVMStateEquiv compact
      (auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm)) := by
    unfold compact
    rw [← hI]
    exact initializeFlags_equiv evm
  have hcore := auctionInitializeCorePostState_equiv I hflags
  have hfinal := initializeClear_equiv hcore
  have hcompact : auctionInitializeTopPostMap evm.accountMap I =
      (auctionInitializeSetInitializingFalseState
        (auctionInitializeCorePostState compact I)).accountMap := by
    unfold auctionInitializeTopPostMap
    rw [← hmap, auctionInitializeCorePostMap_accountMap_state compact I henv]
    exact initializeClearMap_eq_state _ I
      ((auctionInitializeCorePostState_executionEnv compact I).trans henv)
  rw [hcompact]
  unfold auctionInitializeTopPostState
  with_reducible exact hfinal.accountMap

attribute [local irreducible] auctionInitializeTopPostMap auctionInitializeTopPostState

theorem auctionInitializeTopPostMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionInitializeTopPostMap σ I)
      (auctionInitializeTopPostState (initState cA gh bl σ σ₀ g A I) I).accountMap := by
  exact auctionInitializeTopPostMap_accountMap_state (initState cA gh bl σ σ₀ g A I) I rfl

end Auction
