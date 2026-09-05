import Benchmarks.Dss.Clipper.KickSourceFinish
import Benchmarks.Dss.Clipper.KickTailEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unusedTactic false

/-! Relate the compiler's account-map updates to the source interpreter's state updates. -/

theorem clipperKickSlotWord_eq_of_accountMapEquiv
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256)
    (henv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    solcSlotWord σ I slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  rw [henv]
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord] using hslot

theorem clipperKickSalesBaseSlot_eq (evm : EVM.State) (σ : AccountMap)
    (I : ExecutionEnv)
    (hid : clipperKickSourceIdWord evm = clipperKickIdWord σ I) :
    clipperKickSourceSalesBaseSlot evm = clipperKickSalesBaseSlot σ I := by
  unfold clipperKickSourceSalesBaseSlot clipperKickSourceIdKey salesBase mapSlot
    clipperKickSalesBaseSlot solcMappingSlot
  rw [keyValueToWord_uint256, hid]

theorem clipperKickStorageStore_present (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : evm.accountMap.find? addr = some acc) :
    ∃ acc', (Solm.EVM.storageStore evm addr slot val).accountMap.find? addr = some acc' := by
  unfold Solm.EVM.storageStore State.lookupAccount
  rw [hacc]
  simp [Option.option, State.setAccount, accountMap_find_insert_self]

theorem clipperKickSalesUint96Mask_idempotent (w : UInt256) :
    UInt256.land (UInt256.land w clipperSalesUint96Mask) clipperSalesUint96Mask =
      UInt256.land w clipperSalesUint96Mask := by
  apply u256_inj
  rw [u256_land_toNat]
  rw [u256_land_toNat]
  have hmask : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by native_decide
  rw [hmask]
  have hlt : Nat.land w.toNat (2 ^ 96 - 1) < UInt256.size := by
    exact lt_of_le_of_lt (nat_land_le_right _ _)
      (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hlt]
  have hlt' : Nat.land (Nat.land w.toNat (2 ^ 96 - 1)) (2 ^ 96 - 1) <
      UInt256.size := by
    exact lt_of_le_of_lt (nat_land_le_right _ _)
      (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hlt']
  change (w.toNat &&& (2 ^ 96 - 1)) &&& (2 ^ 96 - 1) =
    w.toNat &&& (2 ^ 96 - 1)
  rw [Nat.land_assoc, Nat.and_self]

theorem clipperKickSetAddressWord_eq (old data : UInt256) :
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old data := by
  calc
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
        UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land old (UInt256.lnot solcAddrMask)) := by
          rw [u256_land_comm (UInt256.lnot solcAddrMask) old]
    _ = UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
          (UInt256.land data solcAddrMask) := u256_lor_comm _ _

theorem clipperKickAccountEquiv_trans {a b c : Account}
    (hab : accountEquiv a b) (hbc : accountEquiv b c) : accountEquiv a c := by
  rcases hab with ⟨hn1, hb1, hc1, hs1, ht1⟩
  rcases hbc with ⟨hn2, hb2, hc2, hs2, ht2⟩
  exact ⟨hn1.trans hn2, hb1.trans hb2, hc1.trans hc2,
    fun slot => (hs1 slot).trans (hs2 slot),
    fun slot => (ht1 slot).trans (ht2 slot)⟩

theorem clipperKickAccountMapEquiv_trans {σ τ υ : AccountMap}
    (hστ : accountMapEquiv σ τ) (hτυ : accountMapEquiv τ υ) :
    accountMapEquiv σ υ := by
  intro addr
  specialize hστ addr
  specialize hτυ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    cases hυ : υ.find? addr <;> simp [hσ, hτ, hυ] at hστ hτυ ⊢
  exact clipperKickAccountEquiv_trans hστ hτυ

theorem clipperKickInitializedState_accountMapEquiv
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hpresent : ∃ acc, evm.accountMap.find? I.codeOwner = some acc)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (clipperKickInitializedMap σ I)
      (clipperKickSourceInitializedState evm I).accountMap := by
  let evmId := clipperKickSourceIdState evm
  let evmLen := clipperKickSourceActiveLengthState evm
  let evmActive := clipperKickSourceActiveState evm
  let evmPos := clipperKickSourceSalesPosState evm
  let evmTab := clipperKickSourceSalesTabState evm I
  let evmLot := clipperKickSourceSalesLotState evm I
  let evmUsr := clipperKickSourceSalesUsrState evm I
  let σId := clipperKickIdMap σ I
  let σLen := clipperKickActiveLengthMap σ I
  let σActive := clipperKickActiveMap σ I
  let σPos := clipperKickSalesPosMap σ I
  let σTab := clipperKickSalesTabMap σ I
  let σLot := clipperKickSalesLotMap σ I
  have howner : evm.executionEnv.codeOwner = I.codeOwner := by rw [henv]
  have hid : clipperKickSourceIdWord evm = clipperKickIdWord σ I := by
    rw [clipperKickSourceIdWord, clipperKickIdWord,
      ← clipperKickSlotWord_eq_of_accountMapEquiv evm I ⟨10⟩ henv hAccounts]
  have henvId : evmId.executionEnv = I := by
    simp [evmId, clipperKickSourceIdState, storageStore_executionEnv, henv]
  have hownerId : evmId.executionEnv.codeOwner = I.codeOwner :=
    congrArg ExecutionEnv.codeOwner henvId
  have hId : accountMapEquiv σId evmId.accountMap := by
    simpa [σId, evmId, clipperKickIdMap, clipperKickSourceIdState,
      storageStore_accountMap, howner, hid] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩
        (clipperKickIdWord σ I) hAccounts
  have hlen : clipperKickSourceActiveLengthWord evm =
      clipperKickActiveLengthWord σ I := by
    simpa [clipperKickSourceActiveLengthWord, clipperKickActiveLengthWord,
      evmId, σId, howner, hownerId] using
      (clipperKickSlotWord_eq_of_accountMapEquiv evmId I ⟨11⟩ henvId hId).symm
  have henvLen : evmLen.executionEnv = I := by
    dsimp only [evmLen]
    rw [clipperKickSourceActiveLengthState, storageStore_executionEnv]
    exact henvId
  have hLen : accountMapEquiv σLen evmLen.accountMap := by
    simpa [σLen, σId, evmLen, evmId, clipperKickActiveLengthMap,
      clipperKickSourceActiveLengthState, storageStore_accountMap, henvId,
      hlen] using accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩
        (clipperKickActiveLengthWord σ I + ⟨1⟩) hId
  have helem : clipperKickSourceActiveElemSlot evm =
      clipperKickActiveElemSlot σ I := by
    simp only [clipperKickSourceActiveElemSlot, clipperKickActiveElemSlot, hlen]
    exact u256_add_comm _ _
  have henvActive : evmActive.executionEnv = I := by
    dsimp only [evmActive]
    rw [clipperKickSourceActiveState, storageStore_executionEnv]
    exact henvLen
  have hActive : accountMapEquiv σActive evmActive.accountMap := by
    simpa [σActive, σLen, evmActive, evmLen, clipperKickActiveMap,
      clipperKickSourceActiveState, storageStore_accountMap, henvLen,
      helem, hid] using accountMapEquiv_sstoreAccountMap I.codeOwner
        (clipperKickActiveElemSlot σ I) (clipperKickIdWord σ I) hLen
  have hpostLen : clipperKickSourcePostPushLengthWord evm =
      clipperKickPostPushLengthWord σ I := by
    simpa [clipperKickSourcePostPushLengthWord, clipperKickPostPushLengthWord,
      evmActive, σActive, henvActive] using
      (clipperKickSlotWord_eq_of_accountMapEquiv evmActive I ⟨11⟩
        henvActive hActive).symm
  have hpos : clipperKickSourceActivePosWord evm =
      clipperKickActivePosWord σ I := by
    simp only [clipperKickSourceActivePosWord, clipperKickActivePosWord, hpostLen]
    exact clipperSubOne_eq_addNotZero _
  have hbase : clipperKickSourceSalesBaseSlot evm =
      clipperKickSalesBaseSlot σ I := clipperKickSalesBaseSlot_eq evm σ I hid
  have henvPos : evmPos.executionEnv = I := by
    dsimp only [evmPos]
    rw [clipperKickSourceSalesPosState, storageStore_executionEnv]
    exact henvActive
  have hPos : accountMapEquiv σPos evmPos.accountMap := by
    simpa [σPos, σActive, evmPos, evmActive, clipperKickSalesPosMap,
      clipperKickSourceSalesPosState, storageStore_accountMap, henvActive,
      hbase, hpos] using accountMapEquiv_sstoreAccountMap I.codeOwner
        (clipperKickSalesBaseSlot σ I) (clipperKickActivePosWord σ I) hActive
  have henvTab : evmTab.executionEnv = I := by
    dsimp only [evmTab]
    rw [clipperKickSourceSalesTabState, storageStore_executionEnv]
    exact henvPos
  have hTab : accountMapEquiv σTab evmTab.accountMap := by
    simpa [σTab, σPos, evmTab, evmPos, clipperKickSalesTabMap,
      clipperKickSourceSalesTabState, storageStore_accountMap, henvPos,
      hbase] using accountMapEquiv_sstoreAccountMap I.codeOwner
        (clipperKickSalesBaseSlot σ I + ⟨1⟩) (clipperKickTabWord I) hPos
  have henvLot : evmLot.executionEnv = I := by
    dsimp only [evmLot]
    rw [clipperKickSourceSalesLotState, storageStore_executionEnv]
    exact henvTab
  have hLot : accountMapEquiv σLot evmLot.accountMap := by
    simpa [σLot, σTab, evmLot, evmTab, clipperKickSalesLotMap,
      clipperKickSourceSalesLotState, storageStore_accountMap, henvTab,
      hbase] using accountMapEquiv_sstoreAccountMap I.codeOwner
        (clipperKickSalesBaseSlot σ I + ⟨2⟩) (clipperKickLotWord I) hTab
  obtain ⟨acc0, hacc0⟩ := hpresent
  have hacc0' : evm.accountMap.find? evm.executionEnv.codeOwner = some acc0 := by
    simpa [howner] using hacc0
  obtain ⟨accId, haccId⟩ := clipperKickStorageStore_present evm
    evm.executionEnv.codeOwner ⟨10⟩ (clipperKickSourceIdWord evm) hacc0'
  obtain ⟨accLen, haccLen⟩ := clipperKickStorageStore_present evmId
    evmId.executionEnv.codeOwner ⟨11⟩
      (clipperKickSourceActiveLengthWord evm + ⟨1⟩) (by
        simpa [evmId, clipperKickSourceIdState, storageStore_executionEnv] using haccId)
  obtain ⟨accActive, haccActive⟩ := clipperKickStorageStore_present evmLen
    evmLen.executionEnv.codeOwner (clipperKickSourceActiveElemSlot evm)
      (clipperKickSourceIdWord evm) (by
        simpa [evmLen, clipperKickSourceActiveLengthState,
          storageStore_executionEnv] using haccLen)
  obtain ⟨accPos, haccPos⟩ := clipperKickStorageStore_present evmActive
    evmActive.executionEnv.codeOwner (clipperKickSourceSalesBaseSlot evm)
      (clipperKickSourceActivePosWord evm) (by
        simpa [evmActive, clipperKickSourceActiveState,
          storageStore_executionEnv] using haccActive)
  obtain ⟨accTab, haccTab⟩ := clipperKickStorageStore_present evmPos
    evmPos.executionEnv.codeOwner (clipperKickSourceSalesBaseSlot evm + ⟨1⟩)
      (clipperKickTabWord I) (by
        simpa [evmPos, clipperKickSourceSalesPosState,
          storageStore_executionEnv] using haccPos)
  obtain ⟨accLot, haccLot⟩ := clipperKickStorageStore_present evmTab
    evmTab.executionEnv.codeOwner (clipperKickSourceSalesBaseSlot evm + ⟨2⟩)
      (clipperKickLotWord I) (by
        simpa [evmTab, clipperKickSourceSalesTabState,
          storageStore_executionEnv] using haccTab)
  let slot := clipperKickPackedSlot σ I
  let old := solcSlotWord σLot I slot
  let usrVal := setAddressOffset0Word old (clipperKickUsrMaskedWord I)
  let σUsr := sstoreAccountMap I.codeOwner σLot slot usrVal
  have hsourceSlot : clipperKickSourceSalesBaseSlot evm + ⟨3⟩ = slot := by
    simp [slot, clipperKickPackedSlot, hbase, u256_add_comm]
  have hold : Solm.EVM.storageLoad evmLot evmLot.executionEnv.codeOwner
      (clipperKickSourceSalesBaseSlot evm + ⟨3⟩) = old := by
    have hread := clipperKickSlotWord_eq_of_accountMapEquiv evmLot I slot henvLot hLot
    simpa [old, hsourceSlot] using hread.symm
  have hold' : Solm.EVM.storageLoad evmLot I.codeOwner slot = old := by
    simpa [henvLot, hsourceSlot] using hold
  have henvUsr : evmUsr.executionEnv = I := by
    dsimp only [evmUsr]
    rw [clipperKickSourceSalesUsrState, storageStore_executionEnv]
    exact henvLot
  have hUsr : accountMapEquiv σUsr evmUsr.accountMap := by
    dsimp only [σUsr, evmUsr]
    rw [clipperKickSourceSalesUsrState, storageStore_accountMap, henvLot,
      hsourceSlot, hold']
    exact accountMapEquiv_sstoreAccountMap I.codeOwner slot usrVal hLot
  have haccLot' : evmLot.accountMap.find? evmLot.executionEnv.codeOwner = some accLot := by
    dsimp only [evmLot]
    rw [clipperKickSourceSalesLotState, storageStore_executionEnv]
    dsimp only [evmTab] at haccLot
    exact haccLot
  have husrRead : Solm.EVM.storageLoad evmUsr evmUsr.executionEnv.codeOwner
      (clipperKickSourceSalesBaseSlot evm + ⟨3⟩) = usrVal := by
    dsimp only [evmUsr]
    rw [clipperKickSourceSalesUsrState, storageStore_executionEnv]
    rw [storageLoad_storageStore_same_present evmLot
      evmLot.executionEnv.codeOwner haccLot']
    rw [hold]
  have hmask96 : clipperKickUint96Mask = clipperSalesUint96Mask := by
    native_decide
  have htime : evmUsr.executionEnv.header.timestamp = I.header.timestamp := by
    exact congrArg (fun ee => ee.header.timestamp) henvUsr
  have hpacked :
      UInt256.lor
        (UInt256.mul
          (UInt256.land
            (UInt256.land (UInt256.ofNat evmUsr.executionEnv.header.timestamp)
              clipperSalesUint96Mask)
            clipperSalesUint96Mask)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
        (UInt256.land
          (Solm.EVM.storageLoad evmUsr evmUsr.executionEnv.codeOwner
            (clipperKickSourceSalesBaseSlot evm + ⟨3⟩)) solcAddrMask) =
        clipperKickPackedWord σ I := by
    rw [clipperKickSalesUint96Mask_idempotent, htime, husrRead]
    simp only [clipperKickPackedWord, hmask96, old, usrVal]
    rw [← clipperKickSetAddressWord_eq old (clipperKickUsrMaskedWord I)]
    rw [u256_land_comm (UInt256.ofNat I.header.timestamp) clipperSalesUint96Mask]
    rw [u256_land_comm (clipperKickUsrMaskedWord I) solcAddrMask]
  have hpacked' :
      UInt256.lor
        (UInt256.mul
          (UInt256.land
            (UInt256.land (UInt256.ofNat I.header.timestamp)
              clipperSalesUint96Mask)
            clipperSalesUint96Mask)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
        (UInt256.land
          (Solm.EVM.storageLoad (clipperKickSourceSalesUsrState evm I)
            I.codeOwner slot) solcAddrMask) =
        clipperKickPackedWord σ I := by
    simpa [evmUsr, henvUsr, hsourceSlot] using hpacked
  have hFinalFromUsr : accountMapEquiv
      (sstoreAccountMap I.codeOwner σUsr slot (clipperKickPackedWord σ I))
      (clipperKickSourceInitializedState evm I).accountMap := by
    rw [clipperKickSourceInitializedState]
    rw [storageStore_accountMap, henvUsr, hsourceSlot, hpacked']
    exact accountMapEquiv_sstoreAccountMap I.codeOwner slot
      (clipperKickPackedWord σ I) hUsr
  have hOverwrite : accountMapEquiv
      (sstoreAccountMap I.codeOwner σLot slot (clipperKickPackedWord σ I))
      (sstoreAccountMap I.codeOwner σUsr slot (clipperKickPackedWord σ I)) := by
    simpa [σUsr] using accountMapEquiv_sstoreAccountMap_self_update
      σLot I.codeOwner slot usrVal (clipperKickPackedWord σ I)
  change accountMapEquiv
    (sstoreAccountMap I.codeOwner σLot slot (clipperKickPackedWord σ I))
    (clipperKickSourceInitializedState evm I).accountMap
  exact clipperKickAccountMapEquiv_trans hOverwrite hFinalFromUsr

theorem clipperKickTopState_accountMapEquiv
    {σ : AccountMap} (evmLock evm : EVM.State) (I : ExecutionEnv)
    (id top : UInt256)
    (henv : evm.executionEnv = I)
    (hslot : clipperKickSourceSalesBaseSlot evmLock + ⟨4⟩ =
      clipperKickTopSlot id)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (clipperKickTopMap σ I id top)
      (clipperKickSourceTopState evmLock evm top).accountMap := by
  simpa [clipperKickTopMap, clipperKickSourceTopState,
    storageStore_accountMap, henv, hslot] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (clipperKickTopSlot id) top
      hAccounts

theorem clipperKickUnlockedState_accountMapEquiv
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨0⟩)
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩).accountMap := by
  simpa [storageStore_accountMap, henv] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨0⟩ hAccounts

end Benchmarks.Dss.Clipper
