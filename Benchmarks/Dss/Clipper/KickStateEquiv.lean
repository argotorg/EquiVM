import Reasoning.StateFacts
import Reasoning.WordArithmetic
import Benchmarks.Dss.Clipper.KickSourceFinish
import Benchmarks.Dss.Clipper.KickTailEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unusedTactic false

/-! Relate the compiler's account-map updates to the source interpreter's state updates. -/


theorem clipperKickSalesBaseSlot_eq (evm : EVM.State) (σ : AccountMap)
    (I : ExecutionEnv)
    (hid : clipperKickSourceIdWord evm = clipperKickIdWord σ I) :
    clipperKickSourceSalesBaseSlot evm = clipperKickSalesBaseSlot σ I := by
  unfold clipperKickSourceSalesBaseSlot clipperKickSourceIdKey salesBase mapSlot
    clipperKickSalesBaseSlot solcMappingSlot
  rw [keyValueToWord_uint256, hid]


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


theorem clipperKickInitializedState_accounts_eq
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hpresent : ∃ acc, evm.accountMap.get? I.codeOwner = some acc)
    (hAccounts : σ = evm.accountMap) :
    clipperKickInitializedMap σ I =
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
      ← slotWord_eq_of_accounts_eq evm I ⟨10⟩ henv hAccounts]
  have henvId : evmId.executionEnv = I := by
    simp [evmId, clipperKickSourceIdState, storageStore_executionEnv, henv]
  have hownerId : evmId.executionEnv.codeOwner = I.codeOwner :=
    congrArg ExecutionEnv.codeOwner henvId
  have hId : σId = evmId.accountMap := by
    simpa [σId, evmId, clipperKickIdMap, clipperKickSourceIdState,
      storageStore_accountMap, howner, hid] using
      congrArg (fun m => sstoreAccountMap I.codeOwner m ⟨10⟩
        (clipperKickIdWord σ I)) hAccounts
  have hlen : clipperKickSourceActiveLengthWord evm =
      clipperKickActiveLengthWord σ I := by
    simpa [clipperKickSourceActiveLengthWord, clipperKickActiveLengthWord,
      evmId, σId, howner, hownerId] using
      (slotWord_eq_of_accounts_eq evmId I ⟨11⟩ henvId hId).symm
  have henvLen : evmLen.executionEnv = I := by
    dsimp only [evmLen]
    rw [clipperKickSourceActiveLengthState, storageStore_executionEnv]
    exact henvId
  have hLen : σLen = evmLen.accountMap := by
    simpa [σLen, σId, evmLen, evmId, clipperKickActiveLengthMap,
      clipperKickSourceActiveLengthState, storageStore_accountMap, henvId,
      hlen] using congrArg (fun m => sstoreAccountMap I.codeOwner m ⟨11⟩
        (clipperKickActiveLengthWord σ I + ⟨1⟩)) hId
  have helem : clipperKickSourceActiveElemSlot evm =
      clipperKickActiveElemSlot σ I := by
    simp only [clipperKickSourceActiveElemSlot, clipperKickActiveElemSlot, hlen]
    exact u256_add_comm _ _
  have henvActive : evmActive.executionEnv = I := by
    dsimp only [evmActive]
    rw [clipperKickSourceActiveState, storageStore_executionEnv]
    exact henvLen
  have hActive : σActive = evmActive.accountMap := by
    simpa [σActive, σLen, evmActive, evmLen, clipperKickActiveMap,
      clipperKickSourceActiveState, storageStore_accountMap, henvLen,
      helem, hid] using congrArg (fun m => sstoreAccountMap I.codeOwner m
        (clipperKickActiveElemSlot σ I) (clipperKickIdWord σ I)) hLen
  have hpostLen : clipperKickSourcePostPushLengthWord evm =
      clipperKickPostPushLengthWord σ I := by
    simpa [clipperKickSourcePostPushLengthWord, clipperKickPostPushLengthWord,
      evmActive, σActive, henvActive] using
      (slotWord_eq_of_accounts_eq evmActive I ⟨11⟩
        henvActive hActive).symm
  have hpos : clipperKickSourceActivePosWord evm =
      clipperKickActivePosWord σ I := by
    simp only [clipperKickSourceActivePosWord, clipperKickActivePosWord, hpostLen]
    exact subOne_eq_addNotZero _
  have hbase : clipperKickSourceSalesBaseSlot evm =
      clipperKickSalesBaseSlot σ I := clipperKickSalesBaseSlot_eq evm σ I hid
  have henvPos : evmPos.executionEnv = I := by
    dsimp only [evmPos]
    rw [clipperKickSourceSalesPosState, storageStore_executionEnv]
    exact henvActive
  have hPos : σPos = evmPos.accountMap := by
    simpa [σPos, σActive, evmPos, evmActive, clipperKickSalesPosMap,
      clipperKickSourceSalesPosState, storageStore_accountMap, henvActive,
      hbase, hpos] using congrArg (fun m => sstoreAccountMap I.codeOwner m
        (clipperKickSalesBaseSlot σ I) (clipperKickActivePosWord σ I)) hActive
  have henvTab : evmTab.executionEnv = I := by
    dsimp only [evmTab]
    rw [clipperKickSourceSalesTabState, storageStore_executionEnv]
    exact henvPos
  have hTab : σTab = evmTab.accountMap := by
    simpa [σTab, σPos, evmTab, evmPos, clipperKickSalesTabMap,
      clipperKickSourceSalesTabState, storageStore_accountMap, henvPos,
      hbase] using congrArg (fun m => sstoreAccountMap I.codeOwner m
        (clipperKickSalesBaseSlot σ I + ⟨1⟩) (clipperKickTabWord I)) hPos
  have henvLot : evmLot.executionEnv = I := by
    dsimp only [evmLot]
    rw [clipperKickSourceSalesLotState, storageStore_executionEnv]
    exact henvTab
  have hLot : σLot = evmLot.accountMap := by
    simpa [σLot, σTab, evmLot, evmTab, clipperKickSalesLotMap,
      clipperKickSourceSalesLotState, storageStore_accountMap, henvTab,
      hbase] using congrArg (fun m => sstoreAccountMap I.codeOwner m
        (clipperKickSalesBaseSlot σ I + ⟨2⟩) (clipperKickLotWord I)) hTab
  obtain ⟨acc0, hacc0⟩ := hpresent
  have hacc0' : evm.accountMap.get? evm.executionEnv.codeOwner = some acc0 := by
    simpa [howner] using hacc0
  obtain ⟨accId, haccId⟩ := storageStore_present evm
    evm.executionEnv.codeOwner ⟨10⟩ (clipperKickSourceIdWord evm) hacc0'
  obtain ⟨accLen, haccLen⟩ := storageStore_present evmId
    evmId.executionEnv.codeOwner ⟨11⟩
      (clipperKickSourceActiveLengthWord evm + ⟨1⟩) (by
        simpa [evmId, clipperKickSourceIdState, storageStore_executionEnv] using haccId)
  obtain ⟨accActive, haccActive⟩ := storageStore_present evmLen
    evmLen.executionEnv.codeOwner (clipperKickSourceActiveElemSlot evm)
      (clipperKickSourceIdWord evm) (by
        simpa [evmLen, clipperKickSourceActiveLengthState,
          storageStore_executionEnv] using haccLen)
  obtain ⟨accPos, haccPos⟩ := storageStore_present evmActive
    evmActive.executionEnv.codeOwner (clipperKickSourceSalesBaseSlot evm)
      (clipperKickSourceActivePosWord evm) (by
        simpa [evmActive, clipperKickSourceActiveState,
          storageStore_executionEnv] using haccActive)
  obtain ⟨accTab, haccTab⟩ := storageStore_present evmPos
    evmPos.executionEnv.codeOwner (clipperKickSourceSalesBaseSlot evm + ⟨1⟩)
      (clipperKickTabWord I) (by
        simpa [evmPos, clipperKickSourceSalesPosState,
          storageStore_executionEnv] using haccPos)
  obtain ⟨accLot, haccLot⟩ := storageStore_present evmTab
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
    have hread := slotWord_eq_of_accounts_eq evmLot I slot henvLot hLot
    simpa [old, hsourceSlot] using hread.symm
  have hold' : Solm.EVM.storageLoad evmLot I.codeOwner slot = old := by
    simpa [henvLot, hsourceSlot] using hold
  have henvUsr : evmUsr.executionEnv = I := by
    dsimp only [evmUsr]
    rw [clipperKickSourceSalesUsrState, storageStore_executionEnv]
    exact henvLot
  have hUsr : σUsr = evmUsr.accountMap := by
    dsimp only [σUsr, evmUsr]
    rw [clipperKickSourceSalesUsrState, storageStore_accountMap, henvLot,
      hsourceSlot, hold']
    exact congrArg (fun m => sstoreAccountMap I.codeOwner m slot usrVal) hLot
  have haccLot' : evmLot.accountMap.get? evmLot.executionEnv.codeOwner = some accLot := by
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
    rw [← ctorSetAddressWord_eq old (clipperKickUsrMaskedWord I)]
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
  have hFinalFromUsr :
      (sstoreAccountMap I.codeOwner σUsr slot (clipperKickPackedWord σ I))
      = (clipperKickSourceInitializedState evm I).accountMap := by
    rw [clipperKickSourceInitializedState]
    rw [storageStore_accountMap, henvUsr, hsourceSlot, hpacked']
    exact congrArg (fun m => sstoreAccountMap I.codeOwner m slot
      (clipperKickPackedWord σ I)) hUsr
  have hOverwrite :
      (sstoreAccountMap I.codeOwner σLot slot (clipperKickPackedWord σ I))
      = (sstoreAccountMap I.codeOwner σUsr slot (clipperKickPackedWord σ I)) := by
    simpa [σUsr] using sstoreAccountMap_self_update
      σLot I.codeOwner slot usrVal (clipperKickPackedWord σ I)
  change
    (sstoreAccountMap I.codeOwner σLot slot (clipperKickPackedWord σ I))
    = (clipperKickSourceInitializedState evm I).accountMap
  exact hOverwrite.trans hFinalFromUsr

theorem clipperKickTopState_accounts_eq
    {σ : AccountMap} (evmLock evm : EVM.State) (I : ExecutionEnv)
    (id top : UInt256)
    (henv : evm.executionEnv = I)
    (hslot : clipperKickSourceSalesBaseSlot evmLock + ⟨4⟩ =
      clipperKickTopSlot id)
    (hAccounts : σ = evm.accountMap) :
    clipperKickTopMap σ I id top =
      (clipperKickSourceTopState evmLock evm top).accountMap := by
  simpa [clipperKickTopMap, clipperKickSourceTopState,
    storageStore_accountMap, henv, hslot] using
    congrArg (fun m => sstoreAccountMap I.codeOwner m
      (clipperKickTopSlot id) top) hAccounts

theorem clipperKickUnlockedState_accounts_eq
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hAccounts : σ = evm.accountMap) :
    sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨0⟩ =
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩).accountMap := by
  simpa [storageStore_accountMap, henv] using
    congrArg (fun m => sstoreAccountMap I.codeOwner m ⟨13⟩ ⟨0⟩) hAccounts

end Benchmarks.Dss.Clipper
