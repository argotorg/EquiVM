import Benchmarks.Dss.Flapper.Bids
import Benchmarks.Dss.Flapper.Cage
import Benchmarks.Dss.Flopper.AuctionCommon
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper
/-! ## `yank(uint256)` -/

abbrev auctionIdKey (id : UInt256) : KeyValue :=
  .int (Int.ofNat id.toNat)

abbrev auctionBaseSlot (id : UInt256) : UInt256 :=
  bidsBase (auctionIdKey id)

abbrev auctionBidSlot (id : UInt256) : UInt256 :=
  auctionBaseSlot id

abbrev auctionLotSlot (id : UInt256) : UInt256 :=
  auctionBaseSlot id + ⟨1⟩

abbrev auctionPackedSlot (id : UInt256) : UInt256 :=
  auctionBaseSlot id + ⟨2⟩

theorem auctionBaseSlot_eq (id : UInt256) :
    auctionBaseSlot id = solcMappingSlot ⟨1⟩ id := by
  unfold auctionBaseSlot bidsBase auctionIdKey mapSlot solcMappingSlot
  rw [keyValueToWord_uint256]

theorem auctionBidSlot_eq (id : UInt256) :
    auctionBidSlot id = solcMappingSlot ⟨1⟩ id := by
  exact auctionBaseSlot_eq id

theorem auctionLotSlot_eq (id : UInt256) :
    auctionLotSlot id = solcMappingSlot ⟨1⟩ id + ⟨1⟩ := by
  simp [auctionLotSlot, auctionBaseSlot_eq]

theorem auctionPackedSlot_eq (id : UInt256) :
    auctionPackedSlot id = solcMappingSlot ⟨1⟩ id + ⟨2⟩ := by
  simp [auctionPackedSlot, auctionBaseSlot_eq]

theorem auctionBidLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "bid"] } evm =
      some (uint256Loc (auctionBidSlot id)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionBidSlot,
    auctionBaseSlot, bidsBase, auctionIdKey, wordLoc, uint256Loc, uint256Int]

theorem auctionLotLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "lot"] } evm =
      some (uint256Loc (auctionLotSlot id)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionLotSlot,
    auctionBaseSlot, bidsBase, auctionIdKey, wordLoc, uint256Loc, uint256Int]

theorem auctionGuyLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "guy"] } evm =
      some (addrLoc (auctionPackedSlot id)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionPackedSlot,
    auctionBaseSlot, bidsBase, auctionIdKey]

theorem auctionTicLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "tic"] } evm =
      some (uint48Loc (auctionPackedSlot id) ⟨20, by decide⟩ (by decide)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionPackedSlot,
    auctionBaseSlot, bidsBase, auctionIdKey]

theorem auctionEndLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "end"] } evm =
      some (uint48Loc (auctionPackedSlot id) ⟨26, by decide⟩ (by decide)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionPackedSlot,
    auctionBaseSlot, bidsBase, auctionIdKey]

abbrev clearUint48Offset20Word : UInt256 → UInt256 :=
  Benchmarks.Dss.Flopper.clearUint48Offset20Word

abbrev clearUint48Offset26Word : UInt256 → UInt256 :=
  Benchmarks.Dss.Flopper.clearUint48Offset26Word

theorem clearStorage_uint256_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : cfg.storage.layout er evm = some (uint256Loc slot)) :
    clearStorage? cfg evm er uint256St =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩) :=
  Benchmarks.Dss.Flopper.clearStorage_uint256_zero hloc

theorem clearStorage_addr_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : cfg.storage.layout er evm = some (addrLoc slot)) :
    clearStorage? cfg evm er addrSt =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) :=
  Benchmarks.Dss.Flopper.clearStorage_addr_zero hloc

theorem clearStorage_uint48_offset20_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      cfg.storage.layout er evm = some (uint48Loc slot ⟨20, by decide⟩ (by decide))) :
    clearStorage? cfg evm er uint48St =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset20Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) :=
  Benchmarks.Dss.Flopper.clearStorage_uint48_offset20_zero hloc

theorem clearStorage_uint48_offset26_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      cfg.storage.layout er evm = some (uint48Loc slot ⟨26, by decide⟩ (by decide))) :
    clearStorage? cfg evm er uint48St =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset26Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) :=
  Benchmarks.Dss.Flopper.clearStorage_uint48_offset26_zero hloc

theorem clearUint48Offset26Word_zero :
    clearUint48Offset26Word ⟨0⟩ = ⟨0⟩ :=
  Benchmarks.Dss.Flopper.clearUint48Offset26Word_zero

theorem clearUint48Offset26_after_offset20_after_address_zero (old : UInt256) :
    clearUint48Offset26Word
        (clearUint48Offset20Word (setAddressOffset0Word old ⟨0⟩)) =
      ⟨0⟩ :=
  Benchmarks.Dss.Flopper.clearUint48Offset26_after_offset20_after_address_zero old

theorem twoWordHashMem_solcMappingSlot_any (baseSlot key : UInt256) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key :=
  Benchmarks.Dss.Flopper.twoWordHashMem_solcMappingSlot_any baseSlot key mem

theorem flapperSlotWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperSlotWord slot σ I = flapperSlotWord slot τ I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩

theorem flapperAddressReturnWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperAddressReturnWord slot σ I = flapperAddressReturnWord slot τ I := by
  simp [flapperAddressReturnWord, flapperSlotWord_accountMapEquiv hAccounts slot]

theorem flapperAddressOfSlot_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    AccountAddress.ofNat (flapperAddressReturnWord slot σ I).toNat =
      AccountAddress.ofNat (flapperAddressReturnWord slot τ I).toNat := by
  simp [flapperAddressReturnWord_accountMapEquiv hAccounts slot]

theorem flapperCodeSize_ne_accountMapEquiv_addressSlot {σ τ : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ) (slot : UInt256)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord slot σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (flapperAddressReturnWord slot τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (flapperAddressReturnWord slot σ I)
  have htarget :
      flapperAddressReturnWord slot σ I = flapperAddressReturnWord slot τ I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts slot
  rw [hsame, htarget]
  exact hzero

theorem flapperCodeSize_zero_accountMapEquiv_addressSlot {σ τ : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ) (slot : UInt256)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord slot σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (flapperAddressReturnWord slot τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (flapperAddressReturnWord slot σ I)
  have htarget :
      flapperAddressReturnWord slot σ I = flapperAddressReturnWord slot τ I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts slot
  rw [← htarget, ← hsame]
  exact hzero

abbrev yankIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev yankIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (yankIdWord I).toNat)

abbrev yankLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (yankIdValue I)

abbrev yankMoveLocals (I : ExecutionEnv) : Store :=
  (yankLocals I).insert "_moveRet" (collapseReturns [])

theorem yankMoveLocals_get_id (I : ExecutionEnv) :
    (yankMoveLocals I).get? "id" = some (yankIdValue I) := by
  rw [yankMoveLocals, store_get_ne _ _ (by decide)]
  simp [yankLocals]

theorem yankMoveLocals_getElem_id (I : ExecutionEnv) :
    (yankMoveLocals I)["id"]? = some (yankIdValue I) := by
  simpa [Std.HashMap.get?_eq_getElem?] using yankMoveLocals_get_id I

theorem yankMoveLocals_get_bids (I : ExecutionEnv) :
    (yankMoveLocals I).get? "bids" = none := by
  rw [yankMoveLocals, store_get_ne _ _ (by decide)]
  rw [yankLocals, store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem evalStorageRef_yank_bid (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := yankMoveLocals I } evm
        (bidRef (.var "id")) =
      .ok { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] } := by
  simp [bidRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    yankMoveLocals, yankLocals, yankIdValue,
    auctionIdKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    Std.HashMap.getElem_insert]

theorem resolveStorageRef_yankMove_bid (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config { contract := contract, locals := yankMoveLocals I } evm
      (bidRef (.var "id")) =
      .ok ({ base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] }, BidStructTy) := by
  rw [resolveStorageRef?]
  simp only [bidRef]
  rw [yankMoveLocals_get_bids I]
  rw [show evalStorageRef config { contract := contract, locals := yankMoveLocals I } evm
      { base := "bids", steps := [StorageRefStep.mindex (.var "id")] } =
        .ok { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] } by
    simpa [bidRef] using evalStorageRef_yank_bid evm I]
  simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, BidStructTy,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

def yankDeleteAfterBid (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionBidSlot (yankIdWord I)) ⟨0⟩

def yankDeleteAfterLot (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (yankDeleteAfterBid evm I)
    (yankDeleteAfterBid evm I).executionEnv.codeOwner (auctionLotSlot (yankIdWord I)) ⟨0⟩

def yankDeleteAfterGuy (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (yankDeleteAfterLot evm I)
    (yankDeleteAfterLot evm I).executionEnv.codeOwner (auctionPackedSlot (yankIdWord I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad (yankDeleteAfterLot evm I)
        (yankDeleteAfterLot evm I).executionEnv.codeOwner (auctionPackedSlot (yankIdWord I)))
      ⟨0⟩)

def yankDeleteAfterTic (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (yankDeleteAfterGuy evm I)
    (yankDeleteAfterGuy evm I).executionEnv.codeOwner (auctionPackedSlot (yankIdWord I))
    (clearUint48Offset20Word
      (Solm.EVM.storageLoad (yankDeleteAfterGuy evm I)
        (yankDeleteAfterGuy evm I).executionEnv.codeOwner (auctionPackedSlot (yankIdWord I))))

def yankDeletePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (yankDeleteAfterTic evm I)
    (yankDeleteAfterTic evm I).executionEnv.codeOwner (auctionPackedSlot (yankIdWord I))
    (clearUint48Offset26Word
      (Solm.EVM.storageLoad (yankDeleteAfterTic evm I)
        (yankDeleteAfterTic evm I).executionEnv.codeOwner (auctionPackedSlot (yankIdWord I))))

def yankRuntimeDeleteAccountMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ (auctionBidSlot (yankIdWord I)) ⟨0⟩)
      (auctionLotSlot (yankIdWord I)) ⟨0⟩)
    (auctionPackedSlot (yankIdWord I)) ⟨0⟩

theorem deleteStorage_yankMove_bid (evm : EVM.State) (I : ExecutionEnv) :
    deleteStorage? config { contract := contract, locals := yankMoveLocals I } evm
      (bidRef (.var "id")) = .ok (yankDeletePostState evm I) := by
  rw [deleteStorage?]
  rw [resolveStorageRef_yankMove_bid]
  simp only [EvalResult.bind, bind]
  rw [Solm.clearStorage?.eq_def]
  simp only [BidStructTy]
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint256_zero (slot := auctionBidSlot (yankIdWord I))
    (hloc := auctionBidLayout evm (yankIdWord I))]
  change clearFields? config (yankDeleteAfterBid evm I)
      { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] }
      [("lot", uint256St), ("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (yankDeletePostState evm I)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint256_zero (slot := auctionLotSlot (yankIdWord I))
    (hloc := auctionLotLayout (yankDeleteAfterBid evm I) (yankIdWord I))]
  change clearFields? config (yankDeleteAfterLot evm I)
      { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] }
      [("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (yankDeletePostState evm I)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_addr_zero (slot := auctionPackedSlot (yankIdWord I))
    (hloc := auctionGuyLayout (yankDeleteAfterLot evm I) (yankIdWord I))]
  change clearFields? config (yankDeleteAfterGuy evm I)
      { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] }
      [("tic", uint48St), ("end", uint48St)] =
    .ok (yankDeletePostState evm I)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint48_offset20_zero (slot := auctionPackedSlot (yankIdWord I))
    (hloc := auctionTicLayout (yankDeleteAfterGuy evm I) (yankIdWord I))]
  change clearFields? config (yankDeleteAfterTic evm I)
      { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] }
      [("end", uint48St)] =
    .ok (yankDeletePostState evm I)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint48_offset26_zero (slot := auctionPackedSlot (yankIdWord I))
    (hloc := auctionEndLayout (yankDeleteAfterTic evm I) (yankIdWord I))]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp [yankDeletePostState]

theorem yankDeletePackedFinalWord_zero (evm : EVM.State) (I : ExecutionEnv) :
    clearUint48Offset26Word
        (Solm.EVM.storageLoad (yankDeleteAfterTic evm I)
          (yankDeleteAfterTic evm I).executionEnv.codeOwner
          (auctionPackedSlot (yankIdWord I))) =
      ⟨0⟩ := by
  by_cases hacc0 : evm.accountMap.find? evm.executionEnv.codeOwner = none
  · have hbid : yankDeleteAfterBid evm I = evm := by
      exact storageStore_absent evm evm.executionEnv.codeOwner hacc0
        (auctionBidSlot (yankIdWord I)) ⟨0⟩
    have hlot : yankDeleteAfterLot evm I = evm := by
      simp [yankDeleteAfterLot, hbid,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0
          (auctionLotSlot (yankIdWord I)) ⟨0⟩]
    have hguy : yankDeleteAfterGuy evm I = evm := by
      simp [yankDeleteAfterGuy, hlot,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0
          (auctionPackedSlot (yankIdWord I))
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (auctionPackedSlot (yankIdWord I))) ⟨0⟩)]
    have htic : yankDeleteAfterTic evm I = evm := by
      simp [yankDeleteAfterTic, hguy,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0
          (auctionPackedSlot (yankIdWord I))
          (clearUint48Offset20Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (auctionPackedSlot (yankIdWord I))))]
    have hload :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot (yankIdWord I)) =
          ⟨0⟩ := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hacc0, Option.option]
    rw [htic, hload]
    exact clearUint48Offset26Word_zero
  · obtain ⟨_, hacc0some⟩ := Option.ne_none_iff_exists'.mp hacc0
    have haccLotExists :
        ∃ acc, (yankDeleteAfterLot evm I).accountMap.find?
          (yankDeleteAfterLot evm I).executionEnv.codeOwner = some acc := by
      simp [yankDeleteAfterLot, yankDeleteAfterBid, Solm.EVM.storageStore,
        State.lookupAccount, hacc0some, Option.option, State.setAccount,
        accountMap_find_insert_self]
    obtain ⟨_, haccLot⟩ := haccLotExists
    have hloadGuy :
        Solm.EVM.storageLoad (yankDeleteAfterGuy evm I)
            (yankDeleteAfterGuy evm I).executionEnv.codeOwner
            (auctionPackedSlot (yankIdWord I)) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad (yankDeleteAfterLot evm I)
              (yankDeleteAfterLot evm I).executionEnv.codeOwner
              (auctionPackedSlot (yankIdWord I))) ⟨0⟩ := by
      rw [show (yankDeleteAfterGuy evm I).executionEnv =
          (yankDeleteAfterLot evm I).executionEnv by
        simp [yankDeleteAfterGuy, storageStore_executionEnv]]
      exact storageLoad_storageStore_same_present (yankDeleteAfterLot evm I)
        (yankDeleteAfterLot evm I).executionEnv.codeOwner haccLot
        (auctionPackedSlot (yankIdWord I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad (yankDeleteAfterLot evm I)
            (yankDeleteAfterLot evm I).executionEnv.codeOwner
            (auctionPackedSlot (yankIdWord I))) ⟨0⟩)
    have haccGuyExists :
        ∃ acc, (yankDeleteAfterGuy evm I).accountMap.find?
          (yankDeleteAfterGuy evm I).executionEnv.codeOwner = some acc := by
      simp [yankDeleteAfterGuy, haccLot, Solm.EVM.storageStore, State.lookupAccount,
        Option.option, State.setAccount, accountMap_find_insert_self]
    obtain ⟨_, haccGuy⟩ := haccGuyExists
    have hloadTic :
        Solm.EVM.storageLoad (yankDeleteAfterTic evm I)
            (yankDeleteAfterTic evm I).executionEnv.codeOwner
            (auctionPackedSlot (yankIdWord I)) =
          clearUint48Offset20Word
            (Solm.EVM.storageLoad (yankDeleteAfterGuy evm I)
              (yankDeleteAfterGuy evm I).executionEnv.codeOwner
              (auctionPackedSlot (yankIdWord I))) := by
      rw [show (yankDeleteAfterTic evm I).executionEnv =
          (yankDeleteAfterGuy evm I).executionEnv by
        simp [yankDeleteAfterTic, storageStore_executionEnv]]
      exact storageLoad_storageStore_same_present (yankDeleteAfterGuy evm I)
        (yankDeleteAfterGuy evm I).executionEnv.codeOwner haccGuy
        (auctionPackedSlot (yankIdWord I))
        (clearUint48Offset20Word
          (Solm.EVM.storageLoad (yankDeleteAfterGuy evm I)
            (yankDeleteAfterGuy evm I).executionEnv.codeOwner
            (auctionPackedSlot (yankIdWord I))))
    rw [hloadTic, hloadGuy]
    exact clearUint48Offset26_after_offset20_after_address_zero _

set_option maxHeartbeats 1000000 in
theorem yankDeletePostState_accountMapEquiv (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    accountMapEquiv (yankRuntimeDeleteAccountMap I evm.accountMap)
      (yankDeletePostState evm I).accountMap := by
  let owner := evm.executionEnv.codeOwner
  let bidSlot := auctionBidSlot (yankIdWord I)
  let lotSlot := auctionLotSlot (yankIdWord I)
  let packedSlot := auctionPackedSlot (yankIdWord I)
  let m2 :=
    sstoreAccountMap owner (sstoreAccountMap owner evm.accountMap bidSlot ⟨0⟩)
      lotSlot ⟨0⟩
  let vGuy :=
    setAddressOffset0Word
      (Solm.EVM.storageLoad (yankDeleteAfterLot evm I)
        (yankDeleteAfterLot evm I).executionEnv.codeOwner packedSlot) ⟨0⟩
  let vTic :=
    clearUint48Offset20Word
      (Solm.EVM.storageLoad (yankDeleteAfterGuy evm I)
        (yankDeleteAfterGuy evm I).executionEnv.codeOwner packedSlot)
  let vEnd :=
    clearUint48Offset26Word
      (Solm.EVM.storageLoad (yankDeleteAfterTic evm I)
        (yankDeleteAfterTic evm I).executionEnv.codeOwner packedSlot)
  have hfinal : vEnd = ⟨0⟩ := by
    simpa [vEnd, packedSlot] using yankDeletePackedFinalWord_zero evm I
  have h1 :
      accountMapEquiv (sstoreAccountMap owner m2 packedSlot vEnd)
        (sstoreAccountMap owner (sstoreAccountMap owner m2 packedSlot vGuy) packedSlot vEnd) :=
    accountMapEquiv_sstoreAccountMap_self_update m2 owner packedSlot vGuy vEnd
  have h2 :
      accountMapEquiv
        (sstoreAccountMap owner (sstoreAccountMap owner m2 packedSlot vGuy) packedSlot vEnd)
        (sstoreAccountMap owner
          (sstoreAccountMap owner (sstoreAccountMap owner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd) :=
    accountMapEquiv_sstoreAccountMap_self_update
      (sstoreAccountMap owner m2 packedSlot vGuy) owner packedSlot vTic vEnd
  have h := accountMapEquiv.trans h1 h2
  have hleftEq :
      sstoreAccountMap owner m2 packedSlot vEnd =
        sstoreAccountMap owner m2 packedSlot ⟨0⟩ := by
    rw [hfinal]
  have h' :
      accountMapEquiv (sstoreAccountMap owner m2 packedSlot ⟨0⟩)
        (sstoreAccountMap owner
          (sstoreAccountMap owner (sstoreAccountMap owner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd) := by
    simpa [hleftEq] using h
  simpa [yankRuntimeDeleteAccountMap, yankDeletePostState, yankDeleteAfterTic,
    yankDeleteAfterGuy, yankDeleteAfterLot, yankDeleteAfterBid, m2, owner, bidSlot, lotSlot,
    packedSlot, vGuy, vTic, vEnd, howner, storageStore_accountMap, storageStore_executionEnv]
    using h'

abbrev yankLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev yankGemEvaledRef : EvaledStorageRef :=
  { base := "gem", steps := [] }

abbrev yankGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I)), .field "guy"] }

abbrev yankBidEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I)), .field "bid"] }

abbrev yankThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

abbrev yankMoveSelectorWord : UInt256 :=
  ⟨0xbb35783b⟩

abbrev yankMoveSelectorShifted : UInt256 :=
  UInt256.shiftLeft yankMoveSelectorWord ⟨224⟩

abbrev yankMoveOutPtr : UInt256 := ⟨128⟩

abbrev yankMoveInSize : UInt256 := ⟨100⟩

abbrev yankMoveOutSize : UInt256 := ⟨0⟩

abbrev yankMoveEndPtr : UInt256 := ⟨228⟩

noncomputable def yankMoveSelectorMem (mem : ByteArray) : ByteArray :=
  yankMoveSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def yankMoveSrcMem (src : UInt256) (mem : ByteArray) : ByteArray :=
  src.toByteArray.write 0 (yankMoveSelectorMem mem) 132 32

noncomputable def yankMoveGuyMem (src guy : UInt256) (mem : ByteArray) : ByteArray :=
  guy.toByteArray.write 0 (yankMoveSrcMem src mem) 164 32

noncomputable def yankMoveCalldataMem (src guy bid : UInt256) (mem : ByteArray) : ByteArray :=
  bid.toByteArray.write 0 (yankMoveGuyMem src guy mem) 196 32

theorem yankMoveSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (yankMoveSelectorMem mem).size = 160 := by
  unfold yankMoveSelectorMem
  exact toByteArray_write32_size_of_ge mem yankMoveSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem yankMoveSrcMem_size (src : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (yankMoveSrcMem src mem).size = 164 := by
  unfold yankMoveSrcMem
  exact toByteArray_write32_size_of_le (yankMoveSelectorMem mem) src 132 160 164
    (yankMoveSelectorMem_size hmem)
    (by rw [yankMoveSelectorMem_size hmem]; omega) (by omega)

theorem yankMoveGuyMem_size (src guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankMoveGuyMem src guy mem).size = 196 := by
  unfold yankMoveGuyMem
  exact toByteArray_write32_size_of_le (yankMoveSrcMem src mem) guy 164 164 196
    (yankMoveSrcMem_size src hmem)
    (by rw [yankMoveSrcMem_size src hmem]) (by omega)

theorem yankMoveCalldataMem_size (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankMoveCalldataMem src guy bid mem).size = 228 := by
  unfold yankMoveCalldataMem
  exact toByteArray_write32_size_of_le (yankMoveGuyMem src guy mem) bid 196 196 228
    (yankMoveGuyMem_size src guy hmem)
    (by rw [yankMoveGuyMem_size src guy hmem]) (by omega)

theorem yankMoveSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap yankMoveSelectorShifted mem 128 64
    (by omega) (by native_decide) (by rw [hmem]; native_decide),
    hread64]

theorem yankMoveSrcMem_read64 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveSrcMem src mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveSrcMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [yankMoveSelectorMem_size hmem]; omega) (by omega),
    yankMoveSelectorMem_read64 hmem hread64]

theorem yankMoveGuyMem_read64 (src guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveGuyMem src guy mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveGuyMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [yankMoveSrcMem_size src hmem]) (by omega),
    yankMoveSrcMem_read64 src hmem hread64]

theorem yankMoveCalldataMem_read64 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [yankMoveGuyMem_size src guy hmem]) (by omega),
    yankMoveGuyMem_read64 src guy hmem hread64]

theorem yankMoveCalldataMem_read128_4 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 128 4 = moveSelector := by
  have hGuySize := yankMoveGuyMem_size src guy hmem
  have hSrcSize := yankMoveSrcMem_size src hmem
  have hSelectorSize := yankMoveSelectorMem_size hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankMoveGuyMem src guy mem) 196 128 4
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankMoveGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (yankMoveSrcMem src mem) 164 128 4
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold yankMoveSrcMem
  rw [toByteArray_write_read_below_len_of_gap src (yankMoveSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold yankMoveSelectorMem
  rw [toByteArray_write_read_window_of_gap yankMoveSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem yankMoveCalldataMem_read132_32 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 132 32 = src.toByteArray := by
  have hGuySize := yankMoveGuyMem_size src guy hmem
  have hSrcSize := yankMoveSrcMem_size src hmem
  have hSelectorSize := yankMoveSelectorMem_size hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankMoveGuyMem src guy mem) 196 132 32
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankMoveGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (yankMoveSrcMem src mem) 164 132 32
      (by rw [hSrcSize]) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold yankMoveSrcMem
  rw [toByteArray_write_read_back_of_gap src (yankMoveSelectorMem mem) 132
    (by rw [hSelectorSize]; native_decide)]

theorem yankMoveCalldataMem_read164_32 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 164 32 = guy.toByteArray := by
  have hGuySize := yankMoveGuyMem_size src guy hmem
  have hSrcSize := yankMoveSrcMem_size src hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankMoveGuyMem src guy mem) 196 164 32
      (by rw [hGuySize]) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankMoveGuyMem
  rw [toByteArray_write_read_back_of_gap guy (yankMoveSrcMem src mem) 164
    (by rw [hSrcSize]; native_decide)]

theorem yankMoveCalldataMem_read196_32 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 196 32 = bid.toByteArray := by
  have hGuySize := yankMoveGuyMem_size src guy hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_back_of_gap bid (yankMoveGuyMem src guy mem) 196
    (by rw [hGuySize]; native_decide)]

theorem yankMoveCalldataMem_read128_100 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 128 100 =
      moveSelector ++ src.toByteArray ++ guy.toByteArray ++ bid.toByteArray := by
  have hsize : (yankMoveCalldataMem src guy bid mem).size = 228 :=
    yankMoveCalldataMem_size src guy bid hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (yankMoveCalldataMem src guy bid mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (yankMoveCalldataMem src guy bid mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (yankMoveCalldataMem src guy bid mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [yankMoveCalldataMem_read128_4 src guy bid hmem,
    yankMoveCalldataMem_read132_32 src guy bid hmem,
    yankMoveCalldataMem_read164_32 src guy bid hmem,
    yankMoveCalldataMem_read196_32 src guy bid hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem flapperAddressWord_eq_ofNat_address {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    EVM.word (AccountAddress.ofNat w.toNat).val = w := by
  have haddrVal : (AccountAddress.ofNat w.toNat).val = w.toNat := by
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  change UInt256.ofNat (AccountAddress.ofNat w.toNat).val = w
  rw [haddrVal]
  exact u256_ofNat_toNat _

theorem flapperAddressWord_address_eq_target {w : UInt256} :
    EVM.address (AccountAddress.ofNat w.toNat) = AccountAddress.ofUInt256 w := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simpa [EVM.twoPow, AccountAddress.size] using
        (AccountAddress.ofNat w.toNat).isLt)

theorem yankMoveEncode_eq (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hsrcCanon : src.toNat < EVM.addressModulus)
    (hguyCanon : guy.toNat < EVM.addressModulus) :
    config.externalABI.encode? "move"
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
      some ((yankMoveCalldataMem src guy bid mem).readWithPadding
        yankMoveOutPtr.toNat yankMoveInSize.toNat) := by
  change config.externalABI.encode? "move"
      [.address (AccountAddress.ofNat src.toNat),
        .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
    some ((yankMoveCalldataMem src guy bid mem).readWithPadding 128 100)
  rw [yankMoveCalldataMem_read128_100 src guy bid hmem]
  have hbidLt : bid.toNat < EVM.twoPow 256 := bid.val.isLt
  have hbidWord : EVM.word bid.toNat = bid := by
    show UInt256.ofNat bid.toNat = bid
    exact u256_ofNat_toNat _
  have hsrcWord := flapperAddressWord_eq_ofNat_address hsrcCanon
  have hguyWord := flapperAddressWord_eq_ofNat_address hguyCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, moveSelector, selectorBytes, hbidLt, hbidWord,
    hsrcWord, hguyWord, word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

set_option maxHeartbeats 1000000 in
theorem RD.flapperAuctionDeleteTail
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {drop0 drop1 drop2 scratch id : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hMstore0Aw : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw)
    (hMstore32Aw : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw)
    (hKeccakAw : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw)
    (hov : R.length + 10 ≤ 1024)
    (h : RD flapperBytecode I g s0 ⟨1190⟩
      (drop0 :: drop1 :: drop2 :: scratch :: id :: ⟨360⟩ :: R)
      mem aw rdata (cA, σ) k C) :
    RDret flapperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (auctionBidSlot id) ⟨0⟩)
          (auctionLotSlot id) ⟨0⟩)
        (auctionPackedSlot id) ⟨0⟩)
      ByteArray.empty := by
  let mem1 := wordAt0Mem id mem
  let mem2 := twoWordHashMem id ⟨1⟩ mem
  let base := solcMappingSlot ⟨1⟩ id
  have rd1194 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1198 := evm_run rd1194 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd1199 := rd1198.mstore 0 mem1 aw
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by
        rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide, hMstore0Aw]
        simp))
    (by simp [mem1, wordAt0Mem])
    hMstore0Aw
    (by evm_ov)
  have rd1206pre := evm_run rd1199 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1207 := rd1206pre.mstore 0 mem2 aw
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hMstore32Aw]
        simp))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [mem1, mem2, twoWordHashMem, wordAt32Mem])
    hMstore32Aw
    (by evm_ov)
  have rd1210pre := evm_run rd1207 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (mem2.readWithPadding 0 64))) = base := by
    simpa [base, mem2] using twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd1211raw := rd1210pre.keccak256 0 base aw
    (by native_decide)
    (by
      intro s haws hstks
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide, hKeccakAw]
      simp)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by
      rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact hKeccakAw)
    (by evm_ov)
  have rd1213pre := evm_run rd1211raw with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1214raw⟩ := rd1213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1219pre := evm_run rd1214raw with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1220raw⟩ := rd1219pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1223pre := evm_run rd1220raw with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1224raw⟩ := rd1223pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd360 := rd1224raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd361 := rd360.jumpdest (by native_decide) (by evm_ov)
  have hslot2 : (⟨2⟩ : UInt256) + base = base + ⟨2⟩ := u256_add_comm _ _
  have hstop := RD.stop rd361 (by native_decide) (by evm_ov)
  rw [hslot2] at hstop
  simpa only [base, auctionBidSlot, auctionLotSlot_eq, auctionPackedSlot_eq,
    auctionBaseSlot_eq] using hstop

theorem evalExpr_yank_live_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  have hstorage :
      evalExpr? config frame evm (.storage liveRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := liveRef) (er := yankLiveEvaledRef)
      (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
      (value := .int 0)
      (hbase := by simp [frame, liveRef])
      (her := by simp [frame, yankLiveEvaledRef, evalStorageRef, evalStorageRefSteps,
        liveRef, EvalResult.bind, bind, pure])
      (hty := by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using flapperStorageLocLoad_uint256 evm ⟨7⟩)]
  change evalExpr? config frame evm (.binary .eq (.storage liveRef) (.intLit 0)) =
    .ok (.bool true)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_yank_live_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  have hstorage :
      evalExpr? config frame evm (.storage liveRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := liveRef) (er := yankLiveEvaledRef)
      (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
      (value := .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat))
      (by simp [frame, liveRef])
      (by simp [frame, yankLiveEvaledRef, evalStorageRef, evalStorageRefSteps,
        liveRef, EvalResult.bind, bind, pure])
      (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (by rfl)
      (by exact flapperStorageLocLoad_uint256 evm ⟨7⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hload (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  change evalExpr? config frame evm (.binary .eq (.storage liveRef) (.intLit 0)) =
    .ok (.bool false)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_yank_guy_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "id") "guy") (er := yankGuyEvaledRef I)
      (t := .address) (loc := addrLoc (auctionPackedSlot (yankIdWord I)))
      (value := .address (AccountAddress.ofNat
        (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
          evm.executionEnv).toNat))
      (by simp [frame, bidsF])
      (by
        simp [frame, yankGuyEvaledRef, auctionIdKey, yankLocals, yankIdValue,
          evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
          valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, addrSt])
      (by rfl)
      (by
        simpa [flapperAddressReturnWord, flapperSlotWord] using
          flapperStorageLocLoad_address_offset0 evm (auctionPackedSlot (yankIdWord I)))
  have hzero :
      evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure, EvalResult.bind, bind]
    unfold castValue? addrSt
    norm_num
    rfl
  change evalExpr? config frame evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool false)
  simp only [evalExpr?, hguy, hzero, EvalResult.bind, bind]
  rw [hload]
  simp [evalBinaryOp?]

theorem flapperAddressOfNat_ne_zero_of_word_ne_zero {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) (hne : w ≠ ⟨0⟩) :
    AccountAddress.ofNat w.toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  have hval := congrArg Fin.val haddr
  have hmod : w.toNat % AccountAddress.size = w.toNat := by
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  have hzeroNat : w.toNat = 0 := by
    simpa [AccountAddress.ofNat, Fin.ofNat, hmod] using hval
  exact hne (uint256_toNat_eq_zero hzeroNat)

theorem evalExpr_yank_guy_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  let guyWord :=
    flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
      evm.executionEnv
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat guyWord.toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "id") "guy") (er := yankGuyEvaledRef I)
      (t := .address) (loc := addrLoc (auctionPackedSlot (yankIdWord I)))
      (value := .address (AccountAddress.ofNat guyWord.toNat))
      (by simp [frame, bidsF])
      (by
        simp [frame, yankGuyEvaledRef, auctionIdKey, yankLocals, yankIdValue,
          evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
          valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, addrSt])
      (by rfl)
      (by
        simpa [guyWord, flapperAddressReturnWord, flapperSlotWord] using
          flapperStorageLocLoad_address_offset0 evm (auctionPackedSlot (yankIdWord I)))
  have hzero :
      evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure, EvalResult.bind, bind]
    unfold castValue? addrSt
    norm_num
    rfl
  have haddrNe : AccountAddress.ofNat guyWord.toNat ≠ AccountAddress.ofNat 0 := by
    exact flapperAddressOfNat_ne_zero_of_word_ne_zero
      (by
        simpa [guyWord, flapperAddressReturnWord] using
          solcAddrMask_result_canonical
            (flapperSlotWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
              evm.executionEnv))
      (by simpa [guyWord] using hload)
  have hvalNe :
      Value.address (AccountAddress.ofNat guyWord.toNat) ≠
        Value.address (AccountAddress.ofNat 0) := by
    intro hbad
    injection hbad with haddr
    exact haddrNe haddr
  have hbeq :
      (Value.address (AccountAddress.ofNat guyWord.toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false :=
    beq_eq_false_iff_ne.mpr hvalNe
  change evalExpr? config frame evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool true)
  simp only [evalExpr?, hguy, hzero, EvalResult.bind, bind]
  simp only [evalBinaryOp?]
  rw [hbeq]
  rfl

theorem evalExpr_yank_gem_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat
        (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat)) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := gemRef) (er := yankGemEvaledRef)
    (t := .address) (loc := addrLoc ⟨3⟩)
    (value := .address (AccountAddress.ofNat
      (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat))
    (by simp [frame, gemRef])
    (by simp [frame, yankGemEvaledRef, evalStorageRef, evalStorageRefSteps,
      gemRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [flapperAddressReturnWord, flapperSlotWord] using
        flapperStorageLocLoad_address_offset0 evm ⟨3⟩)

theorem evalExpr_yank_this (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm thisAddr =
      .ok (.address evm.executionEnv.codeOwner) := by
  simp [thisAddr, evalExpr?, envValue, pure]

theorem evalExpr_yank_bid_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat
        (flapperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
          evm.executionEnv).toNat)) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := yankBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (yankIdWord I)))
    (value := .int (Int.ofNat
      (flapperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, yankBidEvaledRef, auctionIdKey, yankLocals, yankIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by
      simpa [flapperSlotWord] using
        flapperStorageLocLoad_uint256 evm (auctionBidSlot (yankIdWord I)))

theorem evalExprs_yank_move_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := yankLocals I } evm
        [thisAddr, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
      .ok
        [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)] := by
  have hguy :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
          (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := { contract := contract, locals := yankLocals I }) (evm := evm)
      (slot := bidsF (.var "id") "guy") (er := yankGuyEvaledRef I)
      (t := .address) (loc := addrLoc (auctionPackedSlot (yankIdWord I)))
      (value := .address (AccountAddress.ofNat
        (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
          evm.executionEnv).toNat))
      (by simp [bidsF])
      (by
        simp [yankGuyEvaledRef, auctionIdKey, yankLocals, yankIdValue,
          evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
          valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, addrSt])
      (by rfl)
      (by
        simpa [flapperAddressReturnWord, flapperSlotWord] using
          flapperStorageLocLoad_address_offset0 evm (auctionPackedSlot (yankIdWord I)))
  simp [evalExprs?, evalExpr_yank_this, hguy, evalExpr_yank_bid_storage]
  rfl

theorem evalExpr_yank_extCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_yank_extCodeGuard_false {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem flapperExtCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap}
    {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

theorem flapperExtCodeSizeWord_zero_lookup_code_zero {σ : AccountMap}
    {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem flapperYankBodyReverts_stillLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [yankTransition, nonpayable] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := yankLocals I })
      (evm := evm)
      (guard := .binary .eq (.storage liveRef) (.intLit 0))
      (rest :=
        [.require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr)] ++
          checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_moveRet" ++
          [.delete (bidRef (.var "id"))])
      hwv
      (evalExpr_yank_live_zero_false evm I hlive)

theorem flapperYankBodyReverts_guyNotSet (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [yankTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_live_zero_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_yank_guy_ne_zero_false evm I hguy)))

theorem flapperYankBodyReverts_moveNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body .reverted := by
  have hvat := evalExpr_yank_gem_storage evm I
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap)
        (target := flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv)
        (addr := AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_yank_extCodeGuard_false hvat hnoCodeLookup
  refine ExecFuncBody.execBlockRevert ?_
  simpa [yankTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_live_zero_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse hguard))

theorem flapperYankBodyReverts_moveCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)]
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body .reverted := by
  have hvat := evalExpr_yank_gem_storage evm I
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv)
        (addr := AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_yank_move_args evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet")
        .reverted := by
    exact checkedExternalCallFailure hguard hvat hargs hcall
  have htail :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
          [.delete (bidRef (.var "id"))])
        .reverted :=
   .execBlock_append_term hchecked (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [yankTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_live_zero_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_guy_ne_zero_true evm I hguy)) <|
      htail)

theorem flapperYankBodyReturns_moveCallSuccess
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)]
        (true, evm', out) true) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body
      (.returned { contract := contract, locals := yankMoveLocals I }
        (yankDeletePostState evm' I) none) := by
  have hvat := evalExpr_yank_gem_storage evm I
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv)
        (addr := AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_yank_move_args evm I
  have hdec : config.externalABI.decode? "move" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hchecked :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet")
        (.ok { contract := contract, locals := yankMoveLocals I } evm') := by
    simpa [checkedExternalCallStmts, yankMoveLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall hdec
  have hdelete :
      ExecBlock config { contract := contract, locals := yankMoveLocals I } evm'
        [.delete (bidRef (.var "id"))]
        (.ok { contract := contract, locals := yankMoveLocals I }
          (yankDeletePostState evm' I)) := by
    exact ExecBlock.consNormal (ExecStmt.delete (deleteStorage_yankMove_bid evm' I))
      ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
          [.delete (bidRef (.var "id"))])
        (.ok { contract := contract, locals := yankMoveLocals I }
          (yankDeletePostState evm' I)) :=
   .execBlock_append hchecked hdelete
  refine ExecFuncBody.execBlockOK ?_
  simpa [yankTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_live_zero_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_guy_ne_zero_true evm I hguy)) <|
      htail)

theorem yankDecodeCalldata_legacyUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem yankDecodeCalldata_legacyUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flapperDecode_yank_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata =
    some (yankLocals I)
  simpa [config, yankLocals, yankIdValue, yankIdWord, uint256] using
    yankDecodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "id") hsz36

theorem flapperDecode_yank_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata = none
  simpa [config, uint256] using
    yankDecodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "id") hsz4 hshort

theorem flapperReachYankBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 19)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨331⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0x26e027f1⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x26 0xe0 0x27 0xf1 ⟨0x26e027f1⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 1 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowLowFirstArmPc 1))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨331⟩ 1 hfirst
    (fun j hj => flapperLowLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperYankX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨331⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨890⟩
      [yankIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flapperBytecode) (sel := sel) (entry := ⟨331⟩) (ret := ⟨360⟩)
    (decoded := ⟨353⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd328 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd329 := rd328.pop (by native_decide) (by evm_ov)
  have rd330 := rd329.calldataload (by native_decide) (by evm_ov)
  have rd333 := rd330.push2 ⟨890⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [yankIdWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd333.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperYankX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨331⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flapperBytecode) (sel := sel) (entry := ⟨331⟩) (ret := ⟨360⟩)
    (decoded := ⟨353⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flapperYankX_stillLive {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I ≠ ⟨0⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨890⟩
      [yankIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd878⟩ := h
  have rd881 := evm_run rd878 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k882, C882, rd882raw⟩ := rd881.sload (by native_decide) (by evm_ov)
  have rd882 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨894⟩
      (flapperSlotWord ⟨7⟩ σ I :: yankIdWord I :: ⟨360⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k882 C882 := by
    simpa [flapperSlotWord] using rd882raw
  have rd886 := evm_run rd882 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨964⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (flapperSlotWord ⟨7⟩ σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlive
  have rd887 := rd886.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨899⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x466c61707065722f7374696c6c2d6c697665⟩)
    (shift := ⟨112⟩)
    (word := ⟨0x466c61707065722f7374696c6c2d6c6976650000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd887
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperYankX_guyNotSet {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I = ⟨0⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨890⟩
      [yankIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := yankIdWord I
  let mem1 := wordAt0Mem id solcFreePtrMem
  let mem2 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  obtain ⟨_, _, rd878⟩ := h
  have rd881 := evm_run rd878 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k882, C882, rd882raw⟩ := rd881.sload (by native_decide) (by evm_ov)
  have rd882 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨894⟩
      (flapperSlotWord ⟨7⟩ σ I :: yankIdWord I :: ⟨360⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k882 C882 := by
    simpa [flapperSlotWord] using rd882raw
  have rd886 := evm_run rd882 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨964⟩ (by native_decide) (by evm_ov)]
  have hcondLive : UInt256.isZero (flapperSlotWord ⟨7⟩ σ I) ≠ ⟨0⟩ := by
    rw [hlive]
    decide
  have rd952 := rd886.jumpiT (by native_decide) hcondLive (by jump_dest) (by evm_ov)
  have rd957pre := evm_run rd952 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd958 := rd957pre.mstore 0 mem1 (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [mem1, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd962pre := evm_run rd958 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd963 := rd962pre.mstore 0 mem2 (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [mem1, mem2, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd966pre := evm_run rd963 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (mem2.readWithPadding 0 64))) = base := by
    simpa [base, mem2, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ (yankIdWord I) solcFreePtrMem
  have rd967 := rd966pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd970pre := evm_run rd967 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hslot2 : (⟨2⟩ : UInt256) + base = auctionPackedSlot (yankIdWord I) := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hslot2] at rd970pre
  obtain ⟨k971, C971, rd971raw⟩ := rd970pre.sload (by native_decide) (by evm_ov)
  have rd971 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      (flapperSlotWord (auctionPackedSlot (yankIdWord I)) σ I ::
        yankIdWord I :: ⟨360⟩ :: [sel])
      mem2 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k971 C971 := by
    simpa [flapperSlotWord] using rd971raw
  have rd980 := evm_run rd971 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨1062⟩ (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flapperSlotWord (auctionPackedSlot (yankIdWord I)) σ I) =
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  rw [hmask, hguy] at rd980
  have rd984 := rd980.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨996⟩)
    (len := ⟨19⟩)
    (rawWord := ⟨0x119b185c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩)
    (shift := ⟨106⟩)
    (word := ⟨0x466c61707065722f6775792d6e6f742d73657400000000000000000000000000⟩)
    (op := .PUSH19)
    (width := 19)
    rd984
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (twoWordHashMem_size_96 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size
      solcFreePtrMem_read64)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperYankX_readyToMove {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I ≠ ⟨0⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨890⟩
      [yankIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1062⟩
      [yankIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := yankIdWord I
  let mem1 := wordAt0Mem id solcFreePtrMem
  let mem2 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  obtain ⟨_, _, rd878⟩ := h
  have rd881 := evm_run rd878 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k882, C882, rd882raw⟩ := rd881.sload (by native_decide) (by evm_ov)
  have rd882 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨894⟩
      (flapperSlotWord ⟨7⟩ σ I :: yankIdWord I :: ⟨360⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k882 C882 := by
    simpa [flapperSlotWord] using rd882raw
  have rd886 := evm_run rd882 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨964⟩ (by native_decide) (by evm_ov)]
  have hcondLive : UInt256.isZero (flapperSlotWord ⟨7⟩ σ I) ≠ ⟨0⟩ := by
    rw [hlive]
    decide
  have rd952 := rd886.jumpiT (by native_decide) hcondLive (by jump_dest) (by evm_ov)
  have rd957pre := evm_run rd952 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd958 := rd957pre.mstore 0 mem1 (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [mem1, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd962pre := evm_run rd958 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd963 := rd962pre.mstore 0 mem2 (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [mem1, mem2, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd966pre := evm_run rd963 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (mem2.readWithPadding 0 64))) = base := by
    simpa [base, mem2, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ (yankIdWord I) solcFreePtrMem
  have rd967 := rd966pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd970pre := evm_run rd967 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hslot2 : (⟨2⟩ : UInt256) + base = auctionPackedSlot (yankIdWord I) := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hslot2] at rd970pre
  obtain ⟨k971, C971, rd971raw⟩ := rd970pre.sload (by native_decide) (by evm_ov)
  have rd971 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      (flapperSlotWord (auctionPackedSlot (yankIdWord I)) σ I ::
        yankIdWord I :: ⟨360⟩ :: [sel])
      mem2 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k971 C971 := by
    simpa [flapperSlotWord] using rd971raw
  have rd980 := evm_run rd971 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨1062⟩ (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flapperSlotWord (auctionPackedSlot (yankIdWord I)) σ I) =
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  rw [hmask] at rd980
  exact ⟨_, _, rd980.jumpiT (by native_decide) hguy (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperYankX_toMoveExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1050 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1062⟩
      [yankIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := yankIdWord I
    let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memMap := twoWordHashMem id ⟨1⟩ memHash
    let gem := flapperAddressReturnWord ⟨3⟩ σ I
    let src := yankThisWord I
    let guy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let bid := flapperSlotWord (auctionBidSlot id) σ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1158⟩
      (gem :: gem :: yankMoveOutSize :: yankMoveOutPtr :: yankMoveInSize ::
        yankMoveOutPtr :: yankMoveOutSize :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src guy bid memMap) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k' C' := by
  intro id memHash memMap gem src guy bid
  let base := solcMappingSlot ⟨1⟩ id
  let memKey := wordAt0Mem id memHash
  have hmemHash : memHash.size = 96 := by
    simpa [memHash, id] using
      twoWordHashMem_size_96 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hread64Hash : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memHash, id] using
      twoWordHashMem_read64 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id, memHash] using twoWordHashMem_size_96 id ⟨1⟩ hmemHash
  have hread64Map : memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id, memHash] using twoWordHashMem_read64 id ⟨1⟩ hmemHash hread64Hash
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem : (yankMoveCalldataMem src guy bid memMap).size = 228 :=
    yankMoveCalldataMem_size src guy bid hmemMap
  have hcallRead64 :
      (yankMoveCalldataMem src guy bid memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    yankMoveCalldataMem_read64 src guy bid hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankMoveCalldataMem src guy bid memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankMoveCalldataMem src guy bid memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd1065pre := evm_run rd1050 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1066, C1066, rd1066raw⟩ :=
    rd1065pre.sload (by native_decide) (by evm_ov)
  have rd1066 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1066⟩
      (flapperSlotWord ⟨3⟩ σ I :: id :: ⟨360⟩ :: [sel])
      memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1066 C1066 := by
    simpa [id, memHash, flapperSlotWord] using rd1066raw
  have rd1070pre := evm_run rd1066 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1071 := rd1070pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1075pre := evm_run rd1071 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1076 := rd1075pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, memHash, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1080pre := evm_run rd1076 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id, memHash] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memHash
  have rd1081 := rd1080pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1085pre := evm_run rd1081 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : base + ⟨2⟩ = auctionPackedSlot id := by
    simp [base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd1085pre
  obtain ⟨k1086, C1086, rd1086raw⟩ :=
    rd1085pre.sload (by native_decide) (by evm_ov)
  have rd1086 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1086⟩
      (flapperSlotWord (auctionPackedSlot id) σ I :: base :: ⟨64⟩ :: ⟨0⟩ ::
        flapperSlotWord ⟨3⟩ σ I :: id :: ⟨360⟩ :: [sel])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1086 C1086 := by
    simpa [flapperSlotWord] using rd1086raw
  have rd1087pre := rd1086.swap1 (by native_decide) (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd1087pre
  obtain ⟨k1088, C1088, rd1088raw⟩ :=
    rd1087pre.sload (by native_decide) (by evm_ov)
  have rd1088 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1088⟩
      (bid :: flapperSlotWord (auctionPackedSlot id) σ I :: ⟨64⟩ :: ⟨0⟩ ::
        flapperSlotWord ⟨3⟩ σ I :: id :: ⟨360⟩ :: [sel])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1088 C1088 := by
    simpa [bid, flapperSlotWord] using rd1088raw
  have rd1106 := evm_run rd1088 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (yankMoveSelectorMem memMap) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveSrcMem src memMap) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [yankMoveSrcMem, src, yankThisWord,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov)]
  have hpc1106 :
      (⟨1088⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ =
        ⟨1106⟩ := by
    native_decide
  rw [hpc1106] at rd1106
  have rd1122 := evm_run rd1106 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveGuyMem src guy memMap) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [yankMoveGuyMem, guy, u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov)]
  have hpc1122 :
      (⟨1106⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨1122⟩ := by
    native_decide
  rw [hpc1122] at rd1122
  have rd1130 := evm_run rd1122 with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveCalldataMem src guy bid memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hpc1130 :
      (⟨1122⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨1130⟩ := by
    native_decide
  rw [hpc1130] at rd1130
  have rd1135 := evm_run rd1130 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have hpc1135 :
      (⟨1130⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨1135⟩ := by
    native_decide
  rw [hpc1135] at rd1135
  have rd1158 := evm_run rd1135 with [
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 yankMoveInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc1158 :
      (⟨1135⟩ : UInt256) + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ =
        ⟨1158⟩ := by
    native_decide
  rw [hpc1158] at rd1158
  exact ⟨_, _, by
    simpa [gem, src, guy, bid, yankThisWord, yankMoveSelectorMem, yankMoveSrcMem,
      yankMoveGuyMem, yankMoveCalldataMem, yankMoveSelectorShifted,
      yankMoveOutPtr, yankMoveOutSize, yankMoveInSize, yankMoveEndPtr,
      flapperAddressReturnWord, flapperSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + yankMoveInSize =
        yankMoveInSize from by native_decide,
      show (⟨128⟩ : UInt256) + yankMoveInSize = yankMoveEndPtr from by native_decide,
      show yankMoveInSize + yankMoveOutPtr = yankMoveEndPtr from by native_decide]
      using rd1158⟩

theorem flapperYankX_moveNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨3⟩ σ I) = ⟨0⟩)
    (rd1050 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1062⟩
      [yankIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1148⟩ := flapperYankX_toMoveExtcodesizeGuard rd1050
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1158⟩) (okPc := ⟨1170⟩) rd1148
    hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)
theorem flapperYankX_moveCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨3⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1050 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1062⟩
      [yankIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := yankIdWord I
    let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memMap := twoWordHashMem id ⟨1⟩ memHash
    let gem := flapperAddressReturnWord ⟨3⟩ σ I
    let src := yankThisWord I
    let guy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let bid := flapperSlotWord (auctionBidSlot id) σ I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1174⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: id :: ⟨360⟩ :: sel :: [])
        (yankMoveCalldataMem src guy bid memMap) (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat gem.toNat)) "move" 0
        [.address I.codeOwner, .address (AccountAddress.ofNat guy.toNat),
          .int (Int.ofNat bid.toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro id memHash memMap gem src guy bid
  have hmemHash : memHash.size = 96 := by
    simpa [memHash, id] using
      twoWordHashMem_size_96 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hmemMap : memMap.size = 96 := by
    have hread64Hash : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memHash, id] using
        twoWordHashMem_read64 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
    simpa [memMap, id, memHash] using twoWordHashMem_size_96 id ⟨1⟩ hmemHash
  have hvatCanon : gem.toNat < EVM.addressModulus := by
    simpa [gem, flapperAddressReturnWord] using
      solcAddrMask_result_canonical (flapperSlotWord ⟨3⟩ σ I)
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [show src = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flapperAddressReturnWord] using
      solcAddrMask_result_canonical (flapperSlotWord (auctionPackedSlot id) σ I)
  have hsrcAddr : AccountAddress.ofNat src.toNat = I.codeOwner := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [src, yankThisWord] using accountAddress_roundtrip I.codeOwner
  obtain ⟨_, _, rd1148⟩ := flapperYankX_toMoveExtcodesizeGuard rd1050
  obtain ⟨gasWord, _, _, rd1163⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1158⟩) (okPc := ⟨1170⟩) rd1148
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k1164, C1164, hΘpack, rd1164raw,
      houtsz⟩ :=
    RD.call rd1163 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1164, C1164, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          yankMoveOutPtr.toNat yankMoveInSize.toNat)
          yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
      native_decide
    have hmin : (min yankMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold yankMoveOutSize
      rfl
    have rd1164 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1174⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: id :: ⟨360⟩ :: sel :: [])
        (out.write 0 (yankMoveCalldataMem src guy bid memMap) yankMoveOutPtr.toNat
          (min yankMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k1164 C1164 :=
      haw ▸ rd1164raw
    rw [hmin, byteArray_write_len_zero] at rd1164
    exact rd1164
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gem)
      (mem := yankMoveCalldataMem src guy bid memMap)
      (inOff := yankMoveOutPtr) (inSize := yankMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flapperAddressWord_address_eq_target
      ?_ ?_
    · simpa [hsrcAddr] using yankMoveEncode_eq src guy bid hmemMap hsrcCanon hguyCanon
    · simpa [initState, hperm] using hΘ

theorem flapperYankX_moveCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨3⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth = 1024)
    (rd1050 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1062⟩
      [yankIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := yankIdWord I
    let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memMap := twoWordHashMem id ⟨1⟩ memHash
    let gem := flapperAddressReturnWord ⟨3⟩ σ I
    let src := yankThisWord I
    let guy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let bid := flapperSlotWord (auctionBidSlot id) σ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1174⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src guy bid memMap) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  intro id memHash memMap gem src guy bid
  obtain ⟨_, _, rd1148⟩ := flapperYankX_toMoveExtcodesizeGuard rd1050
  obtain ⟨gasWord, _, _, rd1163⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1158⟩) (okPc := ⟨1170⟩) rd1148
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k1164, C1164, rd1164raw⟩ :=
    RD.callDepthLimit rd1163 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k1164, C1164, ?_⟩
  have hmin : (min yankMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold yankMoveOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        yankMoveOutPtr.toNat yankMoveInSize.toNat)
        yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
    native_decide
  simpa [yankMoveOutPtr, yankMoveInSize, yankMoveOutSize, hmin,
    byteArray_write_len_zero, haw] using rd1164raw

theorem flapperYankX_moveCallFailure
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd1164 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1174⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨3⟩ σ I :: yankIdWord I :: ⟨360⟩ :: sel :: [])
      mem aw out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1174⟩) (okPc := ⟨1190⟩) rd1164
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

theorem flapperYankX_moveCallSuccessDelete
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel status : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hstatus : status ≠ ⟨0⟩)
    (rd1164 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1174⟩
      (status :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨3⟩ σ I :: yankIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ' (auctionBidSlot (yankIdWord I)) ⟨0⟩)
          (auctionLotSlot (yankIdWord I)) ⟨0⟩)
        (auctionPackedSlot (yankIdWord I)) ⟨0⟩)
      ByteArray.empty := by
  have rd1175 := rd1164.iszero (by native_decide) (by evm_ov)
  have rd1176 := rd1175.dup1 (by native_decide) (by evm_ov)
  have rd1177 := rd1176.iszero (by native_decide) (by evm_ov)
  have rd1180pre := rd1177.push2 ⟨1190⟩ (by native_decide) (by evm_ov)
  have hcond : UInt256.isZero (UInt256.isZero status) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hstatus]
    decide
  have rd1190 := rd1180pre.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  exact RD.flapperAuctionDeleteTail hperm
    (by native_decide) (by native_decide) (by native_decide) (by simp) rd1190

theorem flapperYankBodyCoreStillLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I ≠ ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨331⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hlive (by
      have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
      rw [hword, hzero])
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperYankBodyReverts_stillLive evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
  exact (flapperYankX_stillLive (g := Sat256.ofUInt256 g) hlive
      (flapperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperYankBodyCoreGuyNotSet
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨331⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨0⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I = ⟨0⟩ := by
    have hword :=
      flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (yankIdWord I))
    rw [← hword]
    exact hguy
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperYankBodyReverts_guyNotSet evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
  exact (flapperYankX_guyNotSet (g := Sat256.ofUInt256 g) hlive hguy
      (flapperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperYankBodyCoreMoveNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨3⟩ σ_evm I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨331⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨0⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by
      have hword :=
        flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts
          (auctionPackedSlot (yankIdWord I))
      rw [hword, hzero])
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨3⟩ σ_solm I) = ⟨0⟩ :=
    flapperCodeSize_zero_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hnoCode
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperYankBodyReverts_moveNoCode evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hnoCodeSolm)
  obtain ⟨_, _, rd1050⟩ :=
    flapperYankX_readyToMove (g := Sat256.ofUInt256 g) hlive hguy
      (flapperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flapperYankX_moveNoCode (g := Sat256.ofUInt256 g) hnoCode rd1050)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperYankBodyCoreMoveCallFailure
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hcode : I.code = flapperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩)
    (rd1164 : RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1174⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨3⟩ σ_evm I :: yankIdWord I :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem
        (yankThisWord I)
        (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
        (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
        (twoWordHashMem (yankIdWord I) ⟨1⟩
          (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (houtSize : out.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hpostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hvatEq :
      flapperAddressReturnWord ⟨3⟩ σ_evm I =
        flapperAddressReturnWord ⟨3⟩ σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts ⟨3⟩
  have hguyEq :
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I =
        flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (yankIdWord I))
  have hbidEq :
      flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I =
        flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I :=
    flapperSlotWord_accountMapEquiv hAccounts (auctionBidSlot (yankIdWord I))
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ σ_solm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I).toNat)]
        (false, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, hvatEq, hguyEq, hbidEq] using hcallSolmRaw
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨0⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by rw [hguyEq, hzero])
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨3⟩ σ_solm I) ≠ ⟨0⟩ :=
    flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, evmCallSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperYankBodyReverts_moveCallFailure evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  exact (flapperYankX_moveCallFailure rd1164 houtSize)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperYankBodyCoreMoveCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨331⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := yankIdWord I
  let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memMap := twoWordHashMem id ⟨1⟩ memHash
  let gem := flapperAddressReturnWord ⟨3⟩ σ_solm I
  let src := yankThisWord I
  let guy := flapperAddressReturnWord (auctionPackedSlot id) σ_solm I
  let bid := flapperSlotWord (auctionBidSlot id) σ_solm I
  let A_move := (evmSolm.addAccessedAccount (EVM.address (AccountAddress.ofNat gem.toNat))).substate
  have hmemHash : memHash.size = 96 := by
    simpa [memHash, id] using
      twoWordHashMem_size_96 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id, memHash] using twoWordHashMem_size_96 id ⟨1⟩ hmemHash
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [show src = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flapperAddressReturnWord] using
      solcAddrMask_result_canonical (flapperSlotWord (auctionPackedSlot id) σ_solm I)
  have hsrcAddr : AccountAddress.ofNat src.toNat = I.codeOwner := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [src, yankThisWord] using accountAddress_roundtrip I.codeOwner
  have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
    simpa [evmSolm, initState] using hdepth
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat gem.toNat)) "move" 0
        [.address I.codeOwner, .address (AccountAddress.ofNat guy.toNat),
          .int (Int.ofNat bid.toNat)]
        (false, { evmSolm with substate := A_move }, ByteArray.empty) true := by
    simpa [A_move, hsrcAddr] using
      (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
        (tgt := EVM.address (AccountAddress.ofNat gem.toNat)) (name := "move")
        (args := [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)])
        (callPerm := true)
        (calldata := (yankMoveCalldataMem src guy bid memMap).readWithPadding
          yankMoveOutPtr.toNat yankMoveInSize.toNat)
        (yankMoveEncode_eq src guy bid hmemMap hsrcCanon hguyCanon)
        hdepthInit)
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨0⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by
      have hword :=
        flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts
          (auctionPackedSlot (yankIdWord I))
      rw [hword, hzero])
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨3⟩ σ_solm I) ≠ ⟨0⟩ :=
    flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, gem, src, guy, bid, id, flapperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flapperYankBodyReverts_moveCallFailure evmSolm
        { evmSolm with substate := A_move } I ByteArray.empty
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  obtain ⟨_, _, rd1050⟩ :=
    flapperYankX_readyToMove (g := Sat256.ofUInt256 g) hlive hguy
      (flapperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  obtain ⟨_, _, rd1164⟩ :=
    flapperYankX_moveCallDepthLimit (g := Sat256.ofUInt256 g) hcodeSize hdepth rd1050
  exact (flapperYankX_moveCallFailure rd1164 (by native_decide))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperYankBodyCoreMoveCallSuccess
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hcode : I.code = flapperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨0⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩)
    (rd1164 : RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1174⟩
      (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨3⟩ σ_evm I :: yankIdWord I :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem
        (yankThisWord I)
        (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
        (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
        (twoWordHashMem (yankIdWord I) ⟨1⟩
          (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostCallAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hvatEq :
      flapperAddressReturnWord ⟨3⟩ σ_evm I =
        flapperAddressReturnWord ⟨3⟩ σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts ⟨3⟩
  have hguyEq :
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I =
        flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (yankIdWord I))
  have hbidEq :
      flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I =
        flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I :=
    flapperSlotWord_accountMapEquiv hAccounts (auctionBidSlot (yankIdWord I))
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨3⟩ σ_solm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I).toNat)]
        (true, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, hvatEq, hguyEq, hbidEq] using hcallSolmRaw
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨0⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by rw [hguyEq, hzero])
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨3⟩ σ_solm I) ≠ ⟨0⟩ :=
    flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body
        (.returned { contract := contract, locals := yankMoveLocals I }
          (yankDeletePostState evmCallSolm I) none) := by
    simpa [evmSolm, evmCallSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperYankBodyReturns_moveCallSuccess evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  have hret :=
    flapperYankX_moveCallSuccessDelete
      (g := Sat256.ofUInt256 g) (σ := σ_evm) (sel := sel) hperm
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) rd1164
  have hRuntimeDeleteEquiv :
      accountMapEquiv (yankRuntimeDeleteAccountMap I σ')
        (yankRuntimeDeleteAccountMap I σ'_solm) := by
    unfold yankRuntimeDeleteAccountMap
    exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
      (auctionBidSlot (yankIdWord I)) ⟨0⟩
      (auctionLotSlot (yankIdWord I)) ⟨0⟩
      (auctionPackedSlot (yankIdWord I)) ⟨0⟩
      hpostCallAccounts
  have hDeleteSolm :
      accountMapEquiv (yankRuntimeDeleteAccountMap I σ'_solm)
        (yankDeletePostState evmCallSolm I).accountMap := by
    simpa [evmCallSolm] using
      yankDeletePostState_accountMapEquiv evmCallSolm I
        (by simp [evmCallSolm, evmSolm, initState])
  have hFinalAccounts :
      accountMapEquiv (yankRuntimeDeleteAccountMap I σ')
        (yankDeletePostState evmCallSolm I).accountMap :=
    accountMapEquiv.trans hRuntimeDeleteEquiv hDeleteSolm
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp [yankDeletePostState, yankDeleteAfterTic, yankDeleteAfterGuy,
        yankDeleteAfterLot, yankDeleteAfterBid, evmCallSolm, evmSolm, initState,
        storageStore_createdAccounts])
    (by simpa [yankRuntimeDeleteAccountMap] using hFinalAccounts)
    (by
      simpa [yankTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flapperYankBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨331⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperYankX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flapperDecode_yank_none_short hsz4 hshort)

theorem flapperYankBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 19))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 19) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some yankTransition :=
    flapperDispatchYank hsel
  have hreach := flapperReachYankBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := flapperDecode_yank_ok (I := I) hsz36
    by_cases hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨0⟩
    · by_cases hguy :
          flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I = ⟨0⟩
      · exact flapperYankBodyCoreGuyNotSet hcode hsize hwv hsz36 hlive hguy
          hdispatch hdecode hreach hAccounts
      · by_cases hcodeSize :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (flapperAddressReturnWord ⟨3⟩ σ_evm I) = ⟨0⟩
        · exact flapperYankBodyCoreMoveNoCode hcode hsize hwv hsz36 hlive hguy
            hcodeSize hdispatch hdecode hreach hAccounts
        · by_cases hdepthEq : I.depth = 1024
          · exact flapperYankBodyCoreMoveCallDepthLimit hcode hsize hwv hsz36 hlive
              hguy hcodeSize hdepthEq hdispatch hdecode hreach hAccounts
          · have hdepthLt : I.depth.val < 1024 := by
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              by_contra hn
              have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
              have hval : I.depth.val = 1024 := by omega
              apply hdepthEq
              apply Fin.ext
              exact hval
            obtain ⟨_, _, rd1050⟩ :=
              flapperYankX_readyToMove (g := Sat256.ofUInt256 g) hlive hguy
                (flapperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
            obtain ⟨cA', σ', z, out, A', k1164, C1164, rd1164, hcall, houtSize⟩ :=
              flapperYankX_moveCall (g := Sat256.ofUInt256 g) hperm hcodeSize
                hdepthLt rd1050
            by_cases hz : z = true
            · have rd1164True : RD flapperBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1174⟩
                  (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                    flapperAddressReturnWord ⟨3⟩ σ_evm I ::
                    yankIdWord I :: ⟨360⟩ :: flapperSelWord I :: [])
                  (yankMoveCalldataMem
                    (yankThisWord I)
                    (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
                    (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
                    (twoWordHashMem (yankIdWord I) ⟨1⟩
                      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
                  (UInt256.ofNat 8) out (cA', σ') k1164 C1164 := by
                simpa [hz] using rd1164
              have hcallTrue :
                  typedCallViaEVM config
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat
                      (flapperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
                    "move" 0
                    [.address I.codeOwner,
                    .address (AccountAddress.ofNat
                      (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I))
                        σ_evm I).toNat),
                    .int (Int.ofNat
                      (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
                    (true,
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ', substate := A', createdAccounts := cA' },
                      out) true := by
                simpa [hz] using hcall
              exact flapperYankBodyCoreMoveCallSuccess hcode hsize hperm hwv hsz36
                hlive hguy hcodeSize rd1164True hcallTrue hdispatch hdecode hAccounts
            · have hzFalse : z = false := Bool.eq_false_iff.mpr hz
              have rd1164False : RD flapperBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1174⟩
                  (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                    flapperAddressReturnWord ⟨3⟩ σ_evm I ::
                    yankIdWord I :: ⟨360⟩ :: flapperSelWord I :: [])
                  (yankMoveCalldataMem
                    (yankThisWord I)
                    (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
                    (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
                    (twoWordHashMem (yankIdWord I) ⟨1⟩
                      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
                  (UInt256.ofNat 8) out (cA', σ') k1164 C1164 := by
                simpa [hzFalse] using rd1164
              have hcallFalse :
                  typedCallViaEVM config
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat
                      (flapperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
                    "move" 0
                    [.address I.codeOwner,
                    .address (AccountAddress.ofNat
                      (flapperAddressReturnWord (auctionPackedSlot (yankIdWord I))
                        σ_evm I).toNat),
                    .int (Int.ofNat
                      (flapperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
                    (false,
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ', substate := A', createdAccounts := cA' },
                      out) true := by
                simpa [hzFalse] using hcall
              exact flapperYankBodyCoreMoveCallFailure hcode hsize hwv hsz36 hlive
                hguy hcodeSize rd1164False hcallFalse houtSize hdispatch hdecode hAccounts
    · exact flapperYankBodyCoreStillLive hcode hsize hwv hsz36 hlive
        hdispatch hdecode hreach hAccounts
  · exact flapperYankBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flapper
