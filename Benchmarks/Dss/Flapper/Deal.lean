import Benchmarks.Dss.Flapper.Yank

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

/-! ## `deal(uint256)` -/

abbrev dealIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev dealIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (dealIdWord I).toNat)

abbrev dealLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (dealIdValue I)

abbrev dealLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev dealVatEvaledRef : EvaledStorageRef :=
  { base := "vat", steps := [] }

abbrev dealGemEvaledRef : EvaledStorageRef :=
  { base := "gem", steps := [] }

abbrev dealFillEvaledRef : EvaledStorageRef :=
  { base := "fill", steps := [] }

abbrev dealBidEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "bid"] }

abbrev dealLotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "lot"] }

abbrev dealGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "guy"] }

abbrev dealTicEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "tic"] }

abbrev dealEndEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "end"] }

abbrev dealTicWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) evm.accountMap
    evm.executionEnv

abbrev dealEndWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) evm.accountMap
    evm.executionEnv

abbrev dealGuyWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) evm.accountMap
    evm.executionEnv

abbrev dealBidWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperSlotWord (auctionBidSlot (dealIdWord I)) evm.accountMap evm.executionEnv

abbrev dealLotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperSlotWord (auctionLotSlot (dealIdWord I)) evm.accountMap evm.executionEnv

abbrev dealVatWord (evm : EVM.State) : UInt256 :=
  flapperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv

abbrev dealGemWord (evm : EVM.State) : UInt256 :=
  flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv

abbrev dealFillWord (evm : EVM.State) : UInt256 :=
  flapperSlotWord ⟨9⟩ evm.accountMap evm.executionEnv

abbrev dealTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

def auctionRuntimeDeleteAccountMap (owner : AccountAddress) (id : UInt256)
    (σ : AccountMap) : AccountMap :=
  sstoreAccountMap owner
    (sstoreAccountMap owner
      (sstoreAccountMap owner σ (auctionBidSlot id) ⟨0⟩)
      (auctionLotSlot id) ⟨0⟩)
    (auctionPackedSlot id) ⟨0⟩

theorem evalStorageRef_auction_bid (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm
        (bidRef (.var "id")) =
      .ok { base := "bids", steps := [.mindex (auctionIdKey id)] } := by
  have hgetElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [bidRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hgetElem,
    auctionIdKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem evalStorageRef_auction_field (evm : EVM.State) (locals : Store) (id : UInt256)
    (field : Ident)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm
        (bidsF (.var "id") field) =
      .ok { base := "bids", steps := [.mindex (auctionIdKey id), .field field] } := by
  have hgetElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [bidsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hgetElem,
    auctionIdKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem resolveStorageRef_auction_bid (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbase : locals.get? "bids" = none) :
    resolveStorageRef? config { contract := contract, locals := locals } evm (bidRef (.var "id")) =
      .ok ({ base := "bids", steps := [.mindex (auctionIdKey id)] }, BidStructTy) := by
  rw [resolveStorageRef?]
  simp only [bidRef]
  rw [hbase]
  rw [show evalStorageRef config { contract := contract, locals := locals } evm
      { base := "bids", steps := [StorageRefStep.mindex (.var "id")] } =
        .ok { base := "bids", steps := [.mindex (auctionIdKey id)] } by
    simpa [bidRef] using evalStorageRef_auction_bid evm locals id hget]
  simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, BidStructTy,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

def auctionDeleteAfterBid (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionBidSlot id) ⟨0⟩

def auctionDeleteAfterLot (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterBid id evm)
    (auctionDeleteAfterBid id evm).executionEnv.codeOwner (auctionLotSlot id) ⟨0⟩

def auctionDeleteAfterGuy (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterLot id evm)
    (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
        (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id))
      ⟨0⟩)

def auctionDeleteAfterTic (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterGuy id evm)
    (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)
    (clearUint48Offset20Word
      (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
        (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)))

def auctionDeletePostState (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterTic id evm)
    (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id)
    (clearUint48Offset26Word
      (Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
        (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id)))

theorem deleteStorage_auction_bid (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbase : locals.get? "bids" = none) :
    deleteStorage? config { contract := contract, locals := locals } evm
      (bidRef (.var "id")) = .ok (auctionDeletePostState id evm) := by
  rw [deleteStorage?]
  rw [resolveStorageRef_auction_bid evm locals id hget hbase]
  simp only [EvalResult.bind, bind]
  rw [Solm.clearStorage?.eq_def]
  simp only [BidStructTy]
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint256_zero (slot := auctionBidSlot id) (hloc := auctionBidLayout evm id)]
  change clearFields? config (auctionDeleteAfterBid id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("lot", uint256St), ("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint256_zero (slot := auctionLotSlot id)
    (hloc := auctionLotLayout (auctionDeleteAfterBid id evm) id)]
  change clearFields? config (auctionDeleteAfterLot id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_addr_zero (slot := auctionPackedSlot id)
    (hloc := auctionGuyLayout (auctionDeleteAfterLot id evm) id)]
  change clearFields? config (auctionDeleteAfterGuy id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint48_offset20_zero (slot := auctionPackedSlot id)
    (hloc := auctionTicLayout (auctionDeleteAfterGuy id evm) id)]
  change clearFields? config (auctionDeleteAfterTic id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint48_offset26_zero (slot := auctionPackedSlot id)
    (hloc := auctionEndLayout (auctionDeleteAfterTic id evm) id)]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp [auctionDeletePostState]

theorem auctionDeletePackedFinalWord_zero (id : UInt256) (evm : EVM.State) :
    clearUint48Offset26Word
        (Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
          (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id)) =
      ⟨0⟩ := by
  by_cases hacc0 : evm.accountMap.find? evm.executionEnv.codeOwner = none
  · have hbid : auctionDeleteAfterBid id evm = evm := by
      exact storageStore_absent evm evm.executionEnv.codeOwner hacc0 (auctionBidSlot id) ⟨0⟩
    have hlot : auctionDeleteAfterLot id evm = evm := by
      simp [auctionDeleteAfterLot, hbid,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0 (auctionLotSlot id) ⟨0⟩]
    have hguy : auctionDeleteAfterGuy id evm = evm := by
      simp [auctionDeleteAfterGuy, hlot,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0
          (auctionPackedSlot id)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot id)) ⟨0⟩)]
    have htic : auctionDeleteAfterTic id evm = evm := by
      simp [auctionDeleteAfterTic, hguy,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0
          (auctionPackedSlot id)
          (clearUint48Offset20Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot id)))]
    have hload :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot id) = ⟨0⟩ := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hacc0, Option.option]
    rw [htic, hload]
    exact clearUint48Offset26Word_zero
  · obtain ⟨_, hacc0some⟩ := Option.ne_none_iff_exists'.mp hacc0
    have haccLotExists :
        ∃ acc, (auctionDeleteAfterLot id evm).accountMap.find?
          (auctionDeleteAfterLot id evm).executionEnv.codeOwner = some acc := by
      simp [auctionDeleteAfterLot, auctionDeleteAfterBid, Solm.EVM.storageStore,
        State.lookupAccount, hacc0some, Option.option, State.setAccount,
        accountMap_find_insert_self]
    obtain ⟨_, haccLot⟩ := haccLotExists
    have hloadGuy :
        Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
            (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
              (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id))
            ⟨0⟩ := by
      rw [show (auctionDeleteAfterGuy id evm).executionEnv =
          (auctionDeleteAfterLot id evm).executionEnv by
        simp [auctionDeleteAfterGuy, storageStore_executionEnv]]
      exact storageLoad_storageStore_same_present (auctionDeleteAfterLot id evm)
        (auctionDeleteAfterLot id evm).executionEnv.codeOwner haccLot
        (auctionPackedSlot id)
        (setAddressOffset0Word
          (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
            (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id)) ⟨0⟩)
    have haccGuyExists :
        ∃ acc, (auctionDeleteAfterGuy id evm).accountMap.find?
          (auctionDeleteAfterGuy id evm).executionEnv.codeOwner = some acc := by
      simp [auctionDeleteAfterGuy, haccLot, Solm.EVM.storageStore, State.lookupAccount,
        Option.option, State.setAccount, accountMap_find_insert_self]
    obtain ⟨_, haccGuy⟩ := haccGuyExists
    have hloadTic :
        Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
            (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id) =
          clearUint48Offset20Word
            (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
              (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)) := by
      rw [show (auctionDeleteAfterTic id evm).executionEnv =
          (auctionDeleteAfterGuy id evm).executionEnv by
        simp [auctionDeleteAfterTic, storageStore_executionEnv]]
      exact storageLoad_storageStore_same_present (auctionDeleteAfterGuy id evm)
        (auctionDeleteAfterGuy id evm).executionEnv.codeOwner haccGuy
        (auctionPackedSlot id)
        (clearUint48Offset20Word
          (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
            (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)))
    rw [hloadTic, hloadGuy]
    exact clearUint48Offset26_after_offset20_after_address_zero _

set_option maxHeartbeats 1000000 in
theorem auctionDeletePostState_accountMapEquiv (id : UInt256) (evm : EVM.State)
    (owner : AccountAddress) (howner : evm.executionEnv.codeOwner = owner) :
    accountMapEquiv (auctionRuntimeDeleteAccountMap owner id evm.accountMap)
      (auctionDeletePostState id evm).accountMap := by
  let srcOwner := evm.executionEnv.codeOwner
  let bidSlot := auctionBidSlot id
  let lotSlot := auctionLotSlot id
  let packedSlot := auctionPackedSlot id
  let m2 :=
    sstoreAccountMap srcOwner (sstoreAccountMap srcOwner evm.accountMap bidSlot ⟨0⟩)
      lotSlot ⟨0⟩
  let vGuy :=
    setAddressOffset0Word
      (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
        (auctionDeleteAfterLot id evm).executionEnv.codeOwner packedSlot) ⟨0⟩
  let vTic :=
    clearUint48Offset20Word
      (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
        (auctionDeleteAfterGuy id evm).executionEnv.codeOwner packedSlot)
  let vEnd :=
    clearUint48Offset26Word
      (Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
        (auctionDeleteAfterTic id evm).executionEnv.codeOwner packedSlot)
  have hfinal : vEnd = ⟨0⟩ := by
    simpa [vEnd, packedSlot] using auctionDeletePackedFinalWord_zero id evm
  have h1 :
      accountMapEquiv (sstoreAccountMap srcOwner m2 packedSlot vEnd)
        (sstoreAccountMap srcOwner (sstoreAccountMap srcOwner m2 packedSlot vGuy)
          packedSlot vEnd) :=
    accountMapEquiv_sstoreAccountMap_self_update m2 srcOwner packedSlot vGuy vEnd
  have h2 :
      accountMapEquiv
        (sstoreAccountMap srcOwner (sstoreAccountMap srcOwner m2 packedSlot vGuy)
          packedSlot vEnd)
        (sstoreAccountMap srcOwner
          (sstoreAccountMap srcOwner
            (sstoreAccountMap srcOwner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd) :=
    accountMapEquiv_sstoreAccountMap_self_update
      (sstoreAccountMap srcOwner m2 packedSlot vGuy) srcOwner packedSlot vTic vEnd
  have h := accountMapEquiv.trans h1 h2
  have hleftEq :
      sstoreAccountMap srcOwner m2 packedSlot vEnd =
        sstoreAccountMap srcOwner m2 packedSlot ⟨0⟩ := by
    rw [hfinal]
  have h' :
      accountMapEquiv (sstoreAccountMap srcOwner m2 packedSlot ⟨0⟩)
        (sstoreAccountMap srcOwner
          (sstoreAccountMap srcOwner
            (sstoreAccountMap srcOwner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd) := by
    simpa [hleftEq] using h
  simpa [auctionRuntimeDeleteAccountMap, auctionDeletePostState, auctionDeleteAfterTic,
    auctionDeleteAfterGuy, auctionDeleteAfterLot, auctionDeleteAfterBid, m2, srcOwner, bidSlot,
    lotSlot, packedSlot, vGuy, vTic, vEnd, howner, storageStore_accountMap,
    storageStore_executionEnv] using h'

abbrev dealBurnSelectorWord : UInt256 :=
  ⟨0x9dc29fac⟩

abbrev dealBurnSelectorShifted : UInt256 :=
  UInt256.shiftLeft dealBurnSelectorWord ⟨224⟩

abbrev dealBurnOutPtr : UInt256 := ⟨128⟩

abbrev dealBurnInSize : UInt256 := ⟨68⟩

abbrev dealBurnOutSize : UInt256 := ⟨0⟩

abbrev dealBurnEndPtr : UInt256 := ⟨196⟩

noncomputable def dealBurnSelectorMem (mem : ByteArray) : ByteArray :=
  dealBurnSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def dealBurnSrcMem (src : UInt256) (mem : ByteArray) : ByteArray :=
  src.toByteArray.write 0 (dealBurnSelectorMem mem) 132 32

noncomputable def dealBurnCalldataMem (src bid : UInt256) (mem : ByteArray) : ByteArray :=
  bid.toByteArray.write 0 (dealBurnSrcMem src mem) 164 32

theorem dealBurnSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (dealBurnSelectorMem mem).size = 160 := by
  unfold dealBurnSelectorMem
  exact toByteArray_write32_size_of_ge mem dealBurnSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem dealBurnSrcMem_size (src : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (dealBurnSrcMem src mem).size = 164 := by
  unfold dealBurnSrcMem
  exact toByteArray_write32_size_of_le (dealBurnSelectorMem mem) src 132 160 164
    (dealBurnSelectorMem_size hmem)
    (by rw [dealBurnSelectorMem_size hmem]; omega) (by omega)

theorem dealBurnCalldataMem_size (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealBurnCalldataMem src bid mem).size = 196 := by
  unfold dealBurnCalldataMem
  exact toByteArray_write32_size_of_le (dealBurnSrcMem src mem) bid 164 164 196
    (dealBurnSrcMem_size src hmem)
    (by rw [dealBurnSrcMem_size src hmem]) (by omega)

theorem dealBurnSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealBurnSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealBurnSelectorMem
  rw [toByteArray_write_read_below_of_gap dealBurnSelectorShifted mem 128 64
    (by omega) (by native_decide) (by rw [hmem]; native_decide),
    hread64]

theorem dealBurnSrcMem_read64 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealBurnSrcMem src mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealBurnSrcMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [dealBurnSelectorMem_size hmem]; omega) (by omega),
    dealBurnSelectorMem_read64 hmem hread64]

theorem dealBurnCalldataMem_read64 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealBurnCalldataMem src bid mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold dealBurnCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [dealBurnSrcMem_size src hmem]) (by omega),
    dealBurnSrcMem_read64 src hmem hread64]

theorem dealBurnCalldataMem_read128_4 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealBurnCalldataMem src bid mem).readWithPadding 128 4 = burnSelector := by
  have hSrcSize := dealBurnSrcMem_size src hmem
  have hSelectorSize := dealBurnSelectorMem_size hmem
  unfold dealBurnCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (dealBurnSrcMem src mem) 164 128 4
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold dealBurnSrcMem
  rw [toByteArray_write_read_below_len_of_gap src (dealBurnSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold dealBurnSelectorMem
  rw [toByteArray_write_read_window_of_gap dealBurnSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem dealBurnCalldataMem_read132_32 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealBurnCalldataMem src bid mem).readWithPadding 132 32 = src.toByteArray := by
  have hSrcSize := dealBurnSrcMem_size src hmem
  have hSelectorSize := dealBurnSelectorMem_size hmem
  unfold dealBurnCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (dealBurnSrcMem src mem) 164 132 32
      (by rw [hSrcSize]) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold dealBurnSrcMem
  rw [toByteArray_write_read_back_of_gap src (dealBurnSelectorMem mem) 132
    (by rw [hSelectorSize]; native_decide)]

theorem dealBurnCalldataMem_read164_32 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealBurnCalldataMem src bid mem).readWithPadding 164 32 = bid.toByteArray := by
  have hSrcSize := dealBurnSrcMem_size src hmem
  unfold dealBurnCalldataMem
  rw [toByteArray_write_read_back_of_gap bid (dealBurnSrcMem src mem) 164
    (by rw [hSrcSize]; native_decide)]

theorem dealBurnCalldataMem_read128_68 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealBurnCalldataMem src bid mem).readWithPadding 128 68 =
      burnSelector ++ src.toByteArray ++ bid.toByteArray := by
  have hsize : (dealBurnCalldataMem src bid mem).size = 196 :=
    dealBurnCalldataMem_size src bid hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (dealBurnCalldataMem src bid mem) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (dealBurnCalldataMem src bid mem) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [dealBurnCalldataMem_read128_4 src bid hmem,
    dealBurnCalldataMem_read132_32 src bid hmem,
    dealBurnCalldataMem_read164_32 src bid hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem deal_wordAt0Mem_size_of_ge32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem deal_wordAt32Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem deal_twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [deal_wordAt32Mem_size_of_ge64 slot (by
    rw [deal_wordAt0Mem_size_of_ge32 key (by omega)]
    exact hmem)]
  exact deal_wordAt0Mem_size_of_ge32 key (by omega)

theorem deal_twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [deal_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)
      (by
        rw [deal_wordAt0Mem_size_of_ge32 key (by omega)]
        exact hmem)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by omega)]
  exact hread64

theorem dealBurnSelectorMem_size_228 {mem : ByteArray} (hmem : mem.size = 228) :
    (dealBurnSelectorMem mem).size = 228 := by
  unfold dealBurnSelectorMem
  exact toByteArray_write32_size_of_le mem dealBurnSelectorShifted 128 228 228 hmem
    (by rw [hmem]; omega) (by native_decide)

theorem dealBurnSrcMem_size_228 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (dealBurnSrcMem src mem).size = 228 := by
  unfold dealBurnSrcMem
  exact toByteArray_write32_size_of_le (dealBurnSelectorMem mem) src 132 228 228
    (dealBurnSelectorMem_size_228 hmem)
    (by rw [dealBurnSelectorMem_size_228 hmem]; omega) (by native_decide)

theorem dealBurnCalldataMem_size_228 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (dealBurnCalldataMem src bid mem).size = 228 := by
  unfold dealBurnCalldataMem
  exact toByteArray_write32_size_of_le (dealBurnSrcMem src mem) bid 164 228 228
    (dealBurnSrcMem_size_228 src hmem)
    (by rw [dealBurnSrcMem_size_228 src hmem]; omega) (by native_decide)

theorem dealBurnSelectorMem_read64_228 {mem : ByteArray} (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealBurnSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealBurnSelectorMem
  rw [toByteArray_write_read_below_of_gap dealBurnSelectorShifted mem 128 64
    (by omega) (by native_decide) (by rw [hmem]; native_decide),
    hread64]

theorem dealBurnSrcMem_read64_228 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealBurnSrcMem src mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealBurnSrcMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [dealBurnSelectorMem_size_228 hmem]; omega) (by omega),
    dealBurnSelectorMem_read64_228 hmem hread64]

theorem dealBurnCalldataMem_read64_228 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealBurnCalldataMem src bid mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold dealBurnCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [dealBurnSrcMem_size_228 src hmem]; omega) (by omega),
    dealBurnSrcMem_read64_228 src hmem hread64]

theorem dealBurnCalldataMem_read128_4_228 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (dealBurnCalldataMem src bid mem).readWithPadding 128 4 = burnSelector := by
  have hSrcSize := dealBurnSrcMem_size_228 src hmem
  have hSelectorSize := dealBurnSelectorMem_size_228 hmem
  unfold dealBurnCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (dealBurnSrcMem src mem) 164 128 4
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold dealBurnSrcMem
  rw [toByteArray_write_read_below_len_of_gap src (dealBurnSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold dealBurnSelectorMem
  rw [toByteArray_write_read_window_of_gap dealBurnSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem dealBurnCalldataMem_read132_32_228 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (dealBurnCalldataMem src bid mem).readWithPadding 132 32 = src.toByteArray := by
  have hSrcSize := dealBurnSrcMem_size_228 src hmem
  have hSelectorSize := dealBurnSelectorMem_size_228 hmem
  unfold dealBurnCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (dealBurnSrcMem src mem) 164 132 32
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold dealBurnSrcMem
  rw [toByteArray_write_read_back_of_gap src (dealBurnSelectorMem mem) 132
    (by rw [hSelectorSize]; native_decide)]

theorem dealBurnCalldataMem_read164_32_228 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (dealBurnCalldataMem src bid mem).readWithPadding 164 32 = bid.toByteArray := by
  have hSrcSize := dealBurnSrcMem_size_228 src hmem
  unfold dealBurnCalldataMem
  rw [toByteArray_write_read_back_of_gap bid (dealBurnSrcMem src mem) 164
    (by rw [hSrcSize]; native_decide)]

theorem dealBurnCalldataMem_read128_68_228 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (dealBurnCalldataMem src bid mem).readWithPadding 128 68 =
      burnSelector ++ src.toByteArray ++ bid.toByteArray := by
  have hsize : (dealBurnCalldataMem src bid mem).size = 228 :=
    dealBurnCalldataMem_size_228 src bid hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (dealBurnCalldataMem src bid mem) 128 4 64
      (by native_decide) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (dealBurnCalldataMem src bid mem) 132 32 32
      (by native_decide) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [dealBurnCalldataMem_read128_4_228 src bid hmem,
    dealBurnCalldataMem_read132_32_228 src bid hmem,
    dealBurnCalldataMem_read164_32_228 src bid hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem dealBurnEncode_eq_228 (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hsrcCanon : src.toNat < EVM.addressModulus) :
    config.externalABI.encode? "burn"
        [.address (AccountAddress.ofNat src.toNat), .int (Int.ofNat bid.toNat)] =
      some ((dealBurnCalldataMem src bid mem).readWithPadding
        dealBurnOutPtr.toNat dealBurnInSize.toNat) := by
  change config.externalABI.encode? "burn"
      [.address (AccountAddress.ofNat src.toNat), .int (Int.ofNat bid.toNat)] =
    some ((dealBurnCalldataMem src bid mem).readWithPadding 128 68)
  rw [dealBurnCalldataMem_read128_68_228 src bid hmem]
  have hbidLt : bid.toNat < EVM.twoPow 256 := bid.val.isLt
  have hbidWord : EVM.word bid.toNat = bid := by
    show UInt256.ofNat bid.toNat = bid
    exact u256_ofNat_toNat _
  have hsrcWord := flapperAddressWord_eq_ofNat_address hsrcCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, burnSelector, selectorBytes, hbidLt, hbidWord,
    hsrcWord, word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem dealBurnEncode_eq (src bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hsrcCanon : src.toNat < EVM.addressModulus) :
    config.externalABI.encode? "burn"
        [.address (AccountAddress.ofNat src.toNat), .int (Int.ofNat bid.toNat)] =
      some ((dealBurnCalldataMem src bid mem).readWithPadding
        dealBurnOutPtr.toNat dealBurnInSize.toNat) := by
  change config.externalABI.encode? "burn"
      [.address (AccountAddress.ofNat src.toNat), .int (Int.ofNat bid.toNat)] =
    some ((dealBurnCalldataMem src bid mem).readWithPadding 128 68)
  rw [dealBurnCalldataMem_read128_68 src bid hmem]
  have hbidLt : bid.toNat < EVM.twoPow 256 := bid.val.isLt
  have hbidWord : EVM.word bid.toNat = bid := by
    show UInt256.ofNat bid.toNat = bid
    exact u256_ofNat_toNat _
  have hsrcWord := flapperAddressWord_eq_ofNat_address hsrcCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, burnSelector, selectorBytes, hbidLt, hbidWord,
    hsrcWord, word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

abbrev dealLotLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dealLocals I).insert "lot" (.int (Int.ofNat (dealLotWord evm I).toNat))

abbrev dealMoveLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dealLotLocals evm I).insert "_moveRet" (collapseReturns [])

abbrev dealBurnLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dealMoveLocals evm I).insert "_burnRet" (collapseReturns [])

abbrev dealFillNewLocals (evm0 evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dealBurnLocals evm0 I).insert "fillNew"
    (.int (Int.ofNat (UInt256.sub (dealFillWord evm) (dealLotWord evm0 I)).toNat))

abbrev dealUintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev dealUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (dealUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

theorem dealLotLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (dealLotLocals evm I).get? "id" = some (dealIdValue I) := by
  rw [dealLotLocals, store_get_ne _ _ (by decide)]
  simp [dealLocals]

theorem dealLotLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (dealLotLocals evm I).get? "lot" =
      some (.int (Int.ofNat (dealLotWord evm I).toNat)) := by
  rw [dealLotLocals, store_get_self]

theorem dealMoveLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (dealMoveLocals evm I).get? "id" = some (dealIdValue I) := by
  rw [dealMoveLocals, store_get_ne _ _ (by decide), dealLotLocals_get_id]

theorem dealMoveLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (dealMoveLocals evm I).get? "lot" =
      some (.int (Int.ofNat (dealLotWord evm I).toNat)) := by
  rw [dealMoveLocals, store_get_ne _ _ (by decide), dealLotLocals_get_lot]

theorem dealBurnLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (dealBurnLocals evm I).get? "id" = some (dealIdValue I) := by
  rw [dealBurnLocals, store_get_ne _ _ (by decide), dealMoveLocals_get_id]

theorem dealBurnLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (dealBurnLocals evm I).get? "lot" =
      some (.int (Int.ofNat (dealLotWord evm I).toNat)) := by
  rw [dealBurnLocals, store_get_ne _ _ (by decide), dealMoveLocals_get_lot]

theorem dealBurnLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (dealBurnLocals evm I).get? "bids" = none := by
  rw [dealBurnLocals, store_get_ne _ _ (by decide)]
  rw [dealMoveLocals, store_get_ne _ _ (by decide)]
  rw [dealLotLocals, store_get_ne _ _ (by decide)]
  rw [dealLocals, store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem dealFillNewLocals_get_fillNew (evm0 evm : EVM.State) (I : ExecutionEnv) :
    (dealFillNewLocals evm0 evm I).get? "fillNew" =
      some (.int (Int.ofNat (UInt256.sub (dealFillWord evm) (dealLotWord evm0 I)).toNat)) := by
  rw [dealFillNewLocals, store_get_self]

theorem dealUintBinaryLocals_get_x (x y : UInt256) :
    (dealUintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [dealUintBinaryLocals, store_get_self]

theorem dealUintBinaryLocals_get_y (x y : UInt256) :
    (dealUintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [dealUintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem dealUintBinaryLocalsZ_get_x (x y z : UInt256) :
    (dealUintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [dealUintBinaryLocalsZ, store_get_ne _ _ (by decide), dealUintBinaryLocals_get_x]

theorem dealUintBinaryLocalsZ_get_z (x y z : UInt256) :
    (dealUintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [dealUintBinaryLocalsZ, store_get_self]

theorem dealEvalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem dealEvalExpr_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem dealEvalExpr_sub256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) = .revert := by
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro hle
  exact False.elim (not_le.mpr hlt hle)

theorem dealEvalExpr_le_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hle

theorem dealSubFunctionReturn (evm : EVM.State) {x y diff : UInt256}
    (hdiff : diff = UInt256.sub x y) (hle : y.toNat ≤ x.toNat) :
    ExecFuncBody config { contract := contract, locals := dealUintBinaryLocals x y } evm
      subFunction.body
      (.returned { contract := contract, locals := dealUintBinaryLocalsZ x y diff } evm
        (some [.int (Int.ofNat diff.toNat)])) := by
  let locals := dealUintBinaryLocals x y
  let localsZ := dealUintBinaryLocalsZ x y diff
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using dealEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (dealUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using dealEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (dealUintBinaryLocals_get_y x y)
  have hSub :
      evalExpr? config { contract := contract, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat diff.toNat)) :=
    dealEvalExpr_sub256_ok hx hy hdiff hle
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simpa [localsZ] using dealEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := diff)
      (dealUintBinaryLocalsZ_get_z x y diff)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using dealEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (dealUintBinaryLocalsZ_get_x x y diff)
  have hdiffNat : diff.toNat = x.toNat - y.toNat := by
    rw [hdiff, usub_toNat hle]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "z") (.var "x")) = .ok (.bool true) :=
    dealEvalExpr_le_uint256_true hz hxZ (by rw [hdiffNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat diff.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hSub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [subFunction, checkedSubUintInto, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem dealSubFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hlt : x.toNat < y.toNat) :
    ExecFuncBody config { contract := contract, locals := dealUintBinaryLocals x y } evm
      subFunction.body .reverted := by
  let locals := dealUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using dealEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (dealUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using dealEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (dealUintBinaryLocals_get_y x y)
  have hSubRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .revert :=
    dealEvalExpr_sub256_revert hx hy hlt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hSubRev)
  simpa [subFunction, checkedSubUintInto, locals] using ExecFuncBody.execBlockRevert hblock

theorem evalExpr_deal_live_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := liveRef) (er := dealLiveEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat))
    (by simp [frame, liveRef])
    (by simp [frame, dealLiveEvaledRef, evalStorageRef, evalStorageRefSteps,
      liveRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by exact flapperStorageLocLoad_uint256 evm ⟨7⟩)

theorem evalExpr_deal_live_one_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := dealLocals I } evm (.storage liveRef) =
        .ok (.int 1) := by
    simpa [hload] using evalExpr_deal_live_storage evm I
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_deal_live_one_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage := evalExpr_deal_live_storage evm I
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat) ≠
        Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    apply u256_inj
    exact Int.ofNat.inj hbad
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat) ==
        Value.int 1) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_deal_tic_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
        (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (dealTicWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (dealIdWord I)) ⟨20, by decide⟩ (by decide)) =
        .int (Int.ofNat (dealTicWord evm I).toNat) := by
    rw [flapperStorageLocLoad_uint48_offset20]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (dealIdWord I)))
        (UInt256.ofNat (256 ^ 20)))
      flapperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "tic") (er := dealTicEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (dealIdWord I)) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dealTicWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, dealTicEvaledRef, auctionIdKey, dealLocals, dealIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_deal_end_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
        (.storage (bidsF (.var "id") "end")) =
      .ok (.int (Int.ofNat (dealEndWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (dealIdWord I)) ⟨26, by decide⟩ (by decide)) =
        .int (Int.ofNat (dealEndWord evm I).toNat) := by
    rw [flapperStorageLocLoad_uint48_offset26]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (dealIdWord I)))
        (UInt256.ofNat (256 ^ 26)))
      flapperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "end") (er := dealEndEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (dealIdWord I)) ⟨26, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dealEndWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, dealEndEvaledRef, auctionIdKey, dealLocals, dealIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_deal_lot_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (dealLotWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "lot") (er := dealLotEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionLotSlot (dealIdWord I)))
    (value := .int (Int.ofNat (dealLotWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, dealLotEvaledRef, auctionIdKey, dealLocals, dealIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by
      simpa [dealLotWord, flapperSlotWord] using
        flapperStorageLocLoad_uint256 evm (auctionLotSlot (dealIdWord I)))

theorem evalExpr_deal_vat_storage_of_locals
    (evm : EVM.State) (locals : Store) (hvat : "vat" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat (dealVatWord evm).toNat)) := by
  simpa [dealVatWord] using evalExpr_cage_vat_storage_of_locals evm locals hvat

theorem evalExpr_deal_gem_storage_of_locals
    (evm : EVM.State) (locals : Store) (hgem : "gem" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat (dealGemWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := gemRef) (er := dealGemEvaledRef)
    (t := .address) (loc := addrLoc ⟨3⟩)
    (value := .address (AccountAddress.ofNat (dealGemWord evm).toNat))
    (by simpa [frame, gemRef] using hgem)
    (by simp [frame, dealGemEvaledRef, evalStorageRef, evalStorageRefSteps,
      gemRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [dealGemWord, flapperAddressReturnWord, flapperSlotWord] using
        flapperStorageLocLoad_address_offset0 evm ⟨3⟩)

theorem evalExpr_deal_guy_storage_of_lotLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLotLocals evm I } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat (dealGuyWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLotLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "guy") (er := dealGuyEvaledRef I)
    (t := .address) (loc := addrLoc (auctionPackedSlot (dealIdWord I)))
    (value := .address (AccountAddress.ofNat (dealGuyWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      change evalStorageRef config frame evm (bidsF (.var "id") "guy") =
        .ok (dealGuyEvaledRef I)
      simp only [frame, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF,
        evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
      rw [dealLotLocals_get_id evm I])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, addrSt])
    (by rfl)
    (by
      simpa [dealGuyWord, flapperAddressReturnWord, flapperSlotWord] using
        flapperStorageLocLoad_address_offset0 evm (auctionPackedSlot (dealIdWord I)))

theorem evalExpr_deal_lot_var (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLotLocals evm I } evm'
      (.var "lot") = .ok (.int (Int.ofNat (dealLotWord evm I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((dealLotLocals evm I).get? "lot") =
    .ok (.int (Int.ofNat (dealLotWord evm I).toNat))
  rw [dealLotLocals_get_lot]
  rfl

theorem evalExpr_deal_lot_var_of_burnLocals (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealBurnLocals evm0 I } evm
      (.var "lot") = .ok (.int (Int.ofNat (dealLotWord evm0 I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((dealBurnLocals evm0 I).get? "lot") =
    .ok (.int (Int.ofNat (dealLotWord evm0 I).toNat))
  rw [dealBurnLocals_get_lot]
  rfl

theorem evalExpr_deal_fillNew_var (evm0 evmFill evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealFillNewLocals evm0 evmFill I } evm
      (.var "fillNew") =
        .ok (.int (Int.ofNat
          (UInt256.sub (dealFillWord evmFill) (dealLotWord evm0 I)).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((dealFillNewLocals evm0 evmFill I).get? "fillNew") =
    .ok (.int (Int.ofNat
      (UInt256.sub (dealFillWord evmFill) (dealLotWord evm0 I)).toNat))
  rw [dealFillNewLocals_get_fillNew]
  rfl

theorem evalExpr_deal_this (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm thisAddr =
      .ok (.address evm.executionEnv.codeOwner) := by
  simpa using evalExpr_cage_this evm locals

theorem evalExprs_deal_move_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := dealLotLocals evm I } evm
        [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] =
      .ok [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
        .int (Int.ofNat (dealLotWord evm I).toNat)] := by
  simp [evalExprs?, evalExpr_deal_this, evalExpr_deal_guy_storage_of_lotLocals,
    evalExpr_deal_lot_var]
  rfl

theorem evalExpr_deal_bid_storage_of_moveLocals (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealMoveLocals evm0 I } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (dealBidWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealMoveLocals evm0 I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := dealBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (dealIdWord I)))
    (value := .int (Int.ofNat (dealBidWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp only [frame, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF,
        evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
      rw [dealMoveLocals_get_id evm0 I])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by
      simpa [dealBidWord, flapperSlotWord] using
        flapperStorageLocLoad_uint256 evm (auctionBidSlot (dealIdWord I)))

theorem evalExpr_deal_fill_storage_of_locals
    (evm : EVM.State) (locals : Store) (hfill : "fill" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage fillRef) =
      .ok (.int (Int.ofNat (dealFillWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := fillRef) (er := dealFillEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨9⟩)
    (value := .int (Int.ofNat (dealFillWord evm).toNat))
    (by simpa [frame, fillRef] using hfill)
    (by simp [frame, dealFillEvaledRef, evalStorageRef, evalStorageRefSteps,
      fillRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by
      simpa [dealFillWord, flapperSlotWord] using
        flapperStorageLocLoad_uint256 evm ⟨9⟩)

theorem evalExprs_deal_burn_args (evm0 evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := dealMoveLocals evm0 I } evm
        [thisAddr, .storage (bidsF (.var "id") "bid")] =
      .ok [.address evm.executionEnv.codeOwner,
        .int (Int.ofNat (dealBidWord evm I).toNat)] := by
  simp [evalExprs?, evalExpr_deal_this, evalExpr_deal_bid_storage_of_moveLocals]
  rfl

theorem evalExprs_deal_sub_args (evm0 evmFill : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := dealBurnLocals evm0 I } evmFill
        [.storage fillRef, .var "lot"] =
      .ok [.int (Int.ofNat (dealFillWord evmFill).toNat),
        .int (Int.ofNat (dealLotWord evm0 I).toNat)] := by
  simp [evalExprs?, evalExpr_deal_fill_storage_of_locals,
    evalExpr_deal_lot_var_of_burnLocals, EvalResult.bind, bind, pure]

theorem assign_deal_fillNew (evm0 evmFill : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := dealFillNewLocals evm0 evmFill I }
      evmFill .storage fillRef
      (.int (Int.ofNat (UInt256.sub (dealFillWord evmFill) (dealLotWord evm0 I)).toNat)) =
        .ok ({ contract := contract, locals := dealFillNewLocals evm0 evmFill I },
          Solm.EVM.storageStore evmFill evmFill.executionEnv.codeOwner ⟨9⟩
            (UInt256.sub (dealFillWord evmFill) (dealLotWord evm0 I))) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := dealFillEvaledRef)
      (loc := wordLoc ⟨9⟩)
      (hbase := by simp [dealFillNewLocals, dealBurnLocals, dealMoveLocals, dealLotLocals,
        dealLocals, fillRef])
      (her := by simp [dealFillEvaledRef, evalStorageRef, evalStorageRefSteps, fillRef,
        EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [dealFillWord] using
    storageLocStore_uint256 evmFill ⟨9⟩
      (UInt256.sub (dealFillWord evmFill) (dealLotWord evm0 I))

theorem dealMoveDecode_ok (out : ByteArray) :
    config.externalABI.decode? "move" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem dealBurnDecode_ok (out : ByteArray) :
    config.externalABI.decode? "burn" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem deleteStorage_dealBurn_bid (evm0 evm : EVM.State) (I : ExecutionEnv) :
    deleteStorage? config { contract := contract, locals := dealBurnLocals evm0 I } evm
      (bidRef (.var "id")) = .ok (auctionDeletePostState (dealIdWord I) evm) := by
  exact deleteStorage_auction_bid evm (dealBurnLocals evm0 I) (dealIdWord I)
    (by simpa [dealIdValue] using dealBurnLocals_get_id evm0 I)
    (dealBurnLocals_get_bids evm0 I)

theorem evalExpr_deal_tic_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (htic : dealTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool false) := by
  have hticEval := evalExpr_deal_tic_storage evm I
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  rw [htic]
  simp [evalBinaryOp?]

theorem evalExpr_deal_tic_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (htic : dealTicWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool true) := by
  have hticEval := evalExpr_deal_tic_storage evm I
  have hne :
      Value.int (Int.ofNat (dealTicWord evm I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact htic (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (dealTicWord evm I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]
  rfl

theorem evalExpr_deal_tic_lt_timestamp_true (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hticEval := evalExpr_deal_tic_storage evm I
  simp only [evalExpr?, hticEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [dealTimestampWord] using hlt

theorem evalExpr_deal_tic_lt_timestamp_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (dealTimestampWord evm).toNat ≤ (dealTicWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hticEval := evalExpr_deal_tic_storage evm I
  have hnlt : ¬ (Int.ofNat (dealTicWord evm I).toNat <
      Int.ofNat (dealTimestampWord evm).toNat) := by
    intro hlt
    have hltNat : (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat :=
      Int.ofNat_lt.mp hlt
    exact (Nat.not_lt.mpr hle) hltNat
  have hdec :
      decide (Int.ofNat (dealTicWord evm I).toNat <
        Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) = false := by
    rw [decide_eq_false_iff_not]
    simpa [dealTimestampWord] using hnlt
  simp only [evalExpr?, hticEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_deal_end_lt_timestamp_true (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hendEval := evalExpr_deal_end_storage evm I
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [dealTimestampWord] using hlt

theorem evalExpr_deal_end_lt_timestamp_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (dealTimestampWord evm).toNat ≤ (dealEndWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hendEval := evalExpr_deal_end_storage evm I
  have hnlt : ¬ (Int.ofNat (dealEndWord evm I).toNat <
      Int.ofNat (dealTimestampWord evm).toNat) := by
    intro hlt
    have hltNat : (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat :=
      Int.ofNat_lt.mp hlt
    exact (Nat.not_lt.mpr hle) hltNat
  have hdec :
      decide (Int.ofNat (dealEndWord evm I).toNat <
        Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) = false := by
    rw [decide_eq_false_iff_not]
    simpa [dealTimestampWord] using hnlt
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_deal_finished_false_tic_zero (evm : EVM.State) (I : ExecutionEnv)
    (htic : dealTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .and
        (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
        (.binary .or
          (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) =
      .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_deal_tic_ne_zero_false evm I htic,
    EvalResult.bind, bind, pure]

theorem evalExpr_deal_finished_false_unexpired (evm : EVM.State) (I : ExecutionEnv)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hticGe : (dealTimestampWord evm).toNat ≤ (dealTicWord evm I).toNat)
    (hendGe : (dealTimestampWord evm).toNat ≤ (dealEndWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .and
        (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
        (.binary .or
          (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) =
      .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_deal_tic_ne_zero_true evm I htic,
    evalExpr_deal_tic_lt_timestamp_false evm I hticGe,
    evalExpr_deal_end_lt_timestamp_false evm I hendGe, EvalResult.bind, bind, pure]

theorem evalExpr_deal_finished_true (evm : EVM.State) (I : ExecutionEnv)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .and
        (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
        (.binary .or
          (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) =
      .ok (.bool true) := by
  by_cases hticLt : (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat
  · simp only [evalExpr?, evalExpr_deal_tic_ne_zero_true evm I htic,
      evalExpr_deal_tic_lt_timestamp_true evm I hticLt, EvalResult.bind, bind, pure]
  · have hendLt : (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat := by
      cases hfinished with
      | inl h => exact False.elim (hticLt h)
      | inr h => exact h
    have hticGe : (dealTimestampWord evm).toNat ≤ (dealTicWord evm I).toNat :=
      Nat.le_of_not_gt hticLt
    simp only [evalExpr?, evalExpr_deal_tic_ne_zero_true evm I htic,
      evalExpr_deal_tic_lt_timestamp_false evm I hticGe,
      evalExpr_deal_end_lt_timestamp_true evm I hendLt, EvalResult.bind, bind, pure]

theorem flapperDealBodyReverts_notLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := dealLocals I })
      (evm := evm)
      (guard := .binary .eq (.storage liveRef) (.intLit 1))
      (rest :=
        [.require
          (.binary .and
            (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (.binary .or
              (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
              (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))),
          .letDecl "lot" (some uint256) (.storage (bidsF (.var "id") "lot"))] ++
          checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet" ++
          [.delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew")])
      hwv
      (evalExpr_deal_live_one_false evm I hlive)

theorem flapperDealBodyReverts_ticZero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_deal_finished_false_tic_zero evm I htic)))

theorem flapperDealBodyReverts_notFinished (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hticGe : (dealTimestampWord evm).toNat ≤ (dealTicWord evm I).toNat)
    (hendGe : (dealTimestampWord evm).toNat ≤ (dealEndWord evm I).toNat) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_deal_finished_false_unexpired evm I htic hticGe hendGe)))

theorem flapperDealBodyReverts_moveNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealVatWord evm) = ⟨0⟩) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  have hvat :=
    evalExpr_deal_vat_storage_of_locals evm (dealLotLocals evm I)
      (by simp [dealLotLocals, dealLocals])
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap)
        (target := dealVatWord evm)
        (addr := AccountAddress.ofNat (dealVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := dealLotLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_cage_extCodeGuard_false hvat hnoCodeLookup
  have hchecked :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet")
        .reverted := by
    exact checkedExternalCallNoCode hguard
  have hmoveTail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hchecked (by intro f e h; cases h)
  have htail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        ((checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet") ++
          [.delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew")])
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hmoveTail (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_deal_lot_storage evm I)) <|
      htail)

theorem flapperDealBodyReverts_moveCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealVatWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealVatWord evm).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  have hvat :=
    evalExpr_deal_vat_storage_of_locals evm (dealLotLocals evm I)
      (by simp [dealLotLocals, dealLocals])
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dealVatWord evm)
        (addr := AccountAddress.ofNat (dealVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dealLotLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_deal_move_args evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet")
        .reverted := by
    exact checkedExternalCallFailure hguard hvat hargs hcall
  have hmoveTail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hchecked (by intro f e h; cases h)
  have htail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        ((checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet") ++
          [.delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew")])
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hmoveTail (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_deal_lot_storage evm I)) <|
      htail)

theorem flapperDealBodyReverts_burnNoCode
    (evm evmMove : EVM.State) (I : ExecutionEnv) (outMove : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hmoveCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealVatWord evm) ≠ ⟨0⟩)
    (hmoveCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealVatWord evm).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (true, evmMove, outMove) true)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap
        (dealGemWord evmMove) = ⟨0⟩) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  have hvat :=
    evalExpr_deal_vat_storage_of_locals evm (dealLotLocals evm I)
      (by simp [dealLotLocals, dealLocals])
  have hmoveCodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dealVatWord evm)
        (addr := AccountAddress.ofNat (dealVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hmoveCodeSize
  have hmoveGuard :
      evalExpr? config { contract := contract, locals := dealLotLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hmoveCodeLookup
  have hmoveArgs := evalExprs_deal_move_args evm I
  have hmoveChecked :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet")
        (.ok { contract := contract, locals := dealMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dealMoveLocals] using
      checkedExternalCallSuccess hmoveGuard hvat hmoveArgs hmoveCall
        (dealMoveDecode_ok outMove)
  have hgem :=
    evalExpr_deal_gem_storage_of_locals evmMove (dealMoveLocals evm I)
      (by simp [dealMoveLocals, dealLotLocals, dealLocals])
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dealGemWord evmMove).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evmMove.accountMap)
        (target := dealGemWord evmMove)
        (addr := AccountAddress.ofNat (dealGemWord evmMove).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hburnGuard :
      evalExpr? config { contract := contract, locals := dealMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_cage_extCodeGuard_false hgem hnoCodeLookup
  have hburnChecked :
      ExecBlock config { contract := contract, locals := dealMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
        .reverted := by
    exact checkedExternalCallNoCode hburnGuard
  have hmoveTail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
        .reverted :=
    Reasoning.Refinement.execBlock_append hmoveChecked hburnChecked
  have htail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        ((checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet") ++
          [.delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew")])
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hmoveTail (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_deal_lot_storage evm I)) <|
      htail)

theorem flapperDealBodyReverts_burnCallFailure
    (evm evmMove evmBurn : EVM.State) (I : ExecutionEnv)
    (outMove outBurn : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hmoveCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealVatWord evm) ≠ ⟨0⟩)
    (hmoveCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealVatWord evm).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (true, evmMove, outMove) true)
    (hburnCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap
        (dealGemWord evmMove) ≠ ⟨0⟩)
    (hburnCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dealGemWord evmMove).toNat))
        "burn" 0
        [.address evmMove.executionEnv.codeOwner,
          .int (Int.ofNat (dealBidWord evmMove I).toNat)]
        (false, evmBurn, outBurn) true) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  have hvat :=
    evalExpr_deal_vat_storage_of_locals evm (dealLotLocals evm I)
      (by simp [dealLotLocals, dealLocals])
  have hmoveCodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dealVatWord evm)
        (addr := AccountAddress.ofNat (dealVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hmoveCodeSize
  have hmoveGuard :
      evalExpr? config { contract := contract, locals := dealLotLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hmoveCodeLookup
  have hmoveArgs := evalExprs_deal_move_args evm I
  have hmoveChecked :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet")
        (.ok { contract := contract, locals := dealMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dealMoveLocals] using
      checkedExternalCallSuccess hmoveGuard hvat hmoveArgs hmoveCall
        (dealMoveDecode_ok outMove)
  have hgem :=
    evalExpr_deal_gem_storage_of_locals evmMove (dealMoveLocals evm I)
      (by simp [dealMoveLocals, dealLotLocals, dealLocals])
  have hburnCodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dealGemWord evmMove).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := dealGemWord evmMove)
        (addr := AccountAddress.ofNat (dealGemWord evmMove).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hburnCodeSize
  have hburnGuard :
      evalExpr? config { contract := contract, locals := dealMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hgem hburnCodeLookup
  have hburnArgs := evalExprs_deal_burn_args evm evmMove I
  have hburnChecked :
      ExecBlock config { contract := contract, locals := dealMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
        .reverted := by
    exact checkedExternalCallFailure hburnGuard hgem hburnArgs hburnCall
  have hmoveTail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
        .reverted :=
    Reasoning.Refinement.execBlock_append hmoveChecked hburnChecked
  have htail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        ((checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet") ++
          [.delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew")])
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hmoveTail (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_deal_lot_storage evm I)) <|
      htail)

theorem flapperDealBodyBurnSuccessPrefix
    (evm evmMove evmBurn : EVM.State) (I : ExecutionEnv)
    (outMove outBurn : ByteArray)
    (hmoveCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealVatWord evm) ≠ ⟨0⟩)
    (hmoveCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealVatWord evm).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (true, evmMove, outMove) true)
    (hburnCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap
        (dealGemWord evmMove) ≠ ⟨0⟩)
    (hburnCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dealGemWord evmMove).toNat))
        "burn" 0
        [.address evmMove.executionEnv.codeOwner,
          .int (Int.ofNat (dealBidWord evmMove I).toNat)]
        (true, evmBurn, outBurn) true) :
    ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
      (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
        [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
        checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
      (.ok { contract := contract, locals := dealBurnLocals evm I } evmBurn) := by
  have hvat :=
    evalExpr_deal_vat_storage_of_locals evm (dealLotLocals evm I)
      (by simp [dealLotLocals, dealLocals])
  have hmoveCodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealVatWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dealVatWord evm)
        (addr := AccountAddress.ofNat (dealVatWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hmoveCodeSize
  have hmoveGuard :
      evalExpr? config { contract := contract, locals := dealLotLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hvat hmoveCodeLookup
  have hmoveArgs := evalExprs_deal_move_args evm I
  have hmoveChecked :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet")
        (.ok { contract := contract, locals := dealMoveLocals evm I } evmMove) := by
    simpa [checkedExternalCallStmts, dealMoveLocals] using
      checkedExternalCallSuccess hmoveGuard hvat hmoveArgs hmoveCall
        (dealMoveDecode_ok outMove)
  have hgem :=
    evalExpr_deal_gem_storage_of_locals evmMove (dealMoveLocals evm I)
      (by simp [dealMoveLocals, dealLotLocals, dealLocals])
  have hburnCodeLookup :
      0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat (dealGemWord evmMove).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMove.accountMap)
        (target := dealGemWord evmMove)
        (addr := AccountAddress.ofNat (dealGemWord evmMove).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hburnCodeSize
  have hburnGuard :
      evalExpr? config { contract := contract, locals := dealMoveLocals evm I } evmMove
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hgem hburnCodeLookup
  have hburnArgs := evalExprs_deal_burn_args evm evmMove I
  have hburnChecked :
      ExecBlock config { contract := contract, locals := dealMoveLocals evm I } evmMove
        (checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet")
        (.ok { contract := contract, locals := dealBurnLocals evm I } evmBurn) := by
    simpa [checkedExternalCallStmts, dealBurnLocals] using
      checkedExternalCallSuccess hburnGuard hgem hburnArgs hburnCall
        (dealBurnDecode_ok outBurn)
  exact Reasoning.Refinement.execBlock_append hmoveChecked hburnChecked

theorem flapperDealBodyReverts_fillSubUnderflow
    (evm evmMove evmBurn : EVM.State) (I : ExecutionEnv)
    (outMove outBurn : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hmoveCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealVatWord evm) ≠ ⟨0⟩)
    (hmoveCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealVatWord evm).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (true, evmMove, outMove) true)
    (hburnCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap
        (dealGemWord evmMove) ≠ ⟨0⟩)
    (hburnCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dealGemWord evmMove).toNat))
        "burn" 0
        [.address evmMove.executionEnv.codeOwner,
          .int (Int.ofNat (dealBidWord evmMove I).toNat)]
        (true, evmBurn, outBurn) true)
    (hfillLt :
      (dealFillWord (auctionDeletePostState (dealIdWord I) evmBurn)).toNat <
        (dealLotWord evm I).toNat) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  let evmDelete := auctionDeletePostState (dealIdWord I) evmBurn
  have hprefix :=
    flapperDealBodyBurnSuccessPrefix evm evmMove evmBurn I outMove outBurn
      hmoveCodeSize hmoveCall hburnCodeSize hburnCall
  have hlookupSub : lookupCallable? contract "sub" = some subFunction.toCallable := by
    rfl
  have hbindSub :
      bindParams? subFunction.params
          [.int (Int.ofNat (dealFillWord evmDelete).toNat),
            .int (Int.ofNat (dealLotWord evm I).toNat)] =
        some (dealUintBinaryLocals (dealFillWord evmDelete) (dealLotWord evm I)) := by
    simp [subFunction, dealUintBinaryLocals, bindParams?]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := dealBurnLocals evm I } evmDelete
        (.internalCall "sub" [.storage fillRef, .var "lot"] "fillNew") .reverted :=
    internalCallFunctionRevert
      (cfg := config)
      (caller := Frame.mk contract (dealBurnLocals evm I))
      (evm := evmDelete) (name := "sub") (retVar := "fillNew")
      (args := [.storage fillRef, .var "lot"])
      (argVals := [.int (Int.ofNat (dealFillWord evmDelete).toNat),
        .int (Int.ofNat (dealLotWord evm I).toNat)])
      (callee := subFunction)
      (locals := dealUintBinaryLocals (dealFillWord evmDelete) (dealLotWord evm I))
      (evalExprs_deal_sub_args evm evmDelete I)
      hlookupSub hbindSub
      (dealSubFunctionRevert evmDelete hfillLt)
  have hdeleteSub :
      ExecBlock config { contract := contract, locals := dealBurnLocals evm I } evmBurn
        [.delete (bidRef (.var "id")),
          .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
          .assign .storage fillRef (.var "fillNew")]
        .reverted := by
    exact ExecBlock.consNormal
      (ExecStmt.delete (deleteStorage_dealBurn_bid evm evmBurn I)) <|
      ExecBlock.consRevert hsubStmt
  have htail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        ((checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet") ++
          [.delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew")])
        .reverted := by
    simpa [List.append_assoc] using
      (Reasoning.Refinement.execBlock_append hprefix hdeleteSub)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append, List.append_assoc] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_deal_lot_storage evm I)) <|
      htail)

theorem flapperDealBodyReturns_success
    (evm evmMove evmBurn : EVM.State) (I : ExecutionEnv)
    (outMove outBurn : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hmoveCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealVatWord evm) ≠ ⟨0⟩)
    (hmoveCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealVatWord evm).toNat))
        "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (true, evmMove, outMove) true)
    (hburnCodeSize :
      Reasoning.Theory.extCodeSizeWord evmMove.accountMap
        (dealGemWord evmMove) ≠ ⟨0⟩)
    (hburnCall :
      typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat (dealGemWord evmMove).toNat))
        "burn" 0
        [.address evmMove.executionEnv.codeOwner,
          .int (Int.ofNat (dealBidWord evmMove I).toNat)]
        (true, evmBurn, outBurn) true)
    (hfillLe :
      (dealLotWord evm I).toNat ≤
        (dealFillWord (auctionDeletePostState (dealIdWord I) evmBurn)).toNat) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body
      (.returned
        { contract := contract,
          locals := dealFillNewLocals evm (auctionDeletePostState (dealIdWord I) evmBurn) I }
        (Solm.EVM.storageStore (auctionDeletePostState (dealIdWord I) evmBurn)
          (auctionDeletePostState (dealIdWord I) evmBurn).executionEnv.codeOwner ⟨9⟩
          (UInt256.sub
            (dealFillWord (auctionDeletePostState (dealIdWord I) evmBurn))
            (dealLotWord evm I)))
        none) := by
  let evmDelete := auctionDeletePostState (dealIdWord I) evmBurn
  let diff := UInt256.sub (dealFillWord evmDelete) (dealLotWord evm I)
  let evmFinal :=
    Solm.EVM.storageStore evmDelete evmDelete.executionEnv.codeOwner ⟨9⟩ diff
  have hprefix :=
    flapperDealBodyBurnSuccessPrefix evm evmMove evmBurn I outMove outBurn
      hmoveCodeSize hmoveCall hburnCodeSize hburnCall
  have hlookupSub : lookupCallable? contract "sub" = some subFunction.toCallable := by
    rfl
  have hbindSub :
      bindParams? subFunction.params
          [.int (Int.ofNat (dealFillWord evmDelete).toNat),
            .int (Int.ofNat (dealLotWord evm I).toNat)] =
        some (dealUintBinaryLocals (dealFillWord evmDelete) (dealLotWord evm I)) := by
    simp [subFunction, dealUintBinaryLocals, bindParams?]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := dealBurnLocals evm I } evmDelete
        (.internalCall "sub" [.storage fillRef, .var "lot"] "fillNew")
        (.ok { contract := contract, locals := dealFillNewLocals evm evmDelete I }
          evmDelete) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (dealBurnLocals evm I))
      (evm := evmDelete) (name := "sub") (retVar := "fillNew")
      (args := [.storage fillRef, .var "lot"])
      (argVals := [.int (Int.ofNat (dealFillWord evmDelete).toNat),
        .int (Int.ofNat (dealLotWord evm I).toNat)])
      (callee := subFunction)
      (locals := dealUintBinaryLocals (dealFillWord evmDelete) (dealLotWord evm I))
      (evalExprs_deal_sub_args evm evmDelete I)
      hlookupSub hbindSub
      (dealSubFunctionReturn evmDelete
        (x := dealFillWord evmDelete) (y := dealLotWord evm I) (diff := diff) rfl hfillLe)
    simpa [resumeAfterInternalCall, dealFillNewLocals, diff] using h
  have hassignStmt :
      ExecStmt config { contract := contract, locals := dealFillNewLocals evm evmDelete I }
        evmDelete
        (.assign .storage fillRef (.var "fillNew"))
        (.ok { contract := contract, locals := dealFillNewLocals evm evmDelete I }
          evmFinal) := by
    simpa [evmFinal, diff] using
      (ExecStmt.assign (evalExpr_deal_fillNew_var evm evmDelete evmDelete I)
        (assign_deal_fillNew evm evmDelete I))
  have hdeleteSubAssign :
      ExecBlock config { contract := contract, locals := dealBurnLocals evm I } evmBurn
        [.delete (bidRef (.var "id")),
          .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
          .assign .storage fillRef (.var "fillNew")]
        (.ok { contract := contract, locals := dealFillNewLocals evm evmDelete I }
          evmFinal) := by
    exact ExecBlock.consNormal
      (ExecStmt.delete (deleteStorage_dealBurn_bid evm evmBurn I)) <|
      ExecBlock.consNormal hsubStmt <|
      ExecBlock.consNormal hassignStmt ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := dealLotLocals evm I } evm
        ((checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
          checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet") ++
          [.delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew")])
        (.ok { contract := contract, locals := dealFillNewLocals evm evmDelete I }
          evmFinal) := by
    simpa [List.append_assoc] using
      (Reasoning.Refinement.execBlock_append hprefix hdeleteSubAssign)
  refine ExecFuncBody.execBlockOK ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append, List.append_assoc, evmDelete, evmFinal, diff] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_deal_lot_storage evm I)) <|
      htail)

theorem flapperDecode_deal_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I) := by
  simpa [config, dealTransition, dealLocals, dealIdValue, dealIdWord, calldataWord] using
    decodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "id") hsz36

theorem flapperDecode_deal_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata = none := by
  simpa [config, dealTransition] using
    decodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "id") hsz4 hshort

theorem flapperReachDealBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 3)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨767⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0xc959c42b⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xc9 0x59 0xc4 0x2b ⟨0xc959c42b⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc 4))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨767⟩ 4 hfirst
    (fun j hj => flapperHighLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperDealX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3334⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flapperBytecode) (sel := sel) (entry := ⟨767⟩) (ret := ⟨360⟩)
    (decoded := ⟨789⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd790 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd791 := rd790.pop (by native_decide) (by evm_ov)
  have rd792 := rd791.calldataload (by native_decide) (by evm_ov)
  have rd795 := rd792.push2 ⟨3334⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [dealIdWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd795.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperDealX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flapperBytecode) (sel := sel) (entry := ⟨767⟩) (ret := ⟨360⟩)
    (decoded := ⟨789⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flapperDealX_notLive {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I ≠ ⟨1⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3334⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3334⟩ := h
  have rd3337 := evm_run rd3334 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3338, C3338, rd3338raw⟩ := rd3337.sload (by native_decide) (by evm_ov)
  have rd3338 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3338⟩
      (flapperSlotWord ⟨7⟩ σ I :: dealIdWord I :: ⟨360⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3338 C3338 := by
    simpa [flapperSlotWord] using rd3338raw
  have rd3344 := evm_run rd3338 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨3408⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flapperSlotWord ⟨7⟩ σ I) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro hbad
    exact hlive hbad.symm
  have rd3345 := rd3344.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3345⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨0x466c61707065722f6e6f742d6c697665⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c61707065722f6e6f742d6c69766500000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd3345
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp)

theorem flapperDealX_liveOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3334⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3334⟩ := h
  have rd3337 := evm_run rd3334 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3338, C3338, rd3338raw⟩ := rd3337.sload (by native_decide) (by evm_ov)
  have rd3338 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3338⟩
      (flapperSlotWord ⟨7⟩ σ I :: dealIdWord I :: ⟨360⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3338 C3338 := by
    simpa [flapperSlotWord] using rd3338raw
  have rd3344 := evm_run rd3338 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨3408⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flapperSlotWord ⟨7⟩ σ I) ≠ ⟨0⟩ := by
    rw [hlive, u256_eq_refl]
    exact one_ne_zero_uint
  exact ⟨_, _, rd3344.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperDealX_toTicGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd3408 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3442⟩
      [flapperUint48Offset20Word (auctionPackedSlot id) σ I, id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap
  let memKey := wordAt0Mem id solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  have rd3413pre := evm_run rd3408 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3414 := rd3413pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3418pre := evm_run rd3414 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3419 := rd3418pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3422pre := evm_run rd3419 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id solcFreePtrMem
  have rd3423 := rd3422pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd3426pre := evm_run rd3423 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd3426pre
  obtain ⟨k3427, C3427, rd3427raw⟩ := rd3426pre.sload (by native_decide) (by evm_ov)
  have rd3427 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3427⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3427 C3427 := by
    simpa [flapperSlotWord] using rd3427raw
  have rd3434 := evm_run rd3427 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd3441 := rd3434.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd3442 := rd3441.and (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flapperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd3442⟩

set_option maxHeartbeats 1000000 in
theorem flapperDealX_ticZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I = ⟨0⟩)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := dealIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  obtain ⟨_, _, rd3408'⟩ := rd3408
  obtain ⟨_, _, rd3442⟩ := flapperDealX_toTicGuard rd3408'
  have rd3449 := evm_run rd3442 with [
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3529⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I) ≠
      ⟨0⟩ := by
    rw [show flapperUint48Offset20Word (auctionPackedSlot id) σ I =
      flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I from rfl, htic]
    decide
  have rd3529 := rd3449.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd3530 := rd3529.jumpdest (by native_decide) (by evm_ov)
  have rd3533 := rd3530.push2 ⟨3601⟩ (by native_decide) (by evm_ov)
  have hnotFinished :
      UInt256.isZero
        (UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I)) =
        ⟨0⟩ := by
    rw [show flapperUint48Offset20Word (auctionPackedSlot id) σ I =
      flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I from rfl, htic]
    native_decide
  have rd3534raw := rd3533.jumpiNT (by native_decide) hnotFinished (by evm_ov)
  have hpc3534 : (⟨3529⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3534⟩ := by
    native_decide
  rw [hpc3534] at rd3534raw
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3534⟩)
    (len := ⟨20⟩)
    (rawWord := ⟨0x119b185c1c195c8bdb9bdd0b599a5b9a5cda1959⟩)
    (shift := ⟨98⟩)
    (word := ⟨0x466c61707065722f6e6f742d66696e6973686564000000000000000000000000⟩)
    (op := .PUSH20)
    (width := 20)
    rd3534raw
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (by
      simpa [memMap, id] using
        twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size)
    (by
      simpa [memMap, id] using
        twoWordHashMem_read64 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)
    (by simp)

theorem flapperDealX_ticNonzero_toTicLtStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (rd3442 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3442⟩
      [flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I, dealIdWord I,
        ⟨360⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3451⟩
      [dealIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3449 := evm_run rd3442 with [
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3529⟩ (by native_decide) (by evm_ov)]
  have hcond :
      UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne htic
  have rd3450 := rd3449.jumpiNT (by native_decide) hcond (by evm_ov)
  exact ⟨_, _, rd3450.pop (by native_decide) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperDealX_toTicLtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd3451 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3451⟩
      [dealIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memTic := twoWordHashMem id ⟨1⟩ (twoWordHashMem id ⟨1⟩ solcFreePtrMem)
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3487⟩
      [UInt256.lt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memTic
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memKey := wordAt0Mem id mem0
  let base := solcMappingSlot ⟨1⟩ id
  have rd3455pre := evm_run rd3451 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3456 := rd3455pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, mem0, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3460pre := evm_run rd3456 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3461 := rd3460pre.mstore 0 memTic (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTic, mem0, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3464pre := evm_run rd3461 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTic.readWithPadding 0 64))) = base := by
    have hmem0Size : mem0.size = 96 := by
      simpa [mem0, id] using
        twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
    simpa [base, memTic, mem0, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem0
  have rd3465 := rd3464pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd3468pre := evm_run rd3465 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd3468pre
  obtain ⟨k3469, C3469, rd3469raw⟩ := rd3468pre.sload (by native_decide) (by evm_ov)
  have rd3469 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3469⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3469 C3469 := by
    simpa [flapperSlotWord] using rd3469raw
  have rd3478 := evm_run rd3469 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd3485 := rd3478.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd3486 := rd3485.and (by native_decide) (by evm_ov)
  have rd3487 := rd3486.lt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flapperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd3487⟩

set_option maxHeartbeats 1000000 in
theorem flapperDealX_toEndLtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd3493 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3493⟩
      [dealIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩
        (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memTic := twoWordHashMem id ⟨1⟩ (twoWordHashMem id ⟨1⟩ solcFreePtrMem)
    let memEnd := twoWordHashMem id ⟨1⟩ memTic
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3529⟩
      [UInt256.lt (flapperUint48Offset26Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), id, ⟨360⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memTic memEnd
  let memKey := wordAt0Mem id memTic
  let base := solcMappingSlot ⟨1⟩ id
  have rd3497pre := evm_run rd3493 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3498 := rd3497pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memTic, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3502pre := evm_run rd3498 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3503 := rd3502pre.mstore 0 memEnd (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memEnd, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3506pre := evm_run rd3503 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memEnd.readWithPadding 0 64))) = base := by
    simpa [base, memEnd, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd3507 := rd3506pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd3510pre := evm_run rd3507 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd3510pre
  obtain ⟨k3511, C3511, rd3511raw⟩ := rd3510pre.sload (by native_decide) (by evm_ov)
  have rd3511 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3511⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, id, ⟨360⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3511 C3511 := by
    simpa [flapperSlotWord] using rd3511raw
  have rd3520 := evm_run rd3511 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd3527 := rd3520.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd3528 := rd3527.and (by native_decide) (by evm_ov)
  have rd3529 := rd3528.lt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flapperUint48Offset26Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = UInt256.ofNat (256 ^ 26)
        from by native_decide]
      using rd3529⟩

set_option maxHeartbeats 1000000 in
theorem flapperDealX_notFinished {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hticGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat)
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd3408'⟩ := rd3408
  obtain ⟨_, _, rd3442⟩ := flapperDealX_toTicGuard rd3408'
  obtain ⟨_, _, rd3451⟩ :=
    flapperDealX_ticNonzero_toTicLtStart (g := g) htic
      (by simpa [id, mem0] using rd3442)
  obtain ⟨_, _, rd3487⟩ := flapperDealX_toTicLtGuard rd3451
  have hticLt :
      UInt256.lt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hticGe
  have rd3491 := evm_run rd3487 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨3529⟩ (by native_decide) (by evm_ov)]
  have rd3492 := rd3491.jumpiNT (by native_decide) hticLt (by evm_ov)
  have rd3493raw := rd3492.pop (by native_decide) (by evm_ov)
  have hpc3493 : (⟨3487⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ =
      ⟨3493⟩ := by
    native_decide
  rw [hpc3493] at rd3493raw
  obtain ⟨_, _, rd3493⟩ : ∃ k C,
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3493⟩
        [id, ⟨360⟩, sel] memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [id, memTic, hticLt] using rd3493raw⟩
  obtain ⟨_, _, rd3529⟩ := flapperDealX_toEndLtGuard rd3493
  have hendLt :
      UInt256.lt (flapperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hendGe
  have rd3530 := rd3529.jumpdest (by native_decide) (by evm_ov)
  have rd3533 := rd3530.push2 ⟨3601⟩ (by native_decide) (by evm_ov)
  have rd3534raw := rd3533.jumpiNT (by native_decide) hendLt (by evm_ov)
  have hpc3534 : (⟨3529⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3534⟩ := by
    native_decide
  rw [hpc3534] at rd3534raw
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3534⟩)
    (len := ⟨20⟩)
    (rawWord := ⟨0x119b185c1c195c8bdb9bdd0b599a5b9a5cda1959⟩)
    (shift := ⟨98⟩)
    (word := ⟨0x466c61707065722f6e6f742d66696e6973686564000000000000000000000000⟩)
    (op := .PUSH20)
    (width := 20)
    rd3534raw
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (by
      simpa [memEnd, memTic, id] using
        twoWordHashMem_size_96 id ⟨1⟩
          (by
            simpa [memTic, id, mem0] using
              twoWordHashMem_size_96 id ⟨1⟩
                (by
                  simpa [mem0, id] using
                    twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size)))
    (by
      have hmem0 : mem0.size = 96 := by
        simpa [mem0, id] using
          twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
      have hread0 : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [mem0, id] using
          twoWordHashMem_read64 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, id, mem0] using twoWordHashMem_size_96 id ⟨1⟩ hmem0
      have hreadTic : memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memTic, id, mem0] using twoWordHashMem_read64 id ⟨1⟩ hmem0 hread0
      simpa [memEnd, id, memTic] using twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic)
    (by simp)

theorem flapperDealX_ticLtReadyToMove
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hticLt :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3601⟩
      [dealIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩
        (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  obtain ⟨_, _, rd3408'⟩ := rd3408
  obtain ⟨_, _, rd3442⟩ := flapperDealX_toTicGuard rd3408'
  obtain ⟨_, _, rd3451⟩ :=
    flapperDealX_ticNonzero_toTicLtStart (g := g) htic
      (by simpa [id, mem0] using rd3442)
  obtain ⟨_, _, rd3487⟩ := flapperDealX_toTicLtGuard rd3451
  have hticLtWord :
      UInt256.lt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ult_one
    simpa [id] using hticLt
  have rd3491 := evm_run rd3487 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨3529⟩ (by native_decide) (by evm_ov)]
  have rd3529 := rd3491.jumpiT (by native_decide)
    (by rw [hticLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  have rd3530 := rd3529.jumpdest (by native_decide) (by evm_ov)
  have rd3533 := rd3530.push2 ⟨3601⟩ (by native_decide) (by evm_ov)
  have rd3601 := rd3533.jumpiT (by native_decide)
    (by rw [hticLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [id, mem0, memTic, hticLtWord] using rd3601⟩

theorem flapperDealX_endLtReadyToMove
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hticGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat)
    (hendLt :
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3601⟩
      [dealIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩
        (twoWordHashMem (dealIdWord I) ⟨1⟩
          (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd3408'⟩ := rd3408
  obtain ⟨_, _, rd3442⟩ := flapperDealX_toTicGuard rd3408'
  obtain ⟨_, _, rd3451⟩ :=
    flapperDealX_ticNonzero_toTicLtStart (g := g) htic
      (by simpa [id, mem0] using rd3442)
  obtain ⟨_, _, rd3487⟩ := flapperDealX_toTicLtGuard rd3451
  have hticLtWord :
      UInt256.lt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hticGe
  have rd3491 := evm_run rd3487 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨3529⟩ (by native_decide) (by evm_ov)]
  have rd3492 := rd3491.jumpiNT (by native_decide) hticLtWord (by evm_ov)
  have rd3493raw := rd3492.pop (by native_decide) (by evm_ov)
  have hpc3493 : (⟨3487⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ =
      ⟨3493⟩ := by
    native_decide
  rw [hpc3493] at rd3493raw
  obtain ⟨_, _, rd3493⟩ : ∃ k C,
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3493⟩
        [id, ⟨360⟩, sel] memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [id, memTic, hticLtWord] using rd3493raw⟩
  obtain ⟨_, _, rd3529⟩ := flapperDealX_toEndLtGuard rd3493
  have hendLtWord :
      UInt256.lt (flapperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ult_one
    simpa [id] using hendLt
  have rd3530 := rd3529.jumpdest (by native_decide) (by evm_ov)
  have rd3533 := rd3530.push2 ⟨3601⟩ (by native_decide) (by evm_ov)
  have rd3601 := rd3533.jumpiT (by native_decide)
    (by rw [hendLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [id, mem0, memTic, memEnd, hendLtWord] using rd3601⟩

theorem flapperDealX_readyToMove
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ memStart k C,
      memStart.size = 96 ∧
      memStart.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3601⟩
        [dealIdWord I, ⟨360⟩, sel]
        memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  have hmem0 : mem0.size = 96 := by
    simpa [mem0, id] using
      twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hread0 : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0, id] using
      twoWordHashMem_read64 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
        solcFreePtrMem_read64
  have hmemTic : memTic.size = 96 := by
    simpa [memTic, id, mem0] using twoWordHashMem_size_96 id ⟨1⟩ hmem0
  have hreadTic : memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memTic, id, mem0] using twoWordHashMem_read64 id ⟨1⟩ hmem0 hread0
  by_cases hticLt :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat
  · obtain ⟨_, _, rd3601⟩ :=
      flapperDealX_ticLtReadyToMove (g := g) htic hticLt rd3408
    exact ⟨memTic, _, _, hmemTic, hreadTic, by simpa [id, mem0, memTic] using rd3601⟩
  · have hendLt :
        (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
          (UInt256.ofNat I.header.timestamp).toNat := by
      cases hfinished with
      | inl h => exact False.elim (hticLt h)
      | inr h => exact h
    have hticGe :
        (UInt256.ofNat I.header.timestamp).toNat ≤
          (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat :=
      Nat.le_of_not_gt hticLt
    have hmemEnd : memEnd.size = 96 := by
      simpa [memEnd, id, memTic] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
    have hreadEnd : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memEnd, id, memTic] using
        twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
    obtain ⟨_, _, rd3601⟩ :=
      flapperDealX_endLtReadyToMove (g := g) htic hticGe hendLt rd3408
    exact ⟨memEnd, _, _, hmemEnd, hreadEnd,
      by simpa [id, mem0, memTic, memEnd] using rd3601⟩

set_option maxHeartbeats 1000000 in
theorem flapperDealX_toMoveExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (hmemStart : memStart.size = 96)
    (hread64Start : memStart.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd3601 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3601⟩
      [dealIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memStart
    let vat := dealVatWord (initState cA gh bl σ σ₀ g A I)
    let src := yankThisWord I
    let guy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let lot := flapperSlotWord (auctionLotSlot id) σ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3699⟩
      (vat :: vat :: yankMoveOutSize :: yankMoveOutPtr :: yankMoveInSize ::
        yankMoveOutPtr :: yankMoveOutSize :: yankMoveEndPtr :: yankMoveSelectorWord ::
        vat :: lot :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src guy lot memMap) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k' C' := by
  intro id memMap vat src guy lot
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemStart
  have hread64Map :
      memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using twoWordHashMem_read64 id ⟨1⟩ hmemStart hread64Start
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem :
      (yankMoveCalldataMem src guy lot memMap).size = 228 :=
    yankMoveCalldataMem_size src guy lot hmemMap
  have hcallRead64 :
      (yankMoveCalldataMem src guy lot memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    yankMoveCalldataMem_read64 src guy lot hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankMoveCalldataMem src guy lot memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankMoveCalldataMem src guy lot memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd3606pre := evm_run rd3601 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3606 := rd3606pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3613pre := evm_run rd3606 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3613 := rd3613pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3618pre := evm_run rd3613 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd3618 := rd3618pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd3621pre := evm_run rd3618 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd3621pre
  obtain ⟨k3623, C3623, rd3623raw⟩ := rd3621pre.sload (by native_decide) (by evm_ov)
  have rd3623 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3623⟩
      (lot :: ⟨64⟩ :: base :: ⟨0⟩ :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3623 C3623 := by
    simpa [lot, flapperSlotWord] using rd3623raw
  have rd3626pre := evm_run rd3623 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k3627, C3627, rd3627raw⟩ := rd3626pre.sload (by native_decide) (by evm_ov)
  have rd3627 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3627⟩
      (flapperSlotWord ⟨2⟩ σ I :: ⟨2⟩ :: lot :: ⟨64⟩ :: base ::
        ⟨0⟩ :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3627 C3627 := by
    simpa [flapperSlotWord] using rd3627raw
  have rd3629pre := evm_run rd3627 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : base + ⟨2⟩ = auctionPackedSlot id := by
    simp [base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd3629pre
  obtain ⟨k3630, C3630, rd3630raw⟩ := rd3629pre.sload (by native_decide) (by evm_ov)
  have rd3630 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3630⟩
      (flapperSlotWord (auctionPackedSlot id) σ I :: lot :: ⟨64⟩ ::
        flapperSlotWord ⟨2⟩ σ I :: ⟨0⟩ :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3630 C3630 := by
    simpa [flapperSlotWord] using rd3630raw
  have rd3699 := evm_run rd3630 with [
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
      (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveGuyMem src guy memMap) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [yankMoveGuyMem, guy, flapperAddressReturnWord,
          u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveCalldataMem src guy lot memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 yankMoveInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc3699 :
      (⟨3630⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨3699⟩ := by
    native_decide
  rw [hpc3699] at rd3699
  exact ⟨_, _, by
    simpa [id, memMap, vat, src, guy, lot, dealVatWord, yankThisWord,
      yankMoveSelectorMem, yankMoveSrcMem, yankMoveGuyMem, yankMoveCalldataMem,
      yankMoveSelectorShifted, yankMoveOutPtr, yankMoveOutSize, yankMoveInSize,
      yankMoveEndPtr, flapperAddressReturnWord, flapperSlotWord, solcAddrMask,
      u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + yankMoveInSize =
        yankMoveInSize from by native_decide,
      show (⟨128⟩ : UInt256) + yankMoveInSize = yankMoveEndPtr from by native_decide,
      show yankMoveInSize + yankMoveOutPtr = yankMoveEndPtr from by native_decide]
      using rd3699⟩

theorem flapperDealX_moveNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨2⟩ σ I) =
        ⟨0⟩)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨memStart, _, _, hmemStart, hread64Start, rd3601⟩ :=
    flapperDealX_readyToMove (g := g) htic hfinished rd3408
  obtain ⟨_, _, rd3699⟩ :=
    flapperDealX_toMoveExtcodesizeGuard hmemStart hread64Start rd3601
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3699⟩) (okPc := ⟨3711⟩) rd3699
    hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flapperDealX_moveCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let vat := flapperAddressReturnWord ⟨2⟩ σ I
    let src := yankThisWord I
    let guy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let lot := flapperSlotWord (auctionLotSlot id) σ I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (memCall : ByteArray) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          vat :: lot :: id :: ⟨360⟩ :: sel :: [])
        memCall (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ memCall.size = 228
    ∧ memCall.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
        [.address I.codeOwner, .address (AccountAddress.ofNat guy.toNat),
          .int (Int.ofNat lot.toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro id vat src guy lot
  obtain ⟨memStart, _, _, hmemStart, hread64Start, rd3601⟩ :=
    flapperDealX_readyToMove (g := g) htic hfinished rd3408
  let memMap := twoWordHashMem id ⟨1⟩ memStart
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemStart
  have hread64Map :
      memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using twoWordHashMem_read64 id ⟨1⟩ hmemStart hread64Start
  have hcallMem :
      (yankMoveCalldataMem src guy lot memMap).size = 228 :=
    yankMoveCalldataMem_size src guy lot hmemMap
  have hcallRead64 :
      (yankMoveCalldataMem src guy lot memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    yankMoveCalldataMem_read64 src guy lot hmemMap hread64Map
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
  obtain ⟨_, _, rd3699⟩ :=
    flapperDealX_toMoveExtcodesizeGuard hmemStart hread64Start rd3601
  obtain ⟨gasWord, _, _, rd3714⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3699⟩) (okPc := ⟨3711⟩) rd3699
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k3715, C3715, hΘpack, rd3715raw,
      houtsz⟩ :=
    RD.call rd3714 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', yankMoveCalldataMem src guy lot memMap, k3715, C3715,
    ?_, hcallMem, hcallRead64, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          yankMoveOutPtr.toNat yankMoveInSize.toNat)
          yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
      native_decide
    have hmin : (min yankMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold yankMoveOutSize
      rfl
    have rd3715 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          vat :: lot :: id :: ⟨360⟩ :: sel :: [])
        (out.write 0 (yankMoveCalldataMem src guy lot memMap) yankMoveOutPtr.toNat
          (min yankMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k3715 C3715 :=
      haw ▸ rd3715raw
    rw [hmin, byteArray_write_len_zero] at rd3715
    exact rd3715
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := vat)
      (mem := yankMoveCalldataMem src guy lot memMap)
      (inOff := yankMoveOutPtr) (inSize := yankMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flapperAddressWord_address_eq_target
      ?_ ?_
    · simpa [hsrcAddr] using yankMoveEncode_eq src guy lot hmemMap hsrcCanon hguyCanon
    · simpa [initState, hperm] using hΘ

theorem flapperDealX_moveCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth = 1024)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3408 : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3408⟩
      [dealIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let vat := flapperAddressReturnWord ⟨2⟩ σ I
    let src := yankThisWord I
    let guy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let lot := flapperSlotWord (auctionLotSlot id) σ I
    ∃ memCall k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        vat :: lot :: id :: ⟨360⟩ :: sel :: [])
      memCall (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  intro id vat src guy lot
  obtain ⟨memStart, _, _, hmemStart, hread64Start, rd3601⟩ :=
    flapperDealX_readyToMove (g := g) htic hfinished rd3408
  let memMap := twoWordHashMem id ⟨1⟩ memStart
  obtain ⟨_, _, rd3699⟩ :=
    flapperDealX_toMoveExtcodesizeGuard hmemStart hread64Start rd3601
  obtain ⟨gasWord, _, _, rd3714⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3699⟩) (okPc := ⟨3711⟩) rd3699
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k3715, C3715, rd3715raw⟩ :=
    RD.callDepthLimit rd3714 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨yankMoveCalldataMem src guy lot memMap, k3715, C3715, ?_⟩
  have hmin : (min yankMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold yankMoveOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        yankMoveOutPtr.toNat yankMoveInSize.toNat)
        yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
    native_decide
  simpa [id, memMap, vat, src, guy, lot, yankMoveOutPtr, yankMoveInSize,
    yankMoveOutSize, hmin, byteArray_write_len_zero, haw] using rd3715raw

theorem flapperDealX_moveCallFailure
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (rd3715 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ I :: flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3715⟩) (okPc := ⟨3731⟩) rd3715
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperDealX_toBurnExtcodesizeGuard
    {cA cA' gh bl σ σ₀ σ' A I} {g : Sat256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd3715 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    let id := dealIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ mem
    let lot := flapperSlotWord (auctionLotSlot id) σ I
    let gem := flapperAddressReturnWord ⟨3⟩ σ' I
    let src := yankThisWord I
    let bid := flapperSlotWord (auctionBidSlot id) σ' I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3816⟩
      (gem :: gem :: dealBurnOutSize :: dealBurnOutPtr :: dealBurnInSize ::
        dealBurnOutPtr :: dealBurnOutSize :: dealBurnEndPtr ::
        dealBurnSelectorWord :: gem :: lot :: id :: ⟨360⟩ :: sel :: [])
      (dealBurnCalldataMem src bid memMap) (UInt256.ofNat 8) out (cA', σ') k' C' := by
  intro id memMap lot gem src bid
  let memKey := wordAt0Mem id mem
  let base := solcMappingSlot ⟨1⟩ id
  let gemSlot := flapperSlotWord ⟨3⟩ σ' I
  have hmemKey : memKey.size = 228 := by
    calc
      memKey.size = mem.size := by
        simpa [memKey] using deal_wordAt0Mem_size_of_ge32 id (by rw [hmem]; omega)
      _ = 228 := hmem
  have hmemMap : memMap.size = 228 := by
    calc
      memMap.size = mem.size := by
        simpa [memMap, id] using deal_twoWordHashMem_size_of_ge64 id ⟨1⟩
          (by rw [hmem]; omega)
      _ = 228 := hmem
  have hread64Map :
      memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using
      deal_twoWordHashMem_read64_of_ge96 id ⟨1⟩ (by rw [hmem]; omega) hread64
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem :
      (dealBurnCalldataMem src bid memMap).size = 228 :=
    dealBurnCalldataMem_size_228 src bid hmemMap
  have hcallRead64 :
      (dealBurnCalldataMem src bid memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dealBurnCalldataMem_read64_228 src bid hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (dealBurnCalldataMem src bid memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dealBurnCalldataMem src bid memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  obtain ⟨k3733, C3733, rd3733raw⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3715⟩) (okPc := ⟨3731⟩) rd3715
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3733 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3733⟩
      (yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ I :: lot :: id :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k3733 C3733 := by
    simpa [id, lot,
      show ((⟨3731⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨3733⟩ from by native_decide]
      using rd3733raw
  have rd3736pre := evm_run rd3733 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3737, C3737, rd3737raw⟩ := rd3736pre.sload
    (by native_decide) (by evm_ov)
  have rd3737 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3737⟩
      (gemSlot :: yankMoveSelectorWord :: flapperAddressReturnWord ⟨2⟩ σ I ::
        lot :: id :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k3737 C3737 := by
    simpa [gemSlot, flapperSlotWord] using rd3737raw
  have rd3741pre := evm_run rd3737 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3742 := rd3741pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3746pre := evm_run rd3742 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3747 := rd3746pre.mstore 0 memMap (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3751pre := evm_run rd3747 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd3752pre := rd3751pre.keccak256 0 base (UInt256.ofNat 8)
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
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd3752pre
  obtain ⟨k3753, C3753, rd3753raw⟩ := rd3752pre.sload
    (by native_decide) (by evm_ov)
  have rd3753 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3753⟩
      (bid :: ⟨64⟩ :: ⟨0⟩ :: gemSlot :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ I :: lot :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 8) out (cA', σ') k3753 C3753 := by
    simpa [bid, flapperSlotWord] using rd3753raw
  have hselShift :
      UInt256.shiftLeft (⟨0x2770a7eb⟩ : UInt256) ⟨226⟩ =
        dealBurnSelectorShifted := by
    native_decide
  have rd3816 := evm_run rd3753 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 ⟨0x2770a7eb⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (dealBurnSelectorMem memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
        simp [dealBurnSelectorMem, hselShift])
      (by native_decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (dealBurnSrcMem src memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simp [dealBurnSrcMem, src, yankThisWord,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 0 (dealBurnCalldataMem src bid memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push4 dealBurnSelectorWord (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 dealBurnInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc3816 :
      (⟨3753⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨3816⟩ := by
    native_decide
  rw [hpc3816] at rd3816
  exact ⟨_, _, by
    simpa [id, memMap, lot, gem, src, bid, gemSlot, dealBurnSelectorMem,
      dealBurnSrcMem, dealBurnCalldataMem, dealBurnSelectorShifted,
      dealBurnOutPtr, dealBurnOutSize, dealBurnInSize, dealBurnEndPtr,
      flapperAddressReturnWord, flapperSlotWord, solcAddrMask, u256_land_comm,
      hselShift,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + dealBurnInSize = dealBurnEndPtr from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + dealBurnInSize =
        dealBurnInSize from by native_decide,
      show dealBurnInSize + dealBurnOutPtr = dealBurnEndPtr from by native_decide]
      using rd3816⟩

theorem flapperDealX_burnNoCode
    {cA cA' gh bl σ σ₀ σ' A I} {g : Sat256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ' (flapperAddressReturnWord ⟨3⟩ σ' I) =
        ⟨0⟩)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd3715 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3816⟩ :=
    flapperDealX_toBurnExtcodesizeGuard hmem hread64 rd3715
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3816⟩) (okPc := ⟨3828⟩)
    rd3816 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flapperDealX_burnCall
    {cA cA' gh bl σ σ₀ σ' A A1 I} {g : Sat256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (flapperAddressReturnWord ⟨3⟩ σ' I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd3715 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    let id := dealIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ mem
    let lot := flapperSlotWord (auctionLotSlot id) σ I
    let gem := flapperAddressReturnWord ⟨3⟩ σ' I
    let src := yankThisWord I
    let bid := flapperSlotWord (auctionBidSlot id) σ' I
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (outBurn : ByteArray) (A'' : Substate) (memCall : ByteArray) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3832⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dealBurnEndPtr :: dealBurnSelectorWord ::
          gem :: lot :: id :: ⟨360⟩ :: sel :: [])
        memCall (UInt256.ofNat 8) outBurn (cA'', σ'') k' C'
    ∧ memCall.size = 228
    ∧ memCall.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
    ∧ typedCallViaEVM config
        ({ initState cA gh bl σ σ₀ g A I with
            accountMap := σ', substate := A1, createdAccounts := cA' })
        (EVM.address (AccountAddress.ofNat gem.toNat)) "burn" 0
        [.address I.codeOwner, .int (Int.ofNat bid.toNat)]
        (z,
          { { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A1, createdAccounts := cA' } with
              accountMap := σ'', substate := A'', createdAccounts := cA'' },
          outBurn) true
    ∧ outBurn.size < UInt256.size := by
  intro id memMap lot gem src bid
  have hmemMap : memMap.size = 228 := by
    calc
      memMap.size = mem.size := by
        simpa [memMap, id] using deal_twoWordHashMem_size_of_ge64 id ⟨1⟩
          (by rw [hmem]; omega)
      _ = 228 := hmem
  have hread64Map :
      memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using
      deal_twoWordHashMem_read64_of_ge96 id ⟨1⟩ (by rw [hmem]; omega) hread64
  have hcallMem :
      (dealBurnCalldataMem src bid memMap).size = 228 :=
    dealBurnCalldataMem_size_228 src bid hmemMap
  have hcallRead64 :
      (dealBurnCalldataMem src bid memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dealBurnCalldataMem_read64_228 src bid hmemMap hread64Map
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [show src = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  have hsrcAddr : AccountAddress.ofNat src.toNat = I.codeOwner := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [src, yankThisWord] using accountAddress_roundtrip I.codeOwner
  obtain ⟨_, _, rd3816⟩ :=
    flapperDealX_toBurnExtcodesizeGuard hmem hread64 rd3715
  obtain ⟨gasWord, _, _, rd3831⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3816⟩) (okPc := ⟨3828⟩) rd3816
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA'', σ'', z, outBurn, A_in, callGas, k3832, C3832, hΘpack, rd3832raw,
      houtsz⟩ :=
    RD.call rd3831 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A'', hΘ⟩ := hΘpack
  refine ⟨cA'', σ'', z, outBurn, A'', dealBurnCalldataMem src bid memMap,
    k3832, C3832, ?_, hcallMem, hcallRead64, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          dealBurnOutPtr.toNat dealBurnInSize.toNat)
          dealBurnOutPtr.toNat dealBurnOutSize.toNat) = UInt256.ofNat 8 := by
      unfold dealBurnOutPtr dealBurnInSize dealBurnOutSize
      native_decide
    have hmin : (min dealBurnOutSize (UInt256.ofNat outBurn.size)).toNat = 0 := by
      unfold dealBurnOutSize
      rfl
    have rd3832 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3832⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dealBurnEndPtr :: dealBurnSelectorWord ::
          gem :: lot :: id :: ⟨360⟩ :: sel :: [])
        (outBurn.write 0 (dealBurnCalldataMem src bid memMap) dealBurnOutPtr.toNat
          (min dealBurnOutSize (UInt256.ofNat outBurn.size)).toNat)
        (UInt256.ofNat 8) outBurn (cA'', σ'') k3832 C3832 :=
      haw ▸ rd3832raw
    rw [hmin, byteArray_write_len_zero] at rd3832
    exact rd3832
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gem)
      (mem := dealBurnCalldataMem src bid memMap)
      (inOff := dealBurnOutPtr) (inSize := dealBurnInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flapperAddressWord_address_eq_target
      ?_ ?_
    · simpa [hsrcAddr] using dealBurnEncode_eq_228 src bid hmemMap hsrcCanon
    · simpa [initState, hperm] using hΘ

theorem flapperDealX_burnCallFailure
    {cA cA' gh bl σ σ₀ σMove σ' A I} {g : Sat256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (rd3832 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3832⟩
      (⟨0⟩ :: dealBurnEndPtr :: dealBurnSelectorWord ::
        flapperAddressReturnWord ⟨3⟩ σMove I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3832⟩) (okPc := ⟨3848⟩) rd3832
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperDealX_deleteToFillSub
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {drop0 drop1 gem lot id sel : UInt256}
    {mem out : ByteArray}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g s0 ⟨3850⟩
      (drop0 :: drop1 :: gem :: lot :: id :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    let memMap := twoWordHashMem id ⟨1⟩ mem
    let σDel := auctionRuntimeDeleteAccountMap I.codeOwner id σ
    ∃ k' C', RD flapperBytecode I g s0 ⟨4963⟩
      (lot :: flapperSlotWord ⟨9⟩ σDel I :: ⟨3894⟩ ::
        lot :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 8) out (cA, σDel) k' C' := by
  intro memMap σDel
  let memKey := wordAt0Mem id mem
  let base := solcMappingSlot ⟨1⟩ id
  let σBid := sstoreAccountMap I.codeOwner σ (auctionBidSlot id) ⟨0⟩
  let σLot := sstoreAccountMap I.codeOwner σBid (auctionLotSlot id) ⟨0⟩
  have rd3856pre := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3857 := rd3856pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3863pre := evm_run rd3857 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3864 := rd3863pre.mstore 0 memMap (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3867pre := evm_run rd3864 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap] using twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd3868raw := rd3867pre.keccak256 0 base (UInt256.ofNat 8)
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
  have rd3870pre := evm_run rd3868raw with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  obtain ⟨k3871, C3871, rd3871raw⟩ := rd3870pre.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3871 : RD flapperBytecode I g s0 ⟨3871⟩
      (base :: ⟨1⟩ :: ⟨0⟩ :: gem :: lot :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 8) out (cA, σBid) k3871 C3871 := by
    simpa [σBid, base, auctionBidSlot, auctionBaseSlot_eq,
      show ((⟨3850⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        ⟨3871⟩ from by native_decide]
      using rd3871raw
  have rd3876pre := evm_run rd3871 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k3877, C3877, rd3877raw⟩ := rd3876pre.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq]
  have rd3877 : RD flapperBytecode I g s0 ⟨3877⟩
      (base :: ⟨0⟩ :: gem :: lot :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 8) out (cA, σLot) k3877 C3877 := by
    simpa [σLot, hlotSlot,
      show ((⟨3871⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        ⟨3877⟩ from by native_decide]
      using rd3877raw
  have rd3880pre := evm_run rd3877 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3881, C3881, rd3881raw⟩ := rd3880pre.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hpackedSlot : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq]
  have rd3881 : RD flapperBytecode I g s0 ⟨3881⟩
      (gem :: lot :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 8) out (cA, σDel) k3881 C3881 := by
    simpa [σDel, auctionRuntimeDeleteAccountMap, σLot, σBid, hpackedSlot,
      show ((⟨3877⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        ⟨3881⟩ from by native_decide]
      using rd3881raw
  have rd3884pre := evm_run rd3881 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3885, C3885, rd3885raw⟩ := rd3884pre.sload
    (by native_decide) (by evm_ov)
  have rd3885 : RD flapperBytecode I g s0 ⟨3885⟩
      (flapperSlotWord ⟨9⟩ σDel I :: lot :: id :: ⟨360⟩ :: sel :: [])
      memMap (UInt256.ofNat 8) out (cA, σDel) k3885 C3885 := by
    simpa [flapperSlotWord] using rd3885raw
  have rd3893pre := evm_run rd3885 with [
    raw push2 ⟨3894⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨4963⟩ (by native_decide) (by evm_ov)]
  have rd4963raw := rd3893pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa using rd4963raw⟩

theorem flapperDealX_burnCallSuccessFill
    {cA cA' gh bl σ σ₀ σMove σBurn A I} {g : Sat256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hfillLe :
      (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I).toNat ≤
        (flapperSlotWord ⟨9⟩
          (auctionRuntimeDeleteAccountMap I.codeOwner (dealIdWord I) σBurn) I).toNat)
    (rd3832 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3832⟩
      (⟨1⟩ :: dealBurnEndPtr :: dealBurnSelectorWord ::
        flapperAddressReturnWord ⟨3⟩ σMove I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σBurn) k C) :
    let id := dealIdWord I
    let lot := flapperSlotWord (auctionLotSlot id) σ I
    let σDel := auctionRuntimeDeleteAccountMap I.codeOwner id σBurn
    let fill := flapperSlotWord ⟨9⟩ σDel I
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner σDel ⟨9⟩ (UInt256.sub fill lot))
      ByteArray.empty := by
  intro id lot σDel fill
  obtain ⟨k3850, C3850, rd3850raw⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3832⟩) (okPc := ⟨3848⟩) rd3832
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3850 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3850⟩
      (dealBurnEndPtr :: dealBurnSelectorWord :: flapperAddressReturnWord ⟨3⟩ σMove I ::
        lot :: id :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σBurn) k3850 C3850 := by
    simpa [id, lot,
      show ((⟨3848⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨3850⟩ from by native_decide]
      using rd3850raw
  obtain ⟨_, _, rd4963⟩ :=
    flapperDealX_deleteToFillSub (I := I) hperm rd3850
  obtain ⟨_, _, rd3894⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨4963⟩) (okPc := ⟨4930⟩)
    (a := fill) (b := lot) (ret := ⟨3894⟩)
    (R := [lot, id, ⟨360⟩, sel])
    rd4963
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [id, lot, σDel, fill] using hfillLe)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3897pre := evm_run rd3894 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3898, C3898, rd3898raw⟩ := rd3897pre.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3898 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3898⟩
      (lot :: id :: ⟨360⟩ :: sel :: [])
      (twoWordHashMem id ⟨1⟩ mem) (UInt256.ofNat 8) out
      (cA', sstoreAccountMap I.codeOwner σDel ⟨9⟩ (UInt256.sub fill lot))
      k3898 C3898 := by
    simpa [id, lot, σDel, fill,
      show ((⟨3894⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        ⟨3898⟩ from by native_decide]
      using rd3898raw
  have rd3900 := evm_run rd3898 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd360 := rd3900.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd361 := rd360.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd361 (by native_decide) (by evm_ov)

theorem flapperDealX_fillSubUnderflow
    {cA cA' gh bl σ σ₀ σMove σBurn A I} {g : Sat256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hlt :
      (flapperSlotWord ⟨9⟩
        (auctionRuntimeDeleteAccountMap I.codeOwner (dealIdWord I) σBurn) I).toNat <
        (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I).toNat)
    (rd3832 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3832⟩
      (⟨1⟩ :: dealBurnEndPtr :: dealBurnSelectorWord ::
        flapperAddressReturnWord ⟨3⟩ σMove I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σBurn) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := dealIdWord I
  let lot := flapperSlotWord (auctionLotSlot id) σ I
  let σDel := auctionRuntimeDeleteAccountMap I.codeOwner id σBurn
  let fill := flapperSlotWord ⟨9⟩ σDel I
  obtain ⟨k3850, C3850, rd3850raw⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3832⟩) (okPc := ⟨3848⟩) rd3832
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3850 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3850⟩
      (dealBurnEndPtr :: dealBurnSelectorWord :: flapperAddressReturnWord ⟨3⟩ σMove I ::
        lot :: id :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σBurn) k3850 C3850 := by
    simpa [id, lot,
      show ((⟨3848⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨3850⟩ from by native_decide]
      using rd3850raw
  obtain ⟨_, _, rd4963⟩ :=
    flapperDealX_deleteToFillSub (I := I) hperm rd3850
  have rd4969pre := evm_run rd4963 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4970pre := rd4969pre.gt (by native_decide) (by evm_ov)
  have hsubNat : (UInt256.sub fill lot).toNat = UInt256.size + fill.toNat - lot.toNat :=
    usub_toNat_underflow (by simpa [id, lot, σDel, fill] using hlt)
  have hgt : UInt256.gt (UInt256.sub fill lot) fill = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub fill lot > fill)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub fill lot).toNat > fill.toNat
      rw [hsubNat]
      have hlotLt : lot.toNat < UInt256.size := lot.val.isLt
      omega
  rw [hgt] at rd4970pre
  have rd4971pre := rd4970pre.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4971pre
  have rd4974 := rd4971pre.push2 ⟨4930⟩ (by native_decide) (by evm_ov)
  have rd4975 := rd4974.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rd4975
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem dealUint48Offset20Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperUint48Offset20Word slot σ I = flapperUint48Offset20Word slot τ I := by
  simp [flapperUint48Offset20Word, flapperSlotWord_accountMapEquiv hAccounts slot]

theorem dealUint48Offset26Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperUint48Offset26Word slot σ I = flapperUint48Offset26Word slot τ I := by
  simp [flapperUint48Offset26Word, flapperSlotWord_accountMapEquiv hAccounts slot]

theorem flapperDealBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I ≠ ⟨1⟩ := by
    intro hone
    exact hlive (by
      have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
      rw [hword, hone])
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperDealBodyReverts_notLive evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
  exact (flapperDealX_notLive (g := Sat256.ofUInt256 g) hlive
      (flapperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperDealBodyCoreTicZero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hticSolm : dealTicWord evmSolm I = ⟨0⟩ := by
    have hword :=
      dealUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (dealIdWord I))
    simpa [evmSolm, initState, dealTicWord] using (hword ▸ htic)
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperDealBodyReverts_ticZero evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        hticSolm
  obtain ⟨_, _, rd3408⟩ :=
    flapperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flapperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flapperDealX_ticZero (g := Sat256.ofUInt256 g) htic ⟨_, _, rd3408⟩)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperDealBodyCoreNotFinished
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat)
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    dealUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    dealUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hticGeSolm : (dealTimestampWord evmSolm).toNat ≤ (dealTicWord evmSolm I).toNat := by
    simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using hticGe
  have hendGeSolm : (dealTimestampWord evmSolm).toNat ≤ (dealEndWord evmSolm I).toNat := by
    simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using hendGe
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperDealBodyReverts_notFinished evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hticGeSolm hendGeSolm
  obtain ⟨_, _, rd3408⟩ :=
    flapperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flapperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flapperDealX_notFinished (g := Sat256.ofUInt256 g) htic hticGe hendGe
      ⟨_, _, rd3408⟩)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperDealBodyCoreMoveNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨2⟩ σ_evm I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    dealUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    dealUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨2⟩ σ_solm I) = ⟨0⟩ :=
    flapperCodeSize_zero_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hnoCode
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperDealBodyReverts_moveNoCode evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hnoCodeSolm)
  obtain ⟨_, _, rd3408⟩ :=
    flapperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flapperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flapperDealX_moveNoCode (g := Sat256.ofUInt256 g) htic hfinished hnoCode
      ⟨_, _, rd3408⟩)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperDealBodyCoreMoveCallFailure
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flapperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (rd3715 : RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3715⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ_evm I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I))
            σ_evm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (houtSize : out.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hpostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hvatEq :
      flapperAddressReturnWord ⟨2⟩ σ_evm I =
        flapperAddressReturnWord ⟨2⟩ σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I =
        flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (dealIdWord I))
  have hlotEq :
      flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I =
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I :=
    flapperSlotWord_accountMapEquiv hAccounts (auctionLotSlot (dealIdWord I))
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I).toNat)]
        (false, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, hvatEq, hguyEq, hlotEq] using hcallSolmRaw
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    dealUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    dealUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, evmCallSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperDealBodyReverts_moveCallFailure evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  exact (flapperDealX_moveCallFailure rd3715 houtSize)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperDealBodyCoreMoveCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := dealIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let vat := flapperAddressReturnWord ⟨2⟩ σ_solm I
  let src := yankThisWord I
  let guy := flapperAddressReturnWord (auctionPackedSlot id) σ_solm I
  let lot := flapperSlotWord (auctionLotSlot id) σ_solm I
  let A_move := (evmSolm.addAccessedAccount (EVM.address (AccountAddress.ofNat vat.toNat))).substate
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using
      twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
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
        (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
        [.address I.codeOwner, .address (AccountAddress.ofNat guy.toNat),
          .int (Int.ofNat lot.toNat)]
        (false, { evmSolm with substate := A_move }, ByteArray.empty) true := by
    simpa [A_move, hsrcAddr] using
      (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
        (tgt := EVM.address (AccountAddress.ofNat vat.toNat)) (name := "move")
        (args := [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat lot.toNat)])
        (callPerm := true)
        (calldata := (yankMoveCalldataMem src guy lot memMap).readWithPadding
          yankMoveOutPtr.toNat yankMoveInSize.toNat)
        (yankMoveEncode_eq src guy lot hmemMap hsrcCanon hguyCanon)
        hdepthInit)
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    dealUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    dealUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, vat, src, guy, lot, id, flapperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flapperDealBodyReverts_moveCallFailure evmSolm
        { evmSolm with substate := A_move } I ByteArray.empty
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  obtain ⟨_, _, rd3408⟩ :=
    flapperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flapperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  obtain ⟨_, _, _, rd3715⟩ :=
    flapperDealX_moveCallDepthLimit (g := Sat256.ofUInt256 g) hcodeSize hdepth htic
      hfinished ⟨_, _, rd3408⟩
  exact (flapperDealX_moveCallFailure rd3715 (by native_decide))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperDealBodyCoreBurnNoCode
    {cA cA' gh bl σ_evm σ_solm σMove σ₀ A AMove I} {g : UInt256} {sel : UInt256}
    {mem outMove : ByteArray} {k C : ℕ}
    (hcode : I.code = flapperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hmoveCodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (rd3715 : RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3715⟩
      (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ_evm I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outMove (cA', σMove) k C)
    (hmoveCall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σMove, substate := AMove, createdAccounts := cA' },
          outMove) true)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σMove
        (flapperAddressReturnWord ⟨3⟩ σMove I) = ⟨0⟩)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σMoveSolm, AMoveSolm, hmoveCallSolmRaw, hpostMoveAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hmoveCall) hAccounts
  let evmMoveSolm : EVM.State :=
    { evmSolm with accountMap := σMoveSolm, substate := AMoveSolm, createdAccounts := cA' }
  have hvatEq :
      flapperAddressReturnWord ⟨2⟩ σ_evm I =
        flapperAddressReturnWord ⟨2⟩ σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I =
        flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (dealIdWord I))
  have hlotEq :
      flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I =
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I :=
    flapperSlotWord_accountMapEquiv hAccounts (auctionLotSlot (dealIdWord I))
  have hmoveCallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I).toNat)]
        (true, evmMoveSolm, outMove) true := by
    simpa [evmSolm, evmMoveSolm, hvatEq, hguyEq, hlotEq] using hmoveCallSolmRaw
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    dealUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    dealUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hmoveCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hmoveCodeSize
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σMoveSolm
        (flapperAddressReturnWord ⟨3⟩ σMoveSolm I) = ⟨0⟩ :=
    flapperCodeSize_zero_accountMapEquiv_addressSlot hpostMoveAccounts ⟨3⟩ hnoCode
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, evmMoveSolm, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperDealBodyReverts_burnNoCode evmSolm evmMoveSolm I outMove
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hmoveCodeSizeSolm)
        hmoveCallSolm
        (by simpa [evmMoveSolm, initState] using hnoCodeSolm)
  exact (flapperDealX_burnNoCode hnoCode hmem hread64 rd3715)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem flapperDealBodyCoreMoveCallSuccess
    {cA cA' gh bl σ_evm σ_solm σMove σ₀ A AMove I} {g : UInt256} {sel : UInt256}
    {memMove outMove : ByteArray} {k C : ℕ}
    (hcode : I.code = flapperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hmoveCodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flapperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd3715 : RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3715⟩
      (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        flapperAddressReturnWord ⟨2⟩ σ_evm I ::
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I ::
        dealIdWord I :: ⟨360⟩ :: sel :: [])
      memMove (UInt256.ofNat 8) outMove (cA', σMove) k C)
    (hmemMove : memMove.size = 228)
    (hread64Move : memMove.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmoveCall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σMove, substate := AMove, createdAccounts := cA' },
          outMove) true)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σMoveSolm, AMoveSolm, hmoveCallSolmRaw, hpostMoveAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hmoveCall) hAccounts
  let evmMoveSolm : EVM.State :=
    { evmSolm with accountMap := σMoveSolm, substate := AMoveSolm, createdAccounts := cA' }
  have hvatEq :
      flapperAddressReturnWord ⟨2⟩ σ_evm I =
        flapperAddressReturnWord ⟨2⟩ σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I =
        flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I :=
    flapperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (dealIdWord I))
  have hlotEq :
      flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I =
        flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I :=
    flapperSlotWord_accountMapEquiv hAccounts (auctionLotSlot (dealIdWord I))
  have hmoveCallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flapperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address I.codeOwner,
        .address (AccountAddress.ofNat
          (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I).toNat)]
        (true, evmMoveSolm, outMove) true := by
    simpa [evmSolm, evmMoveSolm, hvatEq, hguyEq, hlotEq] using hmoveCallSolmRaw
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    dealUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    dealUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hmoveCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flapperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hmoveCodeSize
  by_cases hburnNoCode :
      Reasoning.Theory.extCodeSizeWord σMove
        (flapperAddressReturnWord ⟨3⟩ σMove I) = ⟨0⟩
  · exact flapperDealBodyCoreBurnNoCode hcode _hsize hwv _hsz36 hlive htic hfinished
      hmoveCodeSize rd3715 hmoveCall hburnNoCode hmemMove hread64Move hdispatch hdecode
      hAccounts
  · have hburnCodeSize :
        Reasoning.Theory.extCodeSizeWord σMove
          (flapperAddressReturnWord ⟨3⟩ σMove I) ≠ ⟨0⟩ := hburnNoCode
    obtain ⟨cABurn, σBurn, z, outBurn, ABurn, memBurn, k3832, C3832,
        rd3832, hmemBurn, hread64Burn, hburnCall, houtBurnSize⟩ :=
      flapperDealX_burnCall
        (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (σ' := σMove) (A := A) (A1 := AMoveSolm)
        (I := I) (g := Sat256.ofUInt256 g) (sel := sel) (mem := memMove)
        (out := outMove) (k := k) (C := C)
        hperm hburnCodeSize hdepth hmemMove hread64Move rd3715
    let evmMoveEvmForBurn : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMoveSolm, createdAccounts := cA' }
    obtain ⟨σBurnSolm, ABurnSolm, hburnCallSolmRaw, hpostBurnAccounts⟩ :=
      typedCallViaEVM_accountMapEquiv
        (evm_evm := evmMoveEvmForBurn) (evm_solm := evmMoveSolm)
        (hcall := by simpa [evmMoveEvmForBurn] using hburnCall)
        (by simpa [evmMoveEvmForBurn, evmMoveSolm] using hpostMoveAccounts)
        (by simp [evmMoveEvmForBurn, evmMoveSolm, evmSolm, initState])
        (by simp [evmMoveEvmForBurn, evmMoveSolm, evmSolm, initState])
        (by simp [evmMoveEvmForBurn, evmMoveSolm, evmSolm, initState])
        (by simp [evmMoveEvmForBurn, evmMoveSolm, evmSolm, initState])
        (by simp [evmMoveEvmForBurn, evmMoveSolm, evmSolm, initState])
        (by simp [evmMoveEvmForBurn, evmMoveSolm, evmSolm, initState])
    let evmBurnSolm : EVM.State :=
      { evmMoveSolm with accountMap := σBurnSolm, substate := ABurnSolm, createdAccounts := cABurn }
    have hgemEq :
        flapperAddressReturnWord ⟨3⟩ σMove I =
          flapperAddressReturnWord ⟨3⟩ σMoveSolm I :=
      flapperAddressReturnWord_accountMapEquiv hpostMoveAccounts ⟨3⟩
    have hbidEq :
        flapperSlotWord (auctionBidSlot (dealIdWord I)) σMove I =
          flapperSlotWord (auctionBidSlot (dealIdWord I)) σMoveSolm I :=
      flapperSlotWord_accountMapEquiv hpostMoveAccounts (auctionBidSlot (dealIdWord I))
    have hburnCallSolm :
        typedCallViaEVM config evmMoveSolm
          (EVM.address (AccountAddress.ofNat
            (flapperAddressReturnWord ⟨3⟩ σMoveSolm I).toNat))
          "burn" 0
          [.address I.codeOwner,
            .int (Int.ofNat
              (flapperSlotWord (auctionBidSlot (dealIdWord I)) σMoveSolm I).toNat)]
          (z, evmBurnSolm, outBurn) true := by
      simpa [evmMoveEvmForBurn, evmMoveSolm, evmBurnSolm, hgemEq, hbidEq]
        using hburnCallSolmRaw
    have hburnCodeSizeSolm :
        Reasoning.Theory.extCodeSizeWord σMoveSolm
          (flapperAddressReturnWord ⟨3⟩ σMoveSolm I) ≠ ⟨0⟩ :=
      flapperCodeSize_ne_accountMapEquiv_addressSlot hpostMoveAccounts ⟨3⟩ hburnCodeSize
    by_cases hz : z = true
    · have rd3832True : RD flapperBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
          (⟨1⟩ :: dealBurnEndPtr :: dealBurnSelectorWord ::
            flapperAddressReturnWord ⟨3⟩ σMove I ::
            flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I ::
            dealIdWord I :: ⟨360⟩ :: sel :: [])
          memBurn (UInt256.ofNat 8) outBurn (cABurn, σBurn) k3832 C3832 := by
        simpa [hz] using rd3832
      have hburnCallTrue :
          typedCallViaEVM config evmMoveSolm
            (EVM.address (AccountAddress.ofNat
              (flapperAddressReturnWord ⟨3⟩ σMoveSolm I).toNat))
            "burn" 0
            [.address I.codeOwner,
              .int (Int.ofNat
                (flapperSlotWord (auctionBidSlot (dealIdWord I)) σMoveSolm I).toNat)]
            (true, evmBurnSolm, outBurn) true := by
        simpa [hz] using hburnCallSolm
      let id := dealIdWord I
      let σDel := auctionRuntimeDeleteAccountMap I.codeOwner id σBurn
      let σDelSolm := auctionRuntimeDeleteAccountMap I.codeOwner id σBurnSolm
      let evmDeleteSolm := auctionDeletePostState id evmBurnSolm
      have hRuntimeDeleteEquiv :
          accountMapEquiv σDel σDelSolm := by
        unfold σDel σDelSolm auctionRuntimeDeleteAccountMap
        exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
          (auctionBidSlot id) ⟨0⟩
          (auctionLotSlot id) ⟨0⟩
          (auctionPackedSlot id) ⟨0⟩
          (by simpa [evmBurnSolm] using hpostBurnAccounts)
      have hDeleteSolm :
          accountMapEquiv σDelSolm evmDeleteSolm.accountMap := by
        simpa [σDelSolm, evmDeleteSolm, evmBurnSolm] using
          auctionDeletePostState_accountMapEquiv id evmBurnSolm I.codeOwner
            (by simp [evmBurnSolm, evmMoveSolm, evmSolm, initState])
      have hDeleteAccounts : accountMapEquiv σDel evmDeleteSolm.accountMap :=
        accountMapEquiv.trans hRuntimeDeleteEquiv hDeleteSolm
      have hDeleteEnv : evmDeleteSolm.executionEnv = I := by
        simp [evmDeleteSolm, auctionDeletePostState, auctionDeleteAfterTic,
          auctionDeleteAfterGuy, auctionDeleteAfterLot, auctionDeleteAfterBid,
          evmBurnSolm, evmMoveSolm, evmSolm, initState, storageStore_executionEnv]
      have hlotSource :
          dealLotWord evmSolm I = flapperSlotWord (auctionLotSlot id) σ_evm I := by
        simpa [dealLotWord, evmSolm, initState, id, hlotEq.symm]
      have hfillSource :
          dealFillWord evmDeleteSolm = flapperSlotWord ⟨9⟩ σDel I := by
        have hslot :=
          flapperSlotWord_accountMapEquiv (I := evmDeleteSolm.executionEnv)
            hDeleteAccounts ⟨9⟩
        simpa [dealFillWord, evmDeleteSolm, hDeleteEnv] using hslot.symm
      by_cases hfillLe :
          (flapperSlotWord (auctionLotSlot id) σ_evm I).toNat ≤
            (flapperSlotWord ⟨9⟩ σDel I).toNat
      · have hfillLeSolm :
            (dealLotWord evmSolm I).toNat ≤ (dealFillWord evmDeleteSolm).toNat := by
          simpa [hlotSource, hfillSource] using hfillLe
        have hbody :
            ExecTransitionBody config contract evmSolm (dealLocals I)
              dealTransition.body
              (.returned { contract := contract, locals := dealFillNewLocals evmSolm evmDeleteSolm I }
                (Solm.EVM.storageStore evmDeleteSolm
                  evmDeleteSolm.executionEnv.codeOwner ⟨9⟩
                  (UInt256.sub (dealFillWord evmDeleteSolm) (dealLotWord evmSolm I)))
                none) := by
          simpa [evmSolm, evmMoveSolm, evmBurnSolm, evmDeleteSolm, flapperSlotWord,
            initState, Solm.EVM.storageLoad, State.lookupAccount] using
            flapperDealBodyReturns_success evmSolm evmMoveSolm evmBurnSolm I outMove outBurn
              (by simp only [evmSolm, initState]; exact hwv)
              hliveSolmWord hticSolm hfinishedSolm
              (by simpa [evmSolm, initState] using hmoveCodeSizeSolm)
              hmoveCallSolm
              (by simpa [evmMoveSolm, initState] using hburnCodeSizeSolm)
              hburnCallTrue
              hfillLeSolm
        have hret :=
          flapperDealX_burnCallSuccessFill
            (g := Sat256.ofUInt256 g) (σ := σ_evm) (σMove := σMove)
            (σBurn := σBurn) (sel := sel) hperm hfillLe rd3832True
        let fillRuntime := flapperSlotWord ⟨9⟩ σDel I
        let lotRuntime := flapperSlotWord (auctionLotSlot id) σ_evm I
        let diffRuntime := UInt256.sub fillRuntime lotRuntime
        let diffSource := UInt256.sub (dealFillWord evmDeleteSolm) (dealLotWord evmSolm I)
        have hdiff : diffRuntime = diffSource := by
          simp [diffRuntime, diffSource, fillRuntime, lotRuntime, hfillSource, hlotSource]
        have hFinalAccounts :
            accountMapEquiv (sstoreAccountMap I.codeOwner σDel ⟨9⟩ diffRuntime)
              (Solm.EVM.storageStore evmDeleteSolm evmDeleteSolm.executionEnv.codeOwner
                ⟨9⟩ diffSource).accountMap := by
          have hDeleteOwner : evmDeleteSolm.executionEnv.codeOwner = I.codeOwner := by
            simp [hDeleteEnv]
          simpa [storageStore_accountMap, evmDeleteSolm, hdiff, hDeleteOwner] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩ diffRuntime hDeleteAccounts
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          (by
            simp [evmDeleteSolm, auctionDeletePostState, auctionDeleteAfterTic,
              auctionDeleteAfterGuy, auctionDeleteAfterLot, auctionDeleteAfterBid,
              evmBurnSolm, evmMoveSolm, evmSolm, initState, storageStore_createdAccounts])
          (by
            simpa [id, σDel, fillRuntime, lotRuntime, diffRuntime] using hFinalAccounts)
          (by
            simpa [dealTransition] using
              (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                (dvs := []) rfl (by native_decide) (by native_decide)))
      · have hfillLt :
            (flapperSlotWord ⟨9⟩ σDel I).toNat <
              (flapperSlotWord (auctionLotSlot id) σ_evm I).toNat :=
          Nat.lt_of_not_ge hfillLe
        have hfillLtSolm :
            (dealFillWord evmDeleteSolm).toNat < (dealLotWord evmSolm I).toNat := by
          simpa [hlotSource, hfillSource] using hfillLt
        have hbody :
            ExecTransitionBody config contract evmSolm (dealLocals I)
              dealTransition.body .reverted := by
          simpa [evmSolm, evmMoveSolm, evmBurnSolm, evmDeleteSolm, flapperSlotWord,
            initState, Solm.EVM.storageLoad, State.lookupAccount] using
            flapperDealBodyReverts_fillSubUnderflow evmSolm evmMoveSolm evmBurnSolm I
              outMove outBurn
              (by simp only [evmSolm, initState]; exact hwv)
              hliveSolmWord hticSolm hfinishedSolm
              (by simpa [evmSolm, initState] using hmoveCodeSizeSolm)
              hmoveCallSolm
              (by simpa [evmMoveSolm, initState] using hburnCodeSizeSolm)
              hburnCallTrue
              hfillLtSolm
        exact (flapperDealX_fillSubUnderflow
            (g := Sat256.ofUInt256 g) (σ := σ_evm) (σMove := σMove)
            (σBurn := σBurn) (sel := sel) hperm hfillLt rd3832True)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hzFalse : z = false := by
        cases z <;> simp at hz ⊢
      have rd3832False : RD flapperBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
          (⟨0⟩ :: dealBurnEndPtr :: dealBurnSelectorWord ::
            flapperAddressReturnWord ⟨3⟩ σMove I ::
            flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I ::
            dealIdWord I :: ⟨360⟩ :: sel :: [])
          memBurn (UInt256.ofNat 8) outBurn (cABurn, σBurn) k3832 C3832 := by
        simpa [hzFalse] using rd3832
      have hburnCallFalse :
          typedCallViaEVM config evmMoveSolm
            (EVM.address (AccountAddress.ofNat
              (flapperAddressReturnWord ⟨3⟩ σMoveSolm I).toNat))
            "burn" 0
            [.address I.codeOwner,
              .int (Int.ofNat
                (flapperSlotWord (auctionBidSlot (dealIdWord I)) σMoveSolm I).toNat)]
            (false, evmBurnSolm, outBurn) true := by
        simpa [hzFalse] using hburnCallSolm
      have hbody :
          ExecTransitionBody config contract evmSolm (dealLocals I)
            dealTransition.body .reverted := by
        simpa [evmSolm, evmMoveSolm, evmBurnSolm, flapperSlotWord, initState,
          Solm.EVM.storageLoad, State.lookupAccount] using
          flapperDealBodyReverts_burnCallFailure evmSolm evmMoveSolm evmBurnSolm I
            outMove outBurn
            (by simp only [evmSolm, initState]; exact hwv)
            hliveSolmWord hticSolm hfinishedSolm
            (by simpa [evmSolm, initState] using hmoveCodeSizeSolm)
            hmoveCallSolm
            (by simpa [evmMoveSolm, initState] using hburnCodeSizeSolm)
            hburnCallFalse
      exact (flapperDealX_burnCallFailure rd3832False houtBurnSize)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperDealBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨767⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperDealX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flapperDecode_deal_none_short hsz4 hshort)

set_option maxHeartbeats 1000000 in
theorem flapperDealBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flapperDispatchDeal hsel
  have hreach := flapperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := flapperDecode_deal_ok (I := I) hsz36
    by_cases hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩
    · by_cases hticZero :
          flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I = ⟨0⟩
      · exact flapperDealBodyCoreTicZero hcode hsize hwv hsz36 hlive hticZero
          hdispatch hdecode hreach hAccounts
      · have htic :
            flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩ :=
          hticZero
        have hfinishedBranch
            (hfinished :
              (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                (UInt256.ofNat I.header.timestamp).toNat ∨
              (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                (UInt256.ofNat I.header.timestamp).toNat) :
            runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
          by_cases hmoveNoCode :
              Reasoning.Theory.extCodeSizeWord σ_evm
                (flapperAddressReturnWord ⟨2⟩ σ_evm I) = ⟨0⟩
          · exact flapperDealBodyCoreMoveNoCode hcode hsize hwv hsz36 hlive htic
              hfinished hmoveNoCode hdispatch hdecode hreach hAccounts
          · have hmoveCodeSize :
                Reasoning.Theory.extCodeSizeWord σ_evm
                  (flapperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩ :=
              hmoveNoCode
            by_cases hdepthEq : I.depth = 1024
            · exact flapperDealBodyCoreMoveCallDepthLimit hcode hsize hwv hsz36 hlive
                htic hfinished hmoveCodeSize hdepthEq hdispatch hdecode hreach hAccounts
            · have hdepthLt : I.depth.val < 1024 := by
                have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                by_contra hn
                have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
                have hval : I.depth.val = 1024 := by omega
                apply hdepthEq
                apply Fin.ext
                exact hval
              obtain ⟨_, _, rd3408⟩ :=
                flapperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
                  (flapperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
              obtain ⟨cA', σMove, z, outMove, AMove, memMove, k3715, C3715,
                  rd3715, hmemMove, hread64Move, hmoveCall, houtMoveSize⟩ :=
                flapperDealX_moveCall (g := Sat256.ofUInt256 g) hperm hmoveCodeSize
                  hdepthLt htic hfinished ⟨_, _, rd3408⟩
              by_cases hz : z = true
              · have rd3715True : RD flapperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3715⟩
                    (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                      flapperAddressReturnWord ⟨2⟩ σ_evm I ::
                      flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I ::
                      dealIdWord I :: ⟨360⟩ :: flapperSelWord I :: [])
                    memMove (UInt256.ofNat 8) outMove (cA', σMove) k3715 C3715 := by
                  simpa [hz] using rd3715
                have hmoveCallTrue :
                    typedCallViaEVM config
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (EVM.address (AccountAddress.ofNat
                        (flapperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                      "move" 0
                      [.address I.codeOwner,
                      .address (AccountAddress.ofNat
                        (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I))
                          σ_evm I).toNat),
                      .int (Int.ofNat
                        (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
                      (true,
                        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                            accountMap := σMove, substate := AMove, createdAccounts := cA' },
                        outMove) true := by
                  simpa [hz] using hmoveCall
                exact flapperDealBodyCoreMoveCallSuccess hcode hsize hperm hwv hsz36
                  hlive htic hfinished hmoveCodeSize hdepthLt rd3715True hmemMove
                  hread64Move hmoveCallTrue hdispatch hdecode hAccounts
              · have hzFalse : z = false := Bool.eq_false_iff.mpr hz
                have rd3715False : RD flapperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3715⟩
                    (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                      flapperAddressReturnWord ⟨2⟩ σ_evm I ::
                      flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I ::
                      dealIdWord I :: ⟨360⟩ :: flapperSelWord I :: [])
                    memMove (UInt256.ofNat 8) outMove (cA', σMove) k3715 C3715 := by
                  simpa [hzFalse] using rd3715
                have hmoveCallFalse :
                    typedCallViaEVM config
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (EVM.address (AccountAddress.ofNat
                        (flapperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                      "move" 0
                      [.address I.codeOwner,
                      .address (AccountAddress.ofNat
                        (flapperAddressReturnWord (auctionPackedSlot (dealIdWord I))
                          σ_evm I).toNat),
                      .int (Int.ofNat
                        (flapperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
                      (false,
                        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                            accountMap := σMove, substate := AMove, createdAccounts := cA' },
                        outMove) true := by
                  simpa [hzFalse] using hmoveCall
                exact flapperDealBodyCoreMoveCallFailure hcode hsize hwv hsz36 hlive
                  htic hfinished hmoveCodeSize rd3715False hmoveCallFalse houtMoveSize
                  hdispatch hdecode hAccounts
        by_cases hticLt :
            (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat
        · exact hfinishedBranch (Or.inl hticLt)
        · have hticGe :
              (UInt256.ofNat I.header.timestamp).toNat ≤
                (flapperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat :=
            Nat.le_of_not_gt hticLt
          by_cases hendLt :
              (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                (UInt256.ofNat I.header.timestamp).toNat
          · exact hfinishedBranch (Or.inr hendLt)
          · have hendGe :
                (UInt256.ofNat I.header.timestamp).toNat ≤
                  (flapperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat :=
              Nat.le_of_not_gt hendLt
            exact flapperDealBodyCoreNotFinished hcode hsize hwv hsz36 hlive htic
              hticGe hendGe hdispatch hdecode hreach hAccounts
    · exact flapperDealBodyCoreNotLive hcode hsize hwv hsz36 hlive
        hdispatch hdecode hreach hAccounts
  · exact flapperDealBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flapper
