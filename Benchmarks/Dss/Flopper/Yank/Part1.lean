import Benchmarks.Dss.Flopper.AuctionCommon
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `yank(uint256)` -/

abbrev yankIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev yankIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (yankIdWord I).toNat)

abbrev yankLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (yankIdValue I)

abbrev yankSuckLocals (I : ExecutionEnv) : Store :=
  (yankLocals I).insert "_suckRet" (collapseReturns [])

theorem yankSuckLocals_get_id (I : ExecutionEnv) :
    (yankSuckLocals I).get? "id" = some (yankIdValue I) := by
  rw [yankSuckLocals, store_get_ne _ _ (by decide)]
  simp [yankLocals]

theorem yankSuckLocals_getElem_id (I : ExecutionEnv) :
    (yankSuckLocals I)["id"]? = some (yankIdValue I) := by
  simpa [Std.HashMap.get?_eq_getElem?] using yankSuckLocals_get_id I

theorem yankSuckLocals_get_bids (I : ExecutionEnv) :
    (yankSuckLocals I).get? "bids" = none := by
  rw [yankSuckLocals, store_get_ne _ _ (by decide)]
  rw [yankLocals, store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem resolveStorageRef_yankSuck_bid (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config { contract := contract, locals := yankSuckLocals I } evm
      (bidRef (.var "id")) =
      .ok ({ base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I))] }, BidStructTy) := by
  exact resolveStorageRef_auction_bid evm (yankSuckLocals I) (yankIdWord I)
    (by simpa [yankIdValue] using yankSuckLocals_get_id I)
    (yankSuckLocals_get_bids I)

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

theorem deleteStorage_yankSuck_bid (evm : EVM.State) (I : ExecutionEnv) :
    deleteStorage? config { contract := contract, locals := yankSuckLocals I } evm
      (bidRef (.var "id")) = .ok (yankDeletePostState evm I) := by
  rw [deleteStorage?]
  rw [resolveStorageRef_yankSuck_bid]
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

abbrev yankVatEvaledRef : EvaledStorageRef :=
  { base := "vat", steps := [] }

abbrev yankVowEvaledRef : EvaledStorageRef :=
  { base := "vow", steps := [] }

abbrev yankGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I)), .field "guy"] }

abbrev yankBidEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (yankIdWord I)), .field "bid"] }

abbrev yankSuckSelectorWord : UInt256 :=
  ⟨0xf24e23eb⟩

abbrev yankSuckSelectorShifted : UInt256 :=
  UInt256.shiftLeft yankSuckSelectorWord ⟨224⟩

abbrev yankSuckOutPtr : UInt256 := ⟨128⟩

abbrev yankSuckInSize : UInt256 := ⟨100⟩

abbrev yankSuckOutSize : UInt256 := ⟨0⟩

abbrev yankSuckEndPtr : UInt256 := ⟨228⟩

noncomputable def yankSuckSelectorMem (mem : ByteArray) : ByteArray :=
  yankSuckSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def yankSuckVowMem (vow : UInt256) (mem : ByteArray) : ByteArray :=
  vow.toByteArray.write 0 (yankSuckSelectorMem mem) 132 32

noncomputable def yankSuckGuyMem (vow guy : UInt256) (mem : ByteArray) : ByteArray :=
  guy.toByteArray.write 0 (yankSuckVowMem vow mem) 164 32

noncomputable def yankSuckCalldataMem (vow guy bid : UInt256) (mem : ByteArray) : ByteArray :=
  bid.toByteArray.write 0 (yankSuckGuyMem vow guy mem) 196 32

theorem yankSuckSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (yankSuckSelectorMem mem).size = 160 := by
  unfold yankSuckSelectorMem
  exact toByteArray_write32_size_of_ge mem yankSuckSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem yankSuckVowMem_size (vow : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (yankSuckVowMem vow mem).size = 164 := by
  unfold yankSuckVowMem
  exact toByteArray_write32_size_of_le (yankSuckSelectorMem mem) vow 132 160 164
    (yankSuckSelectorMem_size hmem)
    (by rw [yankSuckSelectorMem_size hmem]; omega) (by omega)

theorem yankSuckGuyMem_size (vow guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankSuckGuyMem vow guy mem).size = 196 := by
  unfold yankSuckGuyMem
  exact toByteArray_write32_size_of_le (yankSuckVowMem vow mem) guy 164 164 196
    (yankSuckVowMem_size vow hmem)
    (by rw [yankSuckVowMem_size vow hmem]) (by omega)

theorem yankSuckCalldataMem_size (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankSuckCalldataMem vow guy bid mem).size = 228 := by
  unfold yankSuckCalldataMem
  exact toByteArray_write32_size_of_le (yankSuckGuyMem vow guy mem) bid 196 196 228
    (yankSuckGuyMem_size vow guy hmem)
    (by rw [yankSuckGuyMem_size vow guy hmem]) (by omega)

theorem yankSuckSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankSuckSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankSuckSelectorMem
  rw [toByteArray_write_read_below_of_gap yankSuckSelectorShifted mem 128 64
    (by omega) (by native_decide) (by rw [hmem]; native_decide),
    hread64]

theorem yankSuckVowMem_read64 (vow : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankSuckVowMem vow mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankSuckVowMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [yankSuckSelectorMem_size hmem]; omega) (by omega),
    yankSuckSelectorMem_read64 hmem hread64]

theorem yankSuckGuyMem_read64 (vow guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankSuckGuyMem vow guy mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankSuckGuyMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [yankSuckVowMem_size vow hmem]) (by omega),
    yankSuckVowMem_read64 vow hmem hread64]

theorem yankSuckCalldataMem_read64 (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankSuckCalldataMem vow guy bid mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold yankSuckCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [yankSuckGuyMem_size vow guy hmem]) (by omega),
    yankSuckGuyMem_read64 vow guy hmem hread64]

theorem yankSuckCalldataMem_read128_4 (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankSuckCalldataMem vow guy bid mem).readWithPadding 128 4 = suckSelector := by
  have hGuySize := yankSuckGuyMem_size vow guy hmem
  have hVowSize := yankSuckVowMem_size vow hmem
  have hSelectorSize := yankSuckSelectorMem_size hmem
  unfold yankSuckCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankSuckGuyMem vow guy mem) 196 128 4
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankSuckGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (yankSuckVowMem vow mem) 164 128 4
      (by rw [hVowSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hVowSize]; native_decide)]
  unfold yankSuckVowMem
  rw [toByteArray_write_read_below_len_of_gap vow (yankSuckSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold yankSuckSelectorMem
  rw [toByteArray_write_read_window_of_gap yankSuckSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem yankSuckCalldataMem_read132_32 (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankSuckCalldataMem vow guy bid mem).readWithPadding 132 32 = vow.toByteArray := by
  have hGuySize := yankSuckGuyMem_size vow guy hmem
  have hVowSize := yankSuckVowMem_size vow hmem
  have hSelectorSize := yankSuckSelectorMem_size hmem
  unfold yankSuckCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankSuckGuyMem vow guy mem) 196 132 32
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankSuckGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (yankSuckVowMem vow mem) 164 132 32
      (by rw [hVowSize]) (by omega) (by omega) (by omega)
      (by rw [hVowSize]; native_decide)]
  unfold yankSuckVowMem
  rw [toByteArray_write_read_back_of_gap vow (yankSuckSelectorMem mem) 132
    (by rw [hSelectorSize]; native_decide)]

theorem yankSuckCalldataMem_read164_32 (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankSuckCalldataMem vow guy bid mem).readWithPadding 164 32 = guy.toByteArray := by
  have hGuySize := yankSuckGuyMem_size vow guy hmem
  have hVowSize := yankSuckVowMem_size vow hmem
  unfold yankSuckCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankSuckGuyMem vow guy mem) 196 164 32
      (by rw [hGuySize]) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankSuckGuyMem
  rw [toByteArray_write_read_back_of_gap guy (yankSuckVowMem vow mem) 164
    (by rw [hVowSize]; native_decide)]

theorem yankSuckCalldataMem_read196_32 (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankSuckCalldataMem vow guy bid mem).readWithPadding 196 32 = bid.toByteArray := by
  have hGuySize := yankSuckGuyMem_size vow guy hmem
  unfold yankSuckCalldataMem
  rw [toByteArray_write_read_back_of_gap bid (yankSuckGuyMem vow guy mem) 196
    (by rw [hGuySize]; native_decide)]

theorem yankSuckCalldataMem_read128_100 (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (yankSuckCalldataMem vow guy bid mem).readWithPadding 128 100 =
      suckSelector ++ vow.toByteArray ++ guy.toByteArray ++ bid.toByteArray := by
  have hsize : (yankSuckCalldataMem vow guy bid mem).size = 228 :=
    yankSuckCalldataMem_size vow guy bid hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (yankSuckCalldataMem vow guy bid mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (yankSuckCalldataMem vow guy bid mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (yankSuckCalldataMem vow guy bid mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [yankSuckCalldataMem_read128_4 vow guy bid hmem,
    yankSuckCalldataMem_read132_32 vow guy bid hmem,
    yankSuckCalldataMem_read164_32 vow guy bid hmem,
    yankSuckCalldataMem_read196_32 vow guy bid hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem flopperAddressWord_eq_ofNat_address {w : UInt256}
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

theorem flopperAddressWord_address_eq_target {w : UInt256} :
    EVM.address (AccountAddress.ofNat w.toNat) = AccountAddress.ofUInt256 w := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simpa [EVM.twoPow, AccountAddress.size] using
        (AccountAddress.ofNat w.toNat).isLt)

theorem yankSuckEncode_eq (vow guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hvowCanon : vow.toNat < EVM.addressModulus)
    (hguyCanon : guy.toNat < EVM.addressModulus) :
    config.externalABI.encode? "suck"
        [.address (AccountAddress.ofNat vow.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
      some ((yankSuckCalldataMem vow guy bid mem).readWithPadding
        yankSuckOutPtr.toNat yankSuckInSize.toNat) := by
  change config.externalABI.encode? "suck"
      [.address (AccountAddress.ofNat vow.toNat),
        .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
    some ((yankSuckCalldataMem vow guy bid mem).readWithPadding 128 100)
  rw [yankSuckCalldataMem_read128_100 vow guy bid hmem]
  have hbidLt : bid.toNat < EVM.twoPow 256 := bid.val.isLt
  have hbidWord : EVM.word bid.toNat = bid := by
    show UInt256.ofNat bid.toNat = bid
    exact u256_ofNat_toNat _
  have hvowWord := flopperAddressWord_eq_ofNat_address hvowCanon
  have hguyWord := flopperAddressWord_eq_ofNat_address hguyCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, suckSelector, selectorBytes, hbidLt, hbidWord,
    hvowWord, hguyWord, word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem evalExpr_yank_live_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  have hstorage :
      evalExpr? config frame evm (.storage liveRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := liveRef) (er := yankLiveEvaledRef)
      (t := .int uint256Int) (loc := wordLoc ⟨8⟩)
      (value := .int 0)
      (hbase := by simp [frame, liveRef])
      (her := by simp [frame, yankLiveEvaledRef, evalStorageRef, evalStorageRefSteps,
        liveRef, EvalResult.bind, bind, pure])
      (hty := by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using flopperStorageLocLoad_uint256 evm ⟨8⟩)]
  change evalExpr? config frame evm (.binary .eq (.storage liveRef) (.intLit 0)) =
    .ok (.bool true)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_yank_live_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  have hstorage :
      evalExpr? config frame evm (.storage liveRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := liveRef) (er := yankLiveEvaledRef)
      (t := .int uint256Int) (loc := wordLoc ⟨8⟩)
      (value := .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (by simp [frame, liveRef])
      (by simp [frame, yankLiveEvaledRef, evalStorageRef, evalStorageRefSteps,
        liveRef, EvalResult.bind, bind, pure])
      (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
      (by rfl)
      (by exact flopperStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hload (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  change evalExpr? config frame evm (.binary .eq (.storage liveRef) (.intLit 0)) =
    .ok (.bool false)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_yank_guy_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "id") "guy") (er := yankGuyEvaledRef I)
      (t := .address) (loc := addrLoc (auctionPackedSlot (yankIdWord I)))
      (value := .address (AccountAddress.ofNat
        (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
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
        simpa [flopperAddressReturnWord, flopperSlotWord] using
          flopperStorageLocLoad_address_offset0 evm (auctionPackedSlot (yankIdWord I)))
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

theorem flopperAddressOfNat_ne_zero_of_word_ne_zero {w : UInt256}
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
    (hload : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  let guyWord :=
    flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
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
        simpa [guyWord, flopperAddressReturnWord, flopperSlotWord] using
          flopperStorageLocLoad_address_offset0 evm (auctionPackedSlot (yankIdWord I)))
  have hzero :
      evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure, EvalResult.bind, bind]
    unfold castValue? addrSt
    norm_num
    rfl
  have haddrNe : AccountAddress.ofNat guyWord.toNat ≠ AccountAddress.ofNat 0 := by
    exact flopperAddressOfNat_ne_zero_of_word_ne_zero
      (by
        simpa [guyWord, flopperAddressReturnWord] using
          solcAddrMask_result_canonical
            (flopperSlotWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
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

theorem evalExpr_yank_vat_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := vatRef) (er := yankVatEvaledRef)
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (AccountAddress.ofNat
      (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat))
    (by simp [frame, vatRef])
    (by simp [frame, yankVatEvaledRef, evalStorageRef, evalStorageRefSteps,
      vatRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_yank_vow_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (flopperAddressReturnWord ⟨9⟩ evm.accountMap evm.executionEnv).toNat)) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := vowRef) (er := yankVowEvaledRef)
    (t := .address) (loc := addrLoc ⟨9⟩)
    (value := .address (AccountAddress.ofNat
      (flopperAddressReturnWord ⟨9⟩ evm.accountMap evm.executionEnv).toNat))
    (by simp [frame, vowRef])
    (by simp [frame, yankVowEvaledRef, evalStorageRef, evalStorageRefSteps,
      vowRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm ⟨9⟩)

theorem evalExpr_yank_bid_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat
        (flopperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
          evm.executionEnv).toNat)) := by
  let frame : Frame := { contract := contract, locals := yankLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := yankBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (yankIdWord I)))
    (value := .int (Int.ofNat
      (flopperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
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
      simpa [flopperSlotWord] using
        flopperStorageLocLoad_uint256 evm (auctionBidSlot (yankIdWord I)))

theorem evalExprs_yank_suck_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := yankLocals I } evm
        [.storage vowRef, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
      .ok
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨9⟩ evm.accountMap evm.executionEnv).toNat),
        .address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)] := by
  have hguy :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
          (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := { contract := contract, locals := yankLocals I }) (evm := evm)
      (slot := bidsF (.var "id") "guy") (er := yankGuyEvaledRef I)
      (t := .address) (loc := addrLoc (auctionPackedSlot (yankIdWord I)))
      (value := .address (AccountAddress.ofNat
        (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
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
        simpa [flopperAddressReturnWord, flopperSlotWord] using
          flopperStorageLocLoad_address_offset0 evm (auctionPackedSlot (yankIdWord I)))
  simp [evalExprs?, evalExpr_yank_vow_storage, hguy, evalExpr_yank_bid_storage]
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

theorem flopperExtCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap}
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

theorem flopperExtCodeSizeWord_zero_lookup_code_zero {σ : AccountMap}
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

theorem flopperYankBodyReverts_stillLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
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
          checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [.storage vowRef, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_suckRet" ++
          [.delete (bidRef (.var "id"))])
      hwv
      (evalExpr_yank_live_zero_false evm I hlive)

theorem flopperYankBodyReverts_guyNotSet (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [yankTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_live_zero_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_yank_guy_ne_zero_false evm I hguy)))

theorem flopperYankBodyReverts_suckNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body .reverted := by
  have hvat := evalExpr_yank_vat_storage evm I
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap)
        (target := flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv)
        (addr := AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
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

theorem flopperYankBodyReverts_suckCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat))
        "suck" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨9⟩ evm.accountMap evm.executionEnv).toNat),
        .address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)]
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body .reverted := by
  have hvat := evalExpr_yank_vat_storage evm I
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv)
        (addr := AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_yank_suck_args evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [.storage vowRef, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_suckRet")
        .reverted := by
    exact checkedExternalCallFailure hguard hvat hargs hcall
  have htail :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [.storage vowRef, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_suckRet" ++
          [.delete (bidRef (.var "id"))])
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hchecked (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [yankTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_live_zero_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_guy_ne_zero_true evm I hguy)) <|
      htail)

theorem flopperYankBodyReturns_suckCallSuccess
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
        evm.executionEnv ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat))
        "suck" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨9⟩ evm.accountMap evm.executionEnv).toNat),
        .address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionBidSlot (yankIdWord I)) evm.accountMap
            evm.executionEnv).toNat)]
        (true, evm', out) true) :
    ExecTransitionBody config contract evm (yankLocals I) yankTransition.body
      (.returned { contract := contract, locals := yankSuckLocals I }
        (yankDeletePostState evm' I) none) := by
  have hvat := evalExpr_yank_vat_storage evm I
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount
          (AccountAddress.ofNat
            (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv)
        (addr := AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := yankLocals I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true hvat hcodeLookup
  have hargs := evalExprs_yank_suck_args evm I
  have hdec : config.externalABI.decode? "suck" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hchecked :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [.storage vowRef, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_suckRet")
        (.ok { contract := contract, locals := yankSuckLocals I } evm') := by
    simpa [checkedExternalCallStmts, yankSuckLocals] using
      checkedExternalCallSuccess hguard hvat hargs hcall hdec
  have hdelete :
      ExecBlock config { contract := contract, locals := yankSuckLocals I } evm'
        [.delete (bidRef (.var "id"))]
        (.ok { contract := contract, locals := yankSuckLocals I }
          (yankDeletePostState evm' I)) := by
    exact ExecBlock.consNormal (ExecStmt.delete (deleteStorage_yankSuck_bid evm' I))
      ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := yankLocals I } evm
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [.storage vowRef, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_suckRet" ++
          [.delete (bidRef (.var "id"))])
        (.ok { contract := contract, locals := yankSuckLocals I }
          (yankDeletePostState evm' I)) :=
    Reasoning.Refinement.execBlock_append hchecked hdelete
  refine ExecFuncBody.execBlockOK ?_
  simpa [yankTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_live_zero_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_yank_guy_ne_zero_true evm I hguy)) <|
      htail)

theorem flopperDecode_yank_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata =
    some (yankLocals I)
  simpa [config, yankLocals, yankIdValue, yankIdWord, uint256] using
    decodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "id") hsz36

theorem flopperDecode_yank_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata = none
  simpa [config, uint256] using
    decodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "id") hsz4 hshort

theorem flopperReachYankBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 19)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨305⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0x26e027f1⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x26 0xe0 0x27 0xf1 ⟨0x26e027f1⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 0 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc 0))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨305⟩ 0 hfirst
    (fun j hj => flopperLowLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperYankX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨878⟩
      [yankIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨305⟩) (ret := ⟨334⟩)
    (decoded := ⟨327⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd328 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd329 := rd328.pop (by native_decide) (by evm_ov)
  have rd330 := rd329.calldataload (by native_decide) (by evm_ov)
  have rd333 := rd330.push2 ⟨878⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [yankIdWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd333.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flopperYankX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨305⟩) (ret := ⟨334⟩)
    (decoded := ⟨327⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flopperYankX_stillLive {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I ≠ ⟨0⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨878⟩
      [yankIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd878⟩ := h
  have rd881 := evm_run rd878 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k882, C882, rd882raw⟩ := rd881.sload (by native_decide) (by evm_ov)
  have rd882 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨882⟩
      (flopperSlotWord ⟨8⟩ σ I :: yankIdWord I :: ⟨334⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k882 C882 := by
    simpa [flopperSlotWord] using rd882raw
  have rd886 := evm_run rd882 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨952⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (flopperSlotWord ⟨8⟩ σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlive
  have rd887 := rd886.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨887⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x466c6f707065722f7374696c6c2d6c697665⟩)
    (shift := ⟨112⟩)
    (word := ⟨0x466c6f707065722f7374696c6c2d6c6976650000000000000000000000000000⟩)
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
theorem flopperYankX_guyNotSet {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I = ⟨0⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨878⟩
      [yankIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := yankIdWord I
  let mem1 := wordAt0Mem id solcFreePtrMem
  let mem2 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  obtain ⟨_, _, rd878⟩ := h
  have rd881 := evm_run rd878 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k882, C882, rd882raw⟩ := rd881.sload (by native_decide) (by evm_ov)
  have rd882 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨882⟩
      (flopperSlotWord ⟨8⟩ σ I :: yankIdWord I :: ⟨334⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k882 C882 := by
    simpa [flopperSlotWord] using rd882raw
  have rd886 := evm_run rd882 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨952⟩ (by native_decide) (by evm_ov)]
  have hcondLive : UInt256.isZero (flopperSlotWord ⟨8⟩ σ I) ≠ ⟨0⟩ := by
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
  have rd971 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨971⟩
      (flopperSlotWord (auctionPackedSlot (yankIdWord I)) σ I ::
        yankIdWord I :: ⟨334⟩ :: [sel])
      mem2 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k971 C971 := by
    simpa [flopperSlotWord] using rd971raw
  have rd980 := evm_run rd971 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨1050⟩ (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flopperSlotWord (auctionPackedSlot (yankIdWord I)) σ I) =
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  rw [hmask, hguy] at rd980
  have rd984 := rd980.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨984⟩)
    (len := ⟨19⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩)
    (shift := ⟨106⟩)
    (word := ⟨0x466c6f707065722f6775792d6e6f742d73657400000000000000000000000000⟩)
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
theorem flopperYankX_readyToSuck {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I ≠ ⟨0⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨878⟩
      [yankIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1050⟩
      [yankIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := yankIdWord I
  let mem1 := wordAt0Mem id solcFreePtrMem
  let mem2 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  obtain ⟨_, _, rd878⟩ := h
  have rd881 := evm_run rd878 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k882, C882, rd882raw⟩ := rd881.sload (by native_decide) (by evm_ov)
  have rd882 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨882⟩
      (flopperSlotWord ⟨8⟩ σ I :: yankIdWord I :: ⟨334⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k882 C882 := by
    simpa [flopperSlotWord] using rd882raw
  have rd886 := evm_run rd882 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨952⟩ (by native_decide) (by evm_ov)]
  have hcondLive : UInt256.isZero (flopperSlotWord ⟨8⟩ σ I) ≠ ⟨0⟩ := by
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
  have rd971 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨971⟩
      (flopperSlotWord (auctionPackedSlot (yankIdWord I)) σ I ::
        yankIdWord I :: ⟨334⟩ :: [sel])
      mem2 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k971 C971 := by
    simpa [flopperSlotWord] using rd971raw
  have rd980 := evm_run rd971 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨1050⟩ (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flopperSlotWord (auctionPackedSlot (yankIdWord I)) σ I) =
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  rw [hmask] at rd980
  exact ⟨_, _, rd980.jumpiT (by native_decide) hguy (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperYankX_toSuckExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1050 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1050⟩
      [yankIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := yankIdWord I
    let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memMap := twoWordHashMem id ⟨1⟩ memHash
    let vat := flopperAddressReturnWord ⟨2⟩ σ I
    let vow := flopperAddressReturnWord ⟨9⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    let bid := flopperSlotWord (auctionBidSlot id) σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1148⟩
      (vat :: vat :: yankSuckOutSize :: yankSuckOutPtr :: yankSuckInSize ::
        yankSuckOutPtr :: yankSuckOutSize :: yankSuckEndPtr :: yankSuckSelectorWord ::
        vat :: id :: ⟨334⟩ :: sel :: [])
      (yankSuckCalldataMem vow guy bid memMap) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k' C' := by
  intro id memHash memMap vat vow guy bid
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
  have hcallMem : (yankSuckCalldataMem vow guy bid memMap).size = 228 :=
    yankSuckCalldataMem_size vow guy bid hmemMap
  have hcallRead64 :
      (yankSuckCalldataMem vow guy bid memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    yankSuckCalldataMem_read64 vow guy bid hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (yankSuckCalldataMem vow guy bid memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankSuckCalldataMem vow guy bid memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd1054pre := evm_run rd1050 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k1055, C1055, rd1055raw⟩ := rd1054pre.sload (by native_decide) (by evm_ov)
  have rd1055 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1055⟩
      (flopperSlotWord ⟨2⟩ σ I :: ⟨2⟩ :: id :: ⟨334⟩ :: [sel])
      memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1055 C1055 := by
    simpa [id, memHash, flopperSlotWord] using rd1055raw
  have rd1057pre := rd1055.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1058, C1058, rd1058raw⟩ := rd1057pre.sload (by native_decide) (by evm_ov)
  have rd1058 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1058⟩
      (flopperSlotWord ⟨9⟩ σ I :: flopperSlotWord ⟨2⟩ σ I :: ⟨2⟩ ::
        id :: ⟨334⟩ :: [sel])
      memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1058 C1058 := by
    simpa [id, memHash, flopperSlotWord] using rd1058raw
  have rd1062pre := evm_run rd1058 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1063 := rd1062pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1067pre := evm_run rd1063 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1068 := rd1067pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, memHash, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1072pre := evm_run rd1068 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id, memHash] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memHash
  have rd1073 := rd1072pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd1076pre := evm_run rd1073 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : base + ⟨2⟩ = auctionPackedSlot id := by
    simp [base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd1076pre
  obtain ⟨k1077, C1077, rd1077raw⟩ := rd1076pre.sload (by native_decide) (by evm_ov)
  have rd1077 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1077⟩
      (flopperSlotWord (auctionPackedSlot id) σ I :: ⟨64⟩ :: ⟨0⟩ ::
        flopperSlotWord ⟨9⟩ σ I :: flopperSlotWord ⟨2⟩ σ I :: base ::
        id :: ⟨334⟩ :: [sel])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1077 C1077 := by
    simpa [flopperSlotWord] using rd1077raw
  have rd1078pre := rd1077.swap5 (by native_decide) (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd1078pre
  obtain ⟨k1079, C1079, rd1079raw⟩ := rd1078pre.sload (by native_decide) (by evm_ov)
  have rd1079 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1079⟩
      (bid :: ⟨64⟩ :: ⟨0⟩ :: flopperSlotWord ⟨9⟩ σ I ::
        flopperSlotWord ⟨2⟩ σ I :: flopperSlotWord (auctionPackedSlot id) σ I ::
        id :: ⟨334⟩ :: [sel])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1079 C1079 := by
    simpa [bid, flopperSlotWord] using rd1079raw
  have rd1148 := evm_run rd1079 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 yankSuckSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (yankSuckSelectorMem memMap) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankSuckVowMem vow memMap) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [yankSuckVowMem, vow, u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankSuckGuyMem vow guy memMap) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [yankSuckGuyMem, guy, u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankSuckCalldataMem vow guy bid memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 yankSuckSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 yankSuckInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc1148 :
      (⟨1079⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨1148⟩ := by
    native_decide
  rw [hpc1148] at rd1148
  exact ⟨_, _, by
    simpa [vat, vow, guy, bid, yankSuckSelectorMem, yankSuckVowMem,
      yankSuckGuyMem, yankSuckCalldataMem, yankSuckSelectorShifted,
      yankSuckOutPtr, yankSuckOutSize, yankSuckInSize, yankSuckEndPtr,
      flopperAddressReturnWord, flopperSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + yankSuckInSize =
        yankSuckInSize from by native_decide,
      show (⟨128⟩ : UInt256) + yankSuckInSize = yankSuckEndPtr from by native_decide,
      show yankSuckInSize + yankSuckOutPtr = yankSuckEndPtr from by native_decide]
      using rd1148⟩

theorem flopperYankX_suckNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨2⟩ σ I) = ⟨0⟩)
    (rd1050 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1050⟩
      [yankIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1148⟩ := flopperYankX_toSuckExtcodesizeGuard rd1050
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1148⟩) (okPc := ⟨1160⟩) rd1148
    hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

end Benchmarks.Dss.Flopper
