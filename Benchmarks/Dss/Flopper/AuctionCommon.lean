import Reasoning.EVMWord
import Reasoning.PackedStorage
import Reasoning.ABIComposite
import Benchmarks.Dss.Flopper.Bids
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! Shared ABI helpers for the auction action entry points. -/

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


theorem evalExpr_auction_id (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "id") =
      .ok (.int (Int.ofNat id.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "id") = _
  rw [hget]
  rfl

theorem evalStorageRef_auction_bid (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm (bidRef (.var "id")) =
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

def auctionRuntimeDeleteAccountMap (owner : AccountAddress) (id : UInt256)
    (σ : AccountMap) : AccountMap :=
  sstoreAccountMap owner
    (sstoreAccountMap owner
      (sstoreAccountMap owner σ (auctionBidSlot id) ⟨0⟩)
      (auctionLotSlot id) ⟨0⟩)
    (auctionPackedSlot id) ⟨0⟩

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
  erw [clearStorage_uint256_zero (slot := auctionBidSlot id) (hloc := auctionBidLayout evm id)]
  change clearFields? config (auctionDeleteAfterBid id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("lot", uint256St), ("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  erw [clearStorage_uint256_zero (slot := auctionLotSlot id)
    (hloc := auctionLotLayout (auctionDeleteAfterBid id evm) id)]
  change clearFields? config (auctionDeleteAfterLot id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  erw [clearStorage_addr_zero (slot := auctionPackedSlot id)
    (hloc := auctionGuyLayout (auctionDeleteAfterLot id evm) id)]
  change clearFields? config (auctionDeleteAfterGuy id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  erw [clearStorage_uint48_offset20_zero (slot := auctionPackedSlot id)
    (hloc := auctionTicLayout (auctionDeleteAfterGuy id evm) id)]
  change clearFields? config (auctionDeleteAfterTic id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  erw [clearStorage_uint48_offset26_zero (slot := auctionPackedSlot id)
    (hloc := auctionEndLayout (auctionDeleteAfterTic id evm) id)]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp [auctionDeletePostState]

theorem auctionDeletePackedFinalWord_zero (id : UInt256) (evm : EVM.State) :
    clearUint48Offset26Word
        (Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
          (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id)) =
      ⟨0⟩ := by
  by_cases hacc0 : evm.accountMap.get? evm.executionEnv.codeOwner = none
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
      rw [Std.ExtTreeMap.get?_eq_getElem?] at hacc0
      simp [Solm.EVM.storageLoad, State.lookupAccount, hacc0, Option.option]
    rw [htic, hload]
    exact clearUint48Offset26Word_zero
  · obtain ⟨_, hacc0some⟩ := Option.ne_none_iff_exists'.mp hacc0
    have hacc0someElem := hacc0some
    rw [Std.ExtTreeMap.get?_eq_getElem?] at hacc0someElem
    have haccLotExists :
        ∃ acc, (auctionDeleteAfterLot id evm).accountMap.get?
          (auctionDeleteAfterLot id evm).executionEnv.codeOwner = some acc := by
      simp [auctionDeleteAfterLot, auctionDeleteAfterBid, Solm.EVM.storageStore,
        State.lookupAccount, hacc0someElem, Option.option, State.setAccount,
        Std.ExtTreeMap.getElem?_insert_self]
    obtain ⟨_, haccLot⟩ := haccLotExists
    have haccLotElem := haccLot
    rw [Std.ExtTreeMap.get?_eq_getElem?] at haccLotElem
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
        ∃ acc, (auctionDeleteAfterGuy id evm).accountMap.get?
          (auctionDeleteAfterGuy id evm).executionEnv.codeOwner = some acc := by
      simp [auctionDeleteAfterGuy, haccLotElem, Solm.EVM.storageStore, State.lookupAccount,
        Option.option, State.setAccount, Std.ExtTreeMap.getElem?_insert_self]
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
theorem auctionDeletePostState_accountMapEq (id : UInt256) (evm : EVM.State)
    (owner : AccountAddress) (howner : evm.executionEnv.codeOwner = owner) :
    auctionRuntimeDeleteAccountMap owner id evm.accountMap =
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
      sstoreAccountMap srcOwner m2 packedSlot vEnd =
        sstoreAccountMap srcOwner (sstoreAccountMap srcOwner m2 packedSlot vGuy)
          packedSlot vEnd :=
    sstoreAccountMap_self_update m2 srcOwner packedSlot vGuy vEnd
  have h2 :
      sstoreAccountMap srcOwner (sstoreAccountMap srcOwner m2 packedSlot vGuy)
          packedSlot vEnd =
        sstoreAccountMap srcOwner
          (sstoreAccountMap srcOwner
            (sstoreAccountMap srcOwner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd :=
    sstoreAccountMap_self_update
      (sstoreAccountMap srcOwner m2 packedSlot vGuy) srcOwner packedSlot vTic vEnd
  have h := h1.trans h2
  have hleftEq :
      sstoreAccountMap srcOwner m2 packedSlot vEnd =
        sstoreAccountMap srcOwner m2 packedSlot ⟨0⟩ := by
    rw [hfinal]
  have h' :
      sstoreAccountMap srcOwner m2 packedSlot ⟨0⟩ =
        (sstoreAccountMap srcOwner
          (sstoreAccountMap srcOwner
            (sstoreAccountMap srcOwner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd) := by
    simpa [hleftEq] using h
  simpa [auctionRuntimeDeleteAccountMap, auctionDeletePostState, auctionDeleteAfterTic,
    auctionDeleteAfterGuy, auctionDeleteAfterLot, auctionDeleteAfterBid, m2, srcOwner, bidSlot,
    lotSlot, packedSlot, vGuy, vTic, vEnd, howner, storageStore_accountMap,
    storageStore_executionEnv] using h'


theorem RD.flopperCheckedMulReturns
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hret : (D_J flopperBytecode 0).contains ret = true)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (rd4674 : RD flopperBytecode I g s0 ⟨4674⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    ∃ k' C', RD flopperBytecode I g s0 ret (x * y :: R) mem aw rdata acc k' C' := by
  have rd4701prep := evm_run rd4674 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨4701⟩ (by native_decide) (by evm_ov)]
  by_cases hy0 : y = ⟨0⟩
  · have hcond : UInt256.isZero y ≠ ⟨0⟩ := by
      rw [hy0]
      decide
    have rd4701 := rd4701prep.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd4705 := evm_run rd4701 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
    have rd4710 := rd4705.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd4715 := evm_run rd4710 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd4715.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa [hy0] using rdret⟩
  · have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
    have rd4684 := rd4701prep.jumpiNT (by native_decide) hcond (by evm_ov)
    have rd4696 := evm_run rd4684 with [
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw mul (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨4698⟩ (by native_decide) (by evm_ov)]
    have rd4698 := rd4696.jumpiT (by native_decide) hy0 (by jump_dest) (by evm_ov)
    have hyNatNe : y.toNat ≠ 0 := by
      intro hzero
      exact hy0 (uint256_toNat_eq_zero hzero)
    have hdivWord : UInt256.div (x * y) y = x := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (x * y).toNat = x.toNat * y.toNat := by
        rw [umul_toNat x y hfit]
      rw [hprod]
      simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat
        (Nat.pos_of_ne_zero hyNatNe)
    have rd4705 := evm_run rd4698 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
    have heqCond : UInt256.eq (UInt256.div (x * y) y) x ≠ ⟨0⟩ := by
      rw [hdivWord, u256_eq_refl]
      exact one_ne_zero_uint
    have rd4710 := rd4705.jumpiT (by native_decide) heqCond (by jump_dest)
      (by evm_ov)
    have rd4715 := evm_run rd4710 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd4715.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa using rdret⟩

theorem RD.flopperCheckedMulOverflowReverts
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (rd4674 : RD flopperBytecode I g s0 ⟨4674⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev flopperBytecode g s0 := by
  have hyNe : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (x * y) y ≠ x := by
    intro hbad
    have h := u256_mul_div_overflow_ne x y hover
    exact h (by
      have hcomm : y * x = x * y := by
        simpa using u256_mul_comm y x
      rw [hcomm]
      exact hbad)
  have rd4701prep := evm_run rd4674 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨4701⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyNe
  have rd4684 := rd4701prep.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd4696 := evm_run rd4684 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨4698⟩ (by native_decide) (by evm_ov)]
  have rd4698 := rd4696.jumpiT (by native_decide) hyNe (by jump_dest) (by evm_ov)
  have rd4705 := evm_run rd4698 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rd4706 := rd4705.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4706
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.flopperAuctionDeleteTailSplit
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {σ : AccountMap}
    {k C : ℕ} {drop0 drop1 drop2 scratch id : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hMstore0Aw : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw)
    (hMstore32Aw : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw)
    (hKeccakAw : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw)
    (hov : R.length + 10 ≤ 1024)
    (h : RD flopperBytecode I g s0 ⟨1180⟩
      (drop0 :: drop1 :: drop2 :: scratch :: id :: ⟨334⟩ :: R)
      mem aw rdata σ k C) :
    (I.perm = true ∧
      RDret flopperBytecode g s0
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (auctionBidSlot id) ⟨0⟩)
            (auctionLotSlot id) ⟨0⟩)
          (auctionPackedSlot id) ⟨0⟩)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic flopperBytecode g s0) := by
  let mem1 := wordAt0Mem id mem
  let mem2 := twoWordHashMem id ⟨1⟩ mem
  let base := solcMappingSlot ⟨1⟩ id
  have rd1184 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1188 := evm_run rd1184 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd1189 := rd1188.mstore 0 mem1 aw
    (by native_decide)
    (memoryExpansionCost_zero_of_aw_stable hMstore0Aw)
    (by simp [mem1, wordAt0Mem])
    hMstore0Aw
    (by evm_ov)
  have rd1196pre := evm_run rd1189 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1197 := rd1196pre.mstore 0 mem2 aw
    (by native_decide)
    (memoryExpansionCost_zero_of_aw_stable hMstore32Aw)
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [mem1, mem2, twoWordHashMem, wordAt32Mem])
    hMstore32Aw
    (by evm_ov)
  have rd1200pre := evm_run rd1197 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC (mem2.readWithPadding 0 64))) = base := by
    simpa [base, mem2] using twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd1201raw := rd1200pre.keccak256 0 base aw
    (by native_decide)
    (by
      change Cₘ (UInt256.ofNat (MachineState.M aw.toNat 0 64)) - Cₘ aw = 0
      rw [hKeccakAw]
      simp)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by
      rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact hKeccakAw)
    (by evm_ov)
  have rd1203pre := evm_run rd1201raw with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have hstoreDec : decode flopperBytecode ⟨1203⟩ = some (.SSTORE, none) := by native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd1203pre.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd1204raw⟩ := rd1203pre.sstore hperm hstoreDec
    (by simp only [List.length_cons]; omega)
  have rd1209pre := evm_run rd1204raw with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1210raw⟩ := rd1209pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1213pre := evm_run rd1210raw with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1214raw⟩ := rd1213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd334 := rd1214raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  have hslot2 : (⟨2⟩ : UInt256) + base = base + ⟨2⟩ := u256_add_comm _ _
  have hstop := RD.stop rd335 (by native_decide) (by evm_ov)
  rw [hslot2] at hstop
  simpa only [base, auctionBidSlot, auctionLotSlot_eq, auctionPackedSlot_eq,
    auctionBaseSlot_eq] using hstop

end Benchmarks.Dss.Flopper
