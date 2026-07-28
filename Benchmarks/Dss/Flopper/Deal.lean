import Benchmarks.Dss.Flopper.AuctionCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `deal(uint256)` -/

abbrev dealIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev dealIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (dealIdWord I).toNat)

abbrev dealLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (dealIdValue I)

abbrev dealMintLocals (I : ExecutionEnv) : Store :=
  (dealLocals I).insert "_mintRet" (collapseReturns [])

abbrev dealLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev dealGemEvaledRef : EvaledStorageRef :=
  { base := "gem", steps := [] }

abbrev dealGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "guy"] }

abbrev dealLotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "lot"] }

abbrev dealTicEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "tic"] }

abbrev dealEndEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dealIdWord I)), .field "end"] }

abbrev dealTicWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) evm.accountMap
    evm.executionEnv

abbrev dealEndWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) evm.accountMap
    evm.executionEnv

abbrev dealGuyWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) evm.accountMap evm.executionEnv

abbrev dealLotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperSlotWord (auctionLotSlot (dealIdWord I)) evm.accountMap evm.executionEnv

abbrev dealGemWord (evm : EVM.State) : UInt256 :=
  flopperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv

abbrev dealTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev dealMintSelectorWord : UInt256 :=
  ⟨0x40c10f19⟩

abbrev dealMintSelectorShifted : UInt256 :=
  UInt256.shiftLeft dealMintSelectorWord ⟨224⟩

abbrev dealMintOutPtr : UInt256 := ⟨128⟩

abbrev dealMintInSize : UInt256 := ⟨68⟩

abbrev dealMintOutSize : UInt256 := ⟨0⟩

abbrev dealMintEndPtr : UInt256 := ⟨196⟩

noncomputable def dealMintSelectorMem (mem : ByteArray) : ByteArray :=
  dealMintSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def dealMintGuyMem (guy : UInt256) (mem : ByteArray) : ByteArray :=
  guy.toByteArray.write 0 (dealMintSelectorMem mem) 132 32

noncomputable def dealMintCalldataMem (guy lot : UInt256) (mem : ByteArray) : ByteArray :=
  lot.toByteArray.write 0 (dealMintGuyMem guy mem) 164 32

theorem dealMintSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (dealMintSelectorMem mem).size = 160 := by
  unfold dealMintSelectorMem
  exact toByteArray_write32_size_of_ge mem dealMintSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem dealMintGuyMem_size (guy : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (dealMintGuyMem guy mem).size = 164 := by
  unfold dealMintGuyMem
  exact toByteArray_write32_size_of_le (dealMintSelectorMem mem) guy 132 160 164
    (dealMintSelectorMem_size hmem)
    (by rw [dealMintSelectorMem_size hmem]; omega) (by omega)

theorem dealMintCalldataMem_size (guy lot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealMintCalldataMem guy lot mem).size = 196 := by
  unfold dealMintCalldataMem
  exact toByteArray_write32_size_of_le (dealMintGuyMem guy mem) lot 164 164 196
    (dealMintGuyMem_size guy hmem)
    (by rw [dealMintGuyMem_size guy hmem]) (by omega)

theorem dealMintSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealMintSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealMintSelectorMem
  rw [toByteArray_write_read_below_of_gap dealMintSelectorShifted mem 128 64
    (by omega) (by native_decide) (by rw [hmem]; native_decide),
    hread64]

theorem dealMintGuyMem_read64 (guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealMintGuyMem guy mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealMintGuyMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [dealMintSelectorMem_size hmem]; omega) (by omega),
    dealMintSelectorMem_read64 hmem hread64]

theorem dealMintCalldataMem_read64 (guy lot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dealMintCalldataMem guy lot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealMintCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [dealMintGuyMem_size guy hmem]) (by omega),
    dealMintGuyMem_read64 guy hmem hread64]

theorem dealMintCalldataMem_read128_4 (guy lot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealMintCalldataMem guy lot mem).readWithPadding 128 4 = mintSelector := by
  have hGuySize := dealMintGuyMem_size guy hmem
  have hSelectorSize := dealMintSelectorMem_size hmem
  unfold dealMintCalldataMem
  rw [toByteArray_write_read_below_len_of_gap lot (dealMintGuyMem guy mem) 164 128 4
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold dealMintGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (dealMintSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold dealMintSelectorMem
  rw [toByteArray_write_read_window_of_gap dealMintSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem dealMintCalldataMem_read132_32 (guy lot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealMintCalldataMem guy lot mem).readWithPadding 132 32 = guy.toByteArray := by
  have hGuySize := dealMintGuyMem_size guy hmem
  have hSelectorSize := dealMintSelectorMem_size hmem
  unfold dealMintCalldataMem
  rw [toByteArray_write_read_below_len_of_gap lot (dealMintGuyMem guy mem) 164 132 32
      (by rw [hGuySize]) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold dealMintGuyMem
  rw [toByteArray_write_read_back_of_gap guy (dealMintSelectorMem mem) 132
    (by rw [hSelectorSize]; native_decide)]

theorem dealMintCalldataMem_read164_32 (guy lot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealMintCalldataMem guy lot mem).readWithPadding 164 32 = lot.toByteArray := by
  have hGuySize := dealMintGuyMem_size guy hmem
  unfold dealMintCalldataMem
  rw [toByteArray_write_read_back_of_gap lot (dealMintGuyMem guy mem) 164
    (by rw [hGuySize]; native_decide)]

theorem dealMintCalldataMem_read128_68 (guy lot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dealMintCalldataMem guy lot mem).readWithPadding 128 68 =
      mintSelector ++ guy.toByteArray ++ lot.toByteArray := by
  have hsize : (dealMintCalldataMem guy lot mem).size = 196 :=
    dealMintCalldataMem_size guy lot hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (dealMintCalldataMem guy lot mem) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (dealMintCalldataMem guy lot mem) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [dealMintCalldataMem_read128_4 guy lot hmem,
    dealMintCalldataMem_read132_32 guy lot hmem,
    dealMintCalldataMem_read164_32 guy lot hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem dealAddressWord_eq_ofNat_address {w : UInt256}
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

theorem dealAddressWord_address_eq_target {w : UInt256} :
    EVM.address (AccountAddress.ofNat w.toNat) = AccountAddress.ofUInt256 w := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simpa [EVM.twoPow, AccountAddress.size] using
        (AccountAddress.ofNat w.toNat).isLt)

theorem dealMintEncode_eq (guy lot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hguyCanon : guy.toNat < EVM.addressModulus) :
    config.externalABI.encode? "mint"
        [.address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat lot.toNat)] =
      some ((dealMintCalldataMem guy lot mem).readWithPadding
        dealMintOutPtr.toNat dealMintInSize.toNat) := by
  change config.externalABI.encode? "mint"
      [.address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat lot.toNat)] =
    some ((dealMintCalldataMem guy lot mem).readWithPadding 128 68)
  rw [dealMintCalldataMem_read128_68 guy lot hmem]
  have hlotLt : lot.toNat < EVM.twoPow 256 := lot.val.isLt
  have hlotWord : EVM.word lot.toNat = lot := by
    show UInt256.ofNat lot.toNat = lot
    exact u256_ofNat_toNat _
  have hguyWord := dealAddressWord_eq_ofNat_address hguyCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, mintSelector, selectorBytes, hlotLt, hlotWord,
    hguyWord, word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem dealMintLocals_get_id (I : ExecutionEnv) :
    (dealMintLocals I).get? "id" = some (dealIdValue I) := by
  rw [dealMintLocals, store_get_ne _ _ (by decide)]
  simp [dealLocals]

theorem dealMintLocals_get_bids (I : ExecutionEnv) :
    (dealMintLocals I).get? "bids" = none := by
  rw [dealMintLocals, store_get_ne _ _ (by decide)]
  rw [dealLocals, store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem deleteStorage_dealMint_bid (evm : EVM.State) (I : ExecutionEnv) :
    deleteStorage? config { contract := contract, locals := dealMintLocals I } evm
      (bidRef (.var "id")) = .ok (auctionDeletePostState (dealIdWord I) evm) := by
  exact deleteStorage_auction_bid evm (dealMintLocals I) (dealIdWord I)
    (by simpa [dealIdValue] using dealMintLocals_get_id I)
    (dealMintLocals_get_bids I)

theorem evalExpr_deal_live_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := liveRef) (er := dealLiveEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨8⟩)
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
    (by simp [frame, liveRef])
    (by simp [frame, dealLiveEvaledRef, evalStorageRef, evalStorageRefSteps,
      liveRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by exact flopperStorageLocLoad_uint256 evm ⟨8⟩)

theorem evalExpr_deal_live_one_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := dealLocals I } evm (.storage liveRef) =
        .ok (.int 1) := by
    simpa [hload] using evalExpr_deal_live_storage evm I
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_deal_live_one_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage := evalExpr_deal_live_storage evm I
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    apply u256_inj
    exact Int.ofNat.inj hbad
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
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
    rw [flopperStorageLocLoad_uint48_offset20]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (dealIdWord I)))
        (UInt256.ofNat (256 ^ 20)))
      flopperUint48Mask]
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
    rw [flopperStorageLocLoad_uint48_offset26]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (dealIdWord I)))
        (UInt256.ofNat (256 ^ 26)))
      flopperUint48Mask]
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

theorem evalExpr_deal_guy_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat (dealGuyWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "guy") (er := dealGuyEvaledRef I)
    (t := .address) (loc := addrLoc (auctionPackedSlot (dealIdWord I)))
    (value := .address (AccountAddress.ofNat (dealGuyWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simp [frame, dealGuyEvaledRef, auctionIdKey, dealLocals, dealIdValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, addrSt])
    (by rfl)
    (by
      simpa [dealGuyWord, flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm (auctionPackedSlot (dealIdWord I)))

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
    (by simpa [dealLotWord, flopperSlotWord] using
      flopperStorageLocLoad_uint256 evm (auctionLotSlot (dealIdWord I)))

theorem evalExpr_deal_gem_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dealLocals I } evm (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat (dealGemWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := dealLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := gemRef) (er := dealGemEvaledRef)
    (t := .address) (loc := addrLoc ⟨3⟩)
    (value := .address (AccountAddress.ofNat (dealGemWord evm).toNat))
    (by simp [frame, gemRef])
    (by simp [frame, dealGemEvaledRef, evalStorageRef, evalStorageRefSteps,
      gemRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [dealGemWord, flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm ⟨3⟩)

theorem evalExprs_deal_mint_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := dealLocals I } evm
        [.storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "lot")] =
      .ok [.address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
        .int (Int.ofNat (dealLotWord evm I).toNat)] := by
  simp [evalExprs?, evalExpr_deal_guy_storage, evalExpr_deal_lot_storage]
  rfl

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
    have hltNat : (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat := by
      exact Int.ofNat_lt.mp hlt
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
    have hltNat : (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat := by
      exact Int.ofNat_lt.mp hlt
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

theorem evalExpr_deal_extCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_deal_extCodeGuard_false {evm : EVM.State} {locals : Store}
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

theorem dealExtCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap}
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

theorem dealExtCodeSizeWord_zero_lookup_code_zero {σ : AccountMap}
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

theorem flopperDealBodyReverts_notLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
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
              (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp))))] ++
          checkedExternalCallStmts (.storage gemRef) "mint" (.intLit 0)
            [.storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "lot")]
            "_mintRet" ++
          [.delete (bidRef (.var "id"))])
      hwv
      (evalExpr_deal_live_one_false evm I hlive)

theorem flopperDealBodyReverts_ticZero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (htic : dealTicWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_deal_finished_false_tic_zero evm I htic)))

theorem flopperDealBodyReverts_notFinished (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
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

theorem flopperDealBodyReverts_mintNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealGemWord evm) = ⟨0⟩) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  have hgem := evalExpr_deal_gem_storage evm I
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      dealExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap)
        (target := dealGemWord evm)
        (addr := AccountAddress.ofNat (dealGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := dealLocals I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_deal_extCodeGuard_false hgem hnoCodeLookup
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse hguard))

theorem flopperDealBodyReverts_mintCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealGemWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealGemWord evm).toNat))
        "mint" 0
        [.address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body .reverted := by
  have hgem := evalExpr_deal_gem_storage evm I
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      dealExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dealGemWord evm)
        (addr := AccountAddress.ofNat (dealGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dealLocals I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_deal_extCodeGuard_true hgem hcodeLookup
  have hargs := evalExprs_deal_mint_args evm I
  have hchecked :
      ExecBlock config { contract := contract, locals := dealLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "mint" (.intLit 0)
          [.storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "lot")]
          "_mintRet")
        .reverted := by
    exact checkedExternalCallFailure hguard hgem hargs hcall
  have htail :
      ExecBlock config { contract := contract, locals := dealLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "mint" (.intLit 0)
          [.storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "lot")]
          "_mintRet" ++
          [.delete (bidRef (.var "id"))])
        .reverted :=
    Reasoning.Refinement.execBlock_append_term hchecked (by intro f e h; cases h)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      htail)

theorem flopperDealBodyReturns_mintCallSuccess
    (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (htic : dealTicWord evm I ≠ ⟨0⟩)
    (hfinished :
      (dealTicWord evm I).toNat < (dealTimestampWord evm).toNat ∨
      (dealEndWord evm I).toNat < (dealTimestampWord evm).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (dealGemWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (dealGemWord evm).toNat))
        "mint" 0
        [.address (AccountAddress.ofNat (dealGuyWord evm I).toNat),
          .int (Int.ofNat (dealLotWord evm I).toNat)]
        (true, evm', out) true) :
    ExecTransitionBody config contract evm (dealLocals I) dealTransition.body
      (.returned { contract := contract, locals := dealMintLocals I }
        (auctionDeletePostState (dealIdWord I) evm') none) := by
  have hgem := evalExpr_deal_gem_storage evm I
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (dealGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      dealExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := dealGemWord evm)
        (addr := AccountAddress.ofNat (dealGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dealLocals I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_deal_extCodeGuard_true hgem hcodeLookup
  have hargs := evalExprs_deal_mint_args evm I
  have hdec : config.externalABI.decode? "mint" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hchecked :
      ExecBlock config { contract := contract, locals := dealLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "mint" (.intLit 0)
          [.storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "lot")]
          "_mintRet")
        (.ok { contract := contract, locals := dealMintLocals I } evm') := by
    simpa [checkedExternalCallStmts, dealMintLocals] using
      checkedExternalCallSuccess hguard hgem hargs hcall hdec
  have hdelete :
      ExecBlock config { contract := contract, locals := dealMintLocals I } evm'
        [.delete (bidRef (.var "id"))]
        (.ok { contract := contract, locals := dealMintLocals I }
          (auctionDeletePostState (dealIdWord I) evm')) := by
    exact ExecBlock.consNormal (ExecStmt.delete (deleteStorage_dealMint_bid evm' I))
      ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := dealLocals I } evm
        (checkedExternalCallStmts (.storage gemRef) "mint" (.intLit 0)
          [.storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "lot")]
          "_mintRet" ++
          [.delete (bidRef (.var "id"))])
        (.ok { contract := contract, locals := dealMintLocals I }
          (auctionDeletePostState (dealIdWord I) evm')) :=
    Reasoning.Refinement.execBlock_append hchecked hdelete
  refine ExecFuncBody.execBlockOK ?_
  simpa [dealTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_deal_finished_true evm I htic hfinished)) <|
      htail)

theorem flopperDecode_deal_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata =
    some (dealLocals I)
  simpa [config, dealLocals, dealIdValue, dealIdWord, uint256] using
    decodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "id") hsz36

theorem flopperDecode_deal_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [uint256] I.calldata = none
  simpa [config, uint256] using
    decodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "id") hsz4 hshort

theorem flopperReachDealBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 3)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨804⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0xc959c42b⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xc9 0x59 0xc4 0x2b ⟨0xc959c42b⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 1 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc 1))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨804⟩ 1 hfirst
    (fun j hj => flopperHighHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperDealX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3892⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨804⟩) (ret := ⟨334⟩)
    (decoded := ⟨826⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd827 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd828 := rd827.pop (by native_decide) (by evm_ov)
  have rd829 := rd828.calldataload (by native_decide) (by evm_ov)
  have rd832 := rd829.push2 ⟨3892⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [dealIdWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd832.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flopperDealX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨804⟩) (ret := ⟨334⟩)
    (decoded := ⟨826⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem flopperDealX_notLive {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3892⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3892⟩ := h
  have rd3895 := evm_run rd3892 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3896, C3896, rd3896raw⟩ := rd3895.sload (by native_decide) (by evm_ov)
  have rd3896 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3896⟩
      (flopperSlotWord ⟨8⟩ σ I :: dealIdWord I :: ⟨334⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3896 C3896 := by
    simpa [flopperSlotWord] using rd3896raw
  have rd3902 := evm_run rd3896 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flopperSlotWord ⟨8⟩ σ I) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro hbad
    exact hlive hbad.symm
  have rd3903 := rd3902.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3903⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨0x466c6f707065722f6e6f742d6c697665⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c6f707065722f6e6f742d6c69766500000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd3903
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp)

theorem flopperDealX_liveOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3892⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3892⟩ := h
  have rd3895 := evm_run rd3892 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3896, C3896, rd3896raw⟩ := rd3895.sload (by native_decide) (by evm_ov)
  have rd3896 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3896⟩
      (flopperSlotWord ⟨8⟩ σ I :: dealIdWord I :: ⟨334⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3896 C3896 := by
    simpa [flopperSlotWord] using rd3896raw
  have rd3902 := evm_run rd3896 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flopperSlotWord ⟨8⟩ σ I) ≠ ⟨0⟩ := by
    rw [hlive, u256_eq_refl]
    exact one_ne_zero_uint
  exact ⟨_, _, rd3902.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDealX_toTicGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd3966 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4000⟩
      [flopperUint48Offset20Word (auctionPackedSlot id) σ I, id, ⟨334⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap
  let memKey := wordAt0Mem id solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  have rd3971pre := evm_run rd3966 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3972 := rd3971pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3976pre := evm_run rd3972 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3977 := rd3976pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3980pre := evm_run rd3977 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id solcFreePtrMem
  have rd3981 := rd3980pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd3984pre := evm_run rd3981 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd3984pre
  obtain ⟨k3985, C3985, rd3985raw⟩ := rd3984pre.sload (by native_decide) (by evm_ov)
  have rd3985 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3985⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, id, ⟨334⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3985 C3985 := by
    simpa [flopperSlotWord] using rd3985raw
  have rd3992 := evm_run rd3985 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd3999 := rd3992.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4000 := rd3999.and (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flopperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd4000⟩

set_option maxHeartbeats 1000000 in
theorem flopperDealX_ticZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I = ⟨0⟩)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := dealIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  obtain ⟨_, _, rd3966'⟩ := rd3966
  obtain ⟨_, _, rd4000⟩ := flopperDealX_toTicGuard rd3966'
  have rd4007 := evm_run rd4000 with [
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨4087⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I) ≠
      ⟨0⟩ := by
    rw [show flopperUint48Offset20Word (auctionPackedSlot id) σ I =
      flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I from rfl, htic]
    decide
  have rd4087 := rd4007.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd4088 := rd4087.jumpdest (by native_decide) (by evm_ov)
  have rd4091 := rd4088.push2 ⟨4159⟩ (by native_decide) (by evm_ov)
  have hnotFinished :
      UInt256.isZero
        (UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I)) =
        ⟨0⟩ := by
    rw [show flopperUint48Offset20Word (auctionPackedSlot id) σ I =
      flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I from rfl, htic]
    native_decide
  have rd4092raw := rd4091.jumpiNT (by native_decide) hnotFinished (by evm_ov)
  have hpc4092 : (⟨4087⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨4092⟩ := by
    native_decide
  rw [hpc4092] at rd4092raw
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4092⟩)
    (len := ⟨20⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bdb9bdd0b599a5b9a5cda1959⟩)
    (shift := ⟨98⟩)
    (word := ⟨0x466c6f707065722f6e6f742d66696e6973686564000000000000000000000000⟩)
    (op := .PUSH20)
    (width := 20)
    rd4092raw
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

theorem flopperDealX_ticNonzero_toTicLtStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (rd4000 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4000⟩
      [flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I, dealIdWord I,
        ⟨334⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4009⟩
      [dealIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4007 := evm_run rd4000 with [
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨4087⟩ (by native_decide) (by evm_ov)]
  have hcond :
      UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne htic
  have rd4008 := rd4007.jumpiNT (by native_decide) hcond (by evm_ov)
  exact ⟨_, _, rd4008.pop (by native_decide) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDealX_toTicLtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd4009 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4009⟩
      [dealIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memTic := twoWordHashMem id ⟨1⟩ (twoWordHashMem id ⟨1⟩ solcFreePtrMem)
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4045⟩
      [UInt256.lt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memTic
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memKey := wordAt0Mem id mem0
  let base := solcMappingSlot ⟨1⟩ id
  have rd4013pre := evm_run rd4009 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4014 := rd4013pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, mem0, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4018pre := evm_run rd4014 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4019 := rd4018pre.mstore 0 memTic (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTic, mem0, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4022pre := evm_run rd4019 with [
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
  have rd4023 := rd4022pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd4026pre := evm_run rd4023 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd4026pre
  obtain ⟨k4027, C4027, rd4027raw⟩ := rd4026pre.sload (by native_decide) (by evm_ov)
  have rd4027 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4027⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4027 C4027 := by
    simpa [flopperSlotWord] using rd4027raw
  have rd4036 := evm_run rd4027 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4043 := rd4036.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4044 := rd4043.and (by native_decide) (by evm_ov)
  have rd4045 := rd4044.lt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flopperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd4045⟩

set_option maxHeartbeats 1000000 in
theorem flopperDealX_toEndLtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd4051 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4051⟩
      [dealIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩
        (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memTic := twoWordHashMem id ⟨1⟩ (twoWordHashMem id ⟨1⟩ solcFreePtrMem)
    let memEnd := twoWordHashMem id ⟨1⟩ memTic
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4087⟩
      [UInt256.lt (flopperUint48Offset26Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), id, ⟨334⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memTic memEnd
  let memKey := wordAt0Mem id memTic
  let base := solcMappingSlot ⟨1⟩ id
  have rd4055pre := evm_run rd4051 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4056 := rd4055pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memTic, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4060pre := evm_run rd4056 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4061 := rd4060pre.mstore 0 memEnd (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memEnd, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4064pre := evm_run rd4061 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memEnd.readWithPadding 0 64))) = base := by
    simpa [base, memEnd, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd4065 := rd4064pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd4068pre := evm_run rd4065 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd4068pre
  obtain ⟨k4069, C4069, rd4069raw⟩ := rd4068pre.sload (by native_decide) (by evm_ov)
  have rd4069 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4069⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, id, ⟨334⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4069 C4069 := by
    simpa [flopperSlotWord] using rd4069raw
  have rd4078 := evm_run rd4069 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4085 := rd4078.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4086 := rd4085.and (by native_decide) (by evm_ov)
  have rd4087 := rd4086.lt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flopperUint48Offset26Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = UInt256.ofNat (256 ^ 26)
        from by native_decide]
      using rd4087⟩

set_option maxHeartbeats 1000000 in
theorem flopperDealX_notFinished {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hticGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat)
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd3966'⟩ := rd3966
  obtain ⟨_, _, rd4000⟩ := flopperDealX_toTicGuard rd3966'
  obtain ⟨_, _, rd4009⟩ :=
    flopperDealX_ticNonzero_toTicLtStart (g := g) htic (by simpa [id, mem0] using rd4000)
  obtain ⟨_, _, rd4045⟩ := flopperDealX_toTicLtGuard rd4009
  have hticLt :
      UInt256.lt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hticGe
  have rd4049 := evm_run rd4045 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨4087⟩ (by native_decide) (by evm_ov)]
  have rd4050 := rd4049.jumpiNT (by native_decide) hticLt (by evm_ov)
  have rd4051raw := rd4050.pop (by native_decide) (by evm_ov)
  have hpc4051 : (⟨4045⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ =
      ⟨4051⟩ := by
    native_decide
  rw [hpc4051] at rd4051raw
  have rd4051 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4051⟩
      [id, ⟨334⟩, sel] memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [id, memTic, hticLt] using rd4051raw⟩
  obtain ⟨_, _, rd4051'⟩ := rd4051
  obtain ⟨_, _, rd4087⟩ := flopperDealX_toEndLtGuard rd4051'
  have hendLt :
      UInt256.lt (flopperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hendGe
  have rd4088 := rd4087.jumpdest (by native_decide) (by evm_ov)
  have rd4091 := rd4088.push2 ⟨4159⟩ (by native_decide) (by evm_ov)
  have rd4092raw := rd4091.jumpiNT (by native_decide) hendLt (by evm_ov)
  have hpc4092 : (⟨4087⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨4092⟩ := by
    native_decide
  rw [hpc4092] at rd4092raw
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4092⟩)
    (len := ⟨20⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bdb9bdd0b599a5b9a5cda1959⟩)
    (shift := ⟨98⟩)
    (word := ⟨0x466c6f707065722f6e6f742d66696e6973686564000000000000000000000000⟩)
    (op := .PUSH20)
    (width := 20)
    rd4092raw
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (by
      have hmem0 : mem0.size = 96 := by
        simpa [mem0, id] using
          twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, id, mem0] using twoWordHashMem_size_96 id ⟨1⟩ hmem0
      simpa [memEnd, id, memTic] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic)
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
      simpa [memEnd, id, memTic] using
        twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic)
    (by simp)

end Benchmarks.Dss.Flopper
