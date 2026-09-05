import Benchmarks.Dss.Clipper.TakeChostNonzeroEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- Common refinement for the chost branch that reduces the purchase.  The
   caller chooses the residual-value continuation, including the exact-full-lot
   case where the adjusted slice clears the lot. -/
set_option maxHeartbeats 8000000 in
theorem clipperTakeChostAdjustEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost : AccountMap} {evmPrice : EVM.State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {baseMem rdata : ByteArray} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
      (List.map Param.name (takeTransition v).params)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd4223 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4223⟩
      (((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price) ::
        UInt256.sub tab (solcSlotWord σPost I ⟨9⟩) :: tab :: lot :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      baseMem (UInt256.ofNat 7) rdata (cAPost, σPost) k C)
    (hbaseSize : baseMem.size = 196)
    (hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccountsPost : accountMapEquiv σPost evmPrice.accountMap)
    (hevmPriceSigma0 : evmPrice.σ₀ = σ₀)
    (hevmPriceCreated : evmPrice.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPrice.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPrice.blocks = bl)
    (hevmPriceEnv : evmPrice.executionEnv = I)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat = 32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload : (((I.calldata.toList.drop 4).drop
      ((clipperTakeDataOffsetWord I).toNat + 32)).take
      (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat)
    (hwhoClean : UInt256.land who solcAddrMask = who)
    (hwhoWord : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hidWord : id = clipperTakeIdWord I)
    (hpackedWord : packed = clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hslice : slice = clipperMinWord
      (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I))
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hlt : (UInt256.mul price slice).toNat < tab.toNat)
    (hsliceLt : slice.toNat < lot.toNat)
    (hremainingLt : (UInt256.sub tab (UInt256.mul price slice)).toNat <
      (solcSlotWord σPost I ⟨9⟩).toNat)
    (hchostTab : (solcSlotWord σPost I ⟨9⟩).toNat < tab.toNat)
    (hprice : price ≠ ⟨0⟩)
    (hsliceAdjustedLe :
      ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price).toNat ≤ lot.toNat)
    (hlocked : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstopped : (solcSlotWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr : clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) (Frame.mk (contract v) (clipperTakeLocalsTic evmLock I))
        evmLock (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk (contract v) (clipperTakeLocalsSt evmLock I false price)) evmPrice))
    (hcontinue : ClipperTakeStoreContinuationEquiv v code cA gh bl σ_evm σ_solm
      σ₀ A I g ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price)
      (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩))
      (UInt256.sub tab (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)))
      (UInt256.sub lot
        ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price))
      price tic packed stopped dataLen dataStart who max amt id sel)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let sourceSlice := clipperMinWord
    (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)
  let owe0 := UInt256.mul slice price
  let chost := Solm.EVM.storageLoad evmPrice evmPrice.executionEnv.codeOwner ⟨9⟩
  let remainingTab := UInt256.sub (clipperTakeSalesTabEVMWord evmPrice I) owe0
  let owe := UInt256.sub (clipperTakeSalesTabEVMWord evmPrice I) chost
  let sliceAdjusted := owe.div price
  let arithmeticLocals := clipperTakeLocalsChostOweSlice evmLock evmPrice I price
    slice owe0 owe0 chost remainingTab owe sliceAdjusted
  let fluxLocals := clipperTakeLocalsPostFluxBuyerRet arithmeticLocals
    ((clipperTakeSalesTabEVMWord evmPrice I).sub owe)
    ((clipperTakeSalesLotEVMWord evmPrice I).sub sliceAdjusted)
  have hchostEq : chost = solcSlotWord σPost I ⟨9⟩ := by
    have hslot := accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨9⟩ ⟨0⟩
    simp [chost, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hevmPriceEnv, hslot]
  have hmul' : (UInt256.mul slice price).toNat ≤
      (clipperTakeSalesTabEVMWord evmPrice I).toNat := by
    simpa [u256_mul_comm, htab] using hle
  have hlt' : (UInt256.mul slice price).toNat <
      (clipperTakeSalesTabEVMWord evmPrice I).toNat := by
    simpa [u256_mul_comm, htab] using hlt
  have hsliceLt' : slice.toNat <
      (clipperTakeSalesLotEVMWord evmPrice I).toNat := by
    simpa [hlot] using hsliceLt
  have hremainingLt' :
      ((clipperTakeSalesTabEVMWord evmPrice I).sub (slice.mul price)).toNat <
        chost.toNat := by
    simpa [hchostEq, htab, u256_mul_comm] using hremainingLt
  have hchostTab' : chost.toNat <
      (clipperTakeSalesTabEVMWord evmPrice I).toNat := by
    simpa [hchostEq, htab] using hchostTab
  have hsliceAdjustedLe' : sliceAdjusted.toNat ≤
      (clipperTakeSalesLotEVMWord evmPrice I).toNat := by
    simpa [sliceAdjusted, owe, hchostEq, htab, hlot] using hsliceAdjustedLe
  have hfluxDogAbsent : fluxLocals.get? "dog" = none := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxOwe : fluxLocals.get? "owe" = some (.int (Int.ofNat owe.toNat)) := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxSlice : fluxLocals.get? "slice" =
      some (.int (Int.ofNat sliceAdjusted.toNat)) := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem_insert]
  have hfluxTab : fluxLocals.get? "tab" = some (.int (Int.ofNat
      ((clipperTakeSalesTabEVMWord evmPrice I).sub owe).toNat)) := by
    simp [fluxLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxLot : fluxLocals.get? "lot" = some (.int (Int.ofNat
      ((clipperTakeSalesLotEVMWord evmPrice I).sub sliceAdjusted).toNat)) := by
    simp [fluxLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem_insert]
  have hwhoAddress :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
        AccountAddress.ofNat who.toNat := by
    apply Solm.Value.address.inj
    simpa [hwhoWord, u256_land_comm] using
      solcAddressValue_masked (clipperTakeWhoWord I)
  have hfluxWho : fluxLocals.get? "who" =
      some (.address (AccountAddress.ofNat who.toNat)) := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore,
      clipperTakeWhoValue, hwhoAddress,
      Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem_insert]
  have hfluxUsr : fluxLocals.get? "usr" =
      some (.address (AccountAddress.ofNat packed.toNat)) := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeSalesUsrEVMWord,
      clipperTakeSalesUsrWord, evmLock, evm0, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, storageStore_accountMap, storageStore_executionEnv,
      hpackedWord, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem_insert]
  have hfluxData : fluxLocals.get? "data" = some (clipperTakeDataValue I) := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxId : fluxLocals.get? "id" = some (clipperTakeIdValue I) := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxLocked : fluxLocals.get? "locked" = none := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxVow : fluxLocals.get? "vow" = none := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxSales : fluxLocals.get? "sales" = none := by
    simp [fluxLocals, arithmeticLocals, clipperTakeLocalsPostFluxBuyerRet,
      clipperTakeLocalsPostLotAssigned, clipperTakeLocalsPostTabAssigned,
      clipperTakeLocalsPostLotNew, clipperTakeLocalsPostTabNew,
      clipperTakeLocalsChostOweSlice, clipperTakeLocalsChostOwe,
      clipperTakeLocalsOweAdjusted, clipperTakeLocalsRemainingTab,
      clipperTakeLocalsChost, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hsourceVatNoCode :
      (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0 →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    intro hnoCode
    apply clipperTakeSourceRevertsOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evmPrice := evmPrice) v price hwv hlocked hstopped husr
      hmax hstatus
    have hpref := clipperTakeChostAdjustVatFluxNoCodeTailBlock v evmLock evmPrice
      I price slice hmul hmul' hlt' hsliceLt' hremainingLt' hchostTab' hprice
      hsliceAdjustedLe' hnoCode
    simpa [evm0, evmLock, sourceSlice, hslice, clipperTakeAfterSliceStmts,
      List.append_assoc] using
      (execBlockAppendReverted
        (suff := clipperTakeAfterFluxStmts v ++ clipperTakeAfterMoveStmts v) hpref)
  have hwhoMasked : UInt256.land (clipperTakeWhoWord I) solcAddrMask = who := by
    exact hwhoWord.symm
  have hchostRawEq :
      Solm.EVM.storageLoad evmPrice evmPrice.executionEnv.codeOwner ⟨9⟩ =
        solcSlotWord σPost I ⟨9⟩ := by
    simpa [chost] using hchostEq
  have hsourceVatFailure : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price).toNat)]
        (false, evmVat, outVat) true →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    intro evmVat outVat hvatCode hcallVat
    apply clipperTakeSourceRevertsOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evmPrice := evmPrice) v price hwv hlocked hstopped husr
      hmax hstatus
    have hpref := clipperTakeChostAdjustVatFluxCallFailureTailBlock v evmLock
      evmPrice evmVat I price slice hmul hmul' hlt' hsliceLt' hremainingLt'
      hchostTab' hprice hsliceAdjustedLe' hvatCode
      (by simpa [hwhoMasked, hchostRawEq, htab] using hcallVat)
    simpa [evm0, evmLock, sourceSlice, hslice, clipperTakeAfterSliceStmts,
      List.append_assoc] using
      (execBlockAppendReverted
        (suff := clipperTakeAfterFluxStmts v ++ clipperTakeAfterMoveStmts v) hpref)
  have hsourceFluxSuccess : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price).toNat)]
        (true, evmVat, outVat) true →
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsSlice evmLock evmPrice I false price slice)) evmPrice
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++ clipperTakePostOweFluxStmts v)
        (.ok (Frame.mk (contract v) fluxLocals) evmVat) := by
    intro evmVat outVat hvatCode hcallVat
    simpa [fluxLocals, arithmeticLocals, owe0, chost, remainingTab, owe,
      sliceAdjusted, htab, hlot] using
      (clipperTakeChostAdjustVatFluxCallSuccessTailBlock v evmLock evmPrice evmVat
        I price slice hmul hmul' hlt' hsliceLt' hremainingLt' hchostTab' hprice
        hsliceAdjustedLe' hvatCode
        (by simpa [hwhoMasked, hchostRawEq, htab] using hcallVat))
  have hsourceCloseReverted :
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsSlice evmLock evmPrice I false price slice)) evmPrice
        (clipperTakeAfterSliceStmts v) .reverted →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    intro htail
    apply clipperTakeSourceRevertsOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evmPrice := evmPrice) v price hwv hlocked hstopped husr
      hmax hstatus
    simpa [evm0, evmLock, sourceSlice, hslice] using htail
  have hsourceCloseReturned : ∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsSlice evmLock evmPrice I false price slice)) evmPrice
        (clipperTakeAfterSliceStmts v) (.ok finalFrame finalEvm) →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body
        (.returned finalFrame finalEvm none) := by
    intro finalFrame finalEvm htail
    apply clipperTakeSourceOkOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evmPrice := evmPrice) v price hwv hlocked hstopped husr
      hmax hstatus
    simpa [evm0, evmLock, sourceSlice, hslice] using htail
  by_cases hdataLenZero : dataLen = ⟨0⟩
  · exact clipperTakeFromFluxDataEmptyEquiv
      (sliceLocals := clipperTakeLocalsSlice evmLock evmPrice I false price slice)
      (fluxLocals := fluxLocals)
      (owe := UInt256.sub tab (solcSlotWord σPost I ⟨9⟩))
      (slice := (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price)
      v hpatch hcode hdispatch hdec rd4223 hbaseSize hbaseRead64 hAccountsPost
      hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis hevmPriceBlocks
      hevmPriceEnv hdataLenZero hdataLenEq hfluxDogAbsent
      (by simpa [owe, hchostEq, htab] using hfluxOwe)
      (by simpa [sliceAdjusted, owe, hchostEq, htab] using hfluxSlice)
      (by simpa [owe, hchostEq, htab] using hfluxTab)
      (by simpa [sliceAdjusted, owe, hchostEq, htab, hlot] using hfluxLot)
      hfluxWho hfluxUsr hfluxData hfluxId hfluxLocked hfluxVow hfluxSales
      hsourceVatNoCode hsourceVatFailure hsourceFluxSuccess hsourceCloseReverted
      hsourceCloseReturned hcontinue hdepth hperm
  · exact clipperTakeFromFluxEquiv
      (sliceLocals := clipperTakeLocalsSlice evmLock evmPrice I false price slice)
      (fluxLocals := fluxLocals)
      (owe := UInt256.sub tab (solcSlotWord σPost I ⟨9⟩))
      (slice := (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price)
      v hpatch hcode hdispatch hdec rd4223 hbaseSize hbaseRead64 hAccountsPost
      hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis hevmPriceBlocks
      hevmPriceEnv hdataLenZero hdataLenEq hdataStartEq hlenMax hpayload
      hwhoClean hfluxDogAbsent
      (by simpa [owe, hchostEq, htab] using hfluxOwe)
      (by simpa [sliceAdjusted, owe, hchostEq, htab] using hfluxSlice)
      (by simpa [owe, hchostEq, htab] using hfluxTab)
      (by simpa [sliceAdjusted, owe, hchostEq, htab, hlot] using hfluxLot)
      hfluxWho hfluxUsr hfluxData hfluxId hfluxLocked hfluxVow hfluxSales
      hsourceVatNoCode hsourceVatFailure hsourceFluxSuccess hsourceCloseReverted
      hsourceCloseReturned hcontinue hdepth hperm

/- The strict adjusted-slice case is the ordinary nonzero residual store. -/
theorem clipperTakeChostAdjustNonzeroEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost : AccountMap} {evmPrice : EVM.State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {baseMem rdata : ByteArray} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
      (List.map Param.name (takeTransition v).params)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd4223 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4223⟩
      (((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price) ::
        UInt256.sub tab (solcSlotWord σPost I ⟨9⟩) :: tab :: lot :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      baseMem (UInt256.ofNat 7) rdata (cAPost, σPost) k C)
    (hbaseSize : baseMem.size = 196)
    (hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccountsPost : accountMapEquiv σPost evmPrice.accountMap)
    (hevmPriceSigma0 : evmPrice.σ₀ = σ₀)
    (hevmPriceCreated : evmPrice.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPrice.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPrice.blocks = bl)
    (hevmPriceEnv : evmPrice.executionEnv = I)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat = 32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload : (((I.calldata.toList.drop 4).drop
      ((clipperTakeDataOffsetWord I).toNat + 32)).take
      (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat)
    (hwhoClean : UInt256.land who solcAddrMask = who)
    (hwhoWord : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hidWord : id = clipperTakeIdWord I)
    (hpackedWord : packed = clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hslice : slice = clipperMinWord
      (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I))
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hlt : (UInt256.mul price slice).toNat < tab.toNat)
    (hsliceLt : slice.toNat < lot.toNat)
    (hremainingLt : (UInt256.sub tab (UInt256.mul price slice)).toNat <
      (solcSlotWord σPost I ⟨9⟩).toNat)
    (hchostTab : (solcSlotWord σPost I ⟨9⟩).toNat < tab.toNat)
    (hprice : price ≠ ⟨0⟩)
    (hsliceAdjustedLt :
      ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price).toNat < lot.toNat)
    (hlocked : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstopped : (solcSlotWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr : clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) (Frame.mk (contract v) (clipperTakeLocalsTic evmLock I))
        evmLock (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk (contract v) (clipperTakeLocalsSt evmLock I false price)) evmPrice))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let chost := solcSlotWord σPost I ⟨9⟩
  let owe := UInt256.sub tab chost
  let sliceAdjusted := owe.div price
  have htabNe : UInt256.sub tab owe ≠ ⟨0⟩ := by
    have hchostPos : 0 < chost.toNat := by
      simpa [chost] using lt_of_le_of_lt (Nat.zero_le _) hremainingLt
    have hchostLe : chost.toNat ≤ tab.toNat := Nat.le_of_lt (by
      simpa [chost] using hchostTab)
    have howeNat : owe.toNat = tab.toNat - chost.toNat := usub_toNat hchostLe
    have howeLe : owe.toNat ≤ tab.toNat := by rw [howeNat]; omega
    have hsubNat : (UInt256.sub tab owe).toNat = tab.toNat - owe.toNat :=
      usub_toNat howeLe
    intro hz
    have hnat := congrArg UInt256.toNat hz
    rw [hsubNat, howeNat] at hnat
    change tab.toNat - (tab.toNat - chost.toNat) = 0 at hnat
    omega
  have hlotNe : UInt256.sub lot sliceAdjusted ≠ ⟨0⟩ := by
    have hsliceAdjustedLt' : sliceAdjusted.toNat < lot.toNat := by
      simpa [sliceAdjusted, owe, chost] using hsliceAdjustedLt
    have hsubNat : (UInt256.sub lot sliceAdjusted).toNat =
        lot.toNat - sliceAdjusted.toNat :=
      usub_toNat (Nat.le_of_lt hsliceAdjustedLt')
    intro hz
    have hnat := congrArg UInt256.toNat hz
    change (UInt256.sub lot sliceAdjusted).toNat = 0 at hnat
    rw [hsubNat] at hnat
    change lot.toNat - sliceAdjusted.toNat = 0 at hnat
    omega
  have hcontinue : ClipperTakeStoreContinuationEquiv v code cA gh bl σ_evm
      σ_solm σ₀ A I g
      ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price)
      (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩))
      (UInt256.sub tab (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)))
      (UInt256.sub lot
        ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price))
      price tic packed stopped dataLen dataStart who max amt id sel := by
    exact clipperTakeNonzeroStoreContinuation v hpatch hcode hdispatch hdec hidWord
      (by simpa [owe, chost] using htabNe)
      (by simpa [sliceAdjusted, owe, chost] using hlotNe) hdepth hperm
  exact clipperTakeChostAdjustEquiv v hpatch hcode hwv hdispatch hdec rd4223
    hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0 hevmPriceCreated
    hevmPriceGenesis hevmPriceBlocks hevmPriceEnv hdataLenEq hdataStartEq
    hlenMax hpayload hwhoClean hwhoWord hidWord hpackedWord htab hlot hslice hmul
    hle hlt hsliceLt hremainingLt hchostTab hprice (Nat.le_of_lt hsliceAdjustedLt)
    hlocked hstopped husr hmax hstatus hcontinue hdepth hperm

end Benchmarks.Dss.Clipper
