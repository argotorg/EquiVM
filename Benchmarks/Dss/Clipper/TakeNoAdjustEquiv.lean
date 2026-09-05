import Benchmarks.Dss.Clipper.TakeNonzeroFromFluxEquiv
import Benchmarks.Dss.Clipper.TakeFromFluxDataEmptyEquiv
import Benchmarks.Dss.Clipper.TakeNoAdjustSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- Refinement of the arithmetic path on which the initially computed `owe` and
   `slice` are retained.  Equality and full-lot callers select the appropriate
   zero-value continuation; partial purchases select the ordinary store suffix. -/
set_option maxHeartbeats 10000000 in
theorem clipperTakeNoAdjustEquiv
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
      (slice :: UInt256.mul price slice :: tab :: lot :: price :: tic :: packed ::
        stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
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
    (hpackedWord : packed = clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hslice : slice = clipperMinWord
      (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I))
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (howeLe : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hsliceLe : slice.toNat ≤ lot.toNat)
    (hite :
      let owe := UInt256.mul slice price
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe
            (Solm.EVM.storageStore
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨13⟩ ⟨1⟩)
            evmPrice I false price slice owe owe))
        evmPrice clipperTakeOweAdjustmentStmt
        (.ok (Frame.mk (contract v)
          (clipperTakeLocalsOwe
            (Solm.EVM.storageStore
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨13⟩ ⟨1⟩)
            evmPrice I false price slice owe owe)) evmPrice))
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
      σ₀ A I g slice (UInt256.mul price slice)
      (UInt256.sub tab (UInt256.mul price slice)) (UInt256.sub lot slice)
      price tic packed stopped dataLen dataStart who max amt id sel)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let owe := UInt256.mul price slice
  let tabNew := UInt256.sub tab owe
  let lotNew := UInt256.sub lot slice
  let fluxLocals := clipperTakeLocalsNoAdjustFluxBuyerRet evmLock evmPrice I
    price slice owe owe tabNew lotNew
  have howeLe' : (UInt256.mul slice price).toNat ≤
      (clipperTakeSalesTabEVMWord evmPrice I).toNat := by
    simpa [u256_mul_comm, htab] using howeLe
  have hsliceLe' : slice.toNat ≤
      (clipperTakeSalesLotEVMWord evmPrice I).toNat := by
    simpa [hlot] using hsliceLe
  have hfluxDogAbsent : fluxLocals.get? "dog" = none := by
    simp [fluxLocals, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore, Std.HashMap.get?_eq_getElem?]
  have hfluxOwe : fluxLocals.get? "owe" = some (.int (Int.ofNat owe.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_self]
  have hfluxSlice : fluxLocals.get? "slice" =
      some (.int (Int.ofNat slice.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_self]
  have hfluxTab : fluxLocals.get? "tab" =
      some (.int (Int.ofNat tabNew.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_self]
  have hfluxLot : fluxLocals.get? "lot" =
      some (.int (Int.ofNat lotNew.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotAssigned, store_get_self]
  have hwhoAddress :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
        AccountAddress.ofNat who.toNat := by
    apply Solm.Value.address.inj
    simpa [hwhoWord, u256_land_comm] using
      solcAddressValue_masked (clipperTakeWhoWord I)
  have hfluxWho : fluxLocals.get? "who" =
      some (.address (AccountAddress.ofNat who.toNat)) := by
    simp [fluxLocals, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore, clipperTakeWhoValue, hwhoAddress,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxUsr : fluxLocals.get? "usr" =
      some (.address (AccountAddress.ofNat packed.toNat)) := by
    simp [fluxLocals, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeSalesUsrEVMWord,
      clipperTakeSalesUsrWord, evmLock, evm0, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, storageStore_accountMap, storageStore_executionEnv,
      hpackedWord,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
  have hfluxData : fluxLocals.get? "data" = some (clipperTakeDataValue I) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
      clipperTakeStore, store_get_self]
  have hfluxId : fluxLocals.get? "id" = some (clipperTakeIdValue I) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
      clipperTakeStore, store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  have hfluxLocked : fluxLocals.get? "locked" = none := by
    simp [fluxLocals, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore, Std.HashMap.get?_eq_getElem?]
  have hfluxVow : fluxLocals.get? "vow" = none := by
    simp [fluxLocals, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore, Std.HashMap.get?_eq_getElem?]
  have hfluxSales : fluxLocals.get? "sales" = none := by
    simp [fluxLocals, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore, Std.HashMap.get?_eq_getElem?]
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
    have hpref := clipperTakeNoAdjustVatFluxNoCodeTailBlock v evmLock evmPrice I
      price slice hmul howeLe' hsliceLe'
      (by simpa [evm0, evmLock, owe, u256_mul_comm] using hite)
      hnoCode
    simpa [evm0, evmLock, hslice, clipperTakeAfterSliceStmts, List.append_assoc] using
      (execBlockAppendReverted
        (suff := clipperTakeAfterFluxStmts v ++ clipperTakeAfterMoveStmts v) hpref)
  have hwhoMasked : UInt256.land (clipperTakeWhoWord I) solcAddrMask = who := by
    exact hwhoWord.symm
  have hsourceVatFailure : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    intro evmVat outVat hvatCode hcallVat
    apply clipperTakeSourceRevertsOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evmPrice := evmPrice) v price hwv hlocked hstopped husr
      hmax hstatus
    have hpref := clipperTakeNoAdjustVatFluxCallFailureTailBlock v evmLock
      evmPrice evmVat I price slice hmul howeLe' hsliceLe'
      (by simpa [evm0, evmLock, owe, u256_mul_comm] using hite) hvatCode
      (by simpa [hwhoMasked] using hcallVat)
    simpa [evm0, evmLock, hslice, clipperTakeAfterSliceStmts, List.append_assoc] using
      (execBlockAppendReverted
        (suff := clipperTakeAfterFluxStmts v ++ clipperTakeAfterMoveStmts v) hpref)
  have hsourceFluxSuccess : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true →
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsSlice evmLock evmPrice I false price slice)) evmPrice
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++ clipperTakePostOweFluxStmts v)
        (.ok (Frame.mk (contract v) fluxLocals) evmVat) := by
    intro evmVat outVat hvatCode hcallVat
    simpa [fluxLocals, owe, tabNew, lotNew, htab, hlot, hwhoWord,
      u256_mul_comm] using
      (clipperTakeNoAdjustVatFluxCallSuccessTailBlock v evmLock evmPrice evmVat I
        price slice hmul howeLe' hsliceLe'
        (by simpa [evm0, evmLock, owe, u256_mul_comm] using hite) hvatCode
        (by simpa [hwhoMasked] using hcallVat))
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
    simpa [evm0, evmLock, hslice] using htail
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
    simpa [evm0, evmLock, hslice] using htail
  have hcontinue' : ClipperTakeStoreContinuationEquiv v code cA gh bl σ_evm
      σ_solm σ₀ A I g slice owe tabNew lotNew price tic packed stopped dataLen
      dataStart who max amt id sel := by
    dsimp only [owe, tabNew, lotNew]
    exact hcontinue
  by_cases hdataLenZero : dataLen = ⟨0⟩
  · exact clipperTakeFromFluxDataEmptyEquiv
      (sliceLocals := clipperTakeLocalsSlice evmLock evmPrice I false price slice)
      (fluxLocals := fluxLocals) (owe := owe) v hpatch hcode hdispatch hdec
      (by simpa [owe] using rd4223) hbaseSize hbaseRead64
      hAccountsPost hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis
      hevmPriceBlocks hevmPriceEnv hdataLenZero hdataLenEq hfluxDogAbsent
      hfluxOwe hfluxSlice hfluxTab hfluxLot hfluxWho hfluxUsr hfluxData hfluxId
      hfluxLocked hfluxVow hfluxSales hsourceVatNoCode hsourceVatFailure
      hsourceFluxSuccess hsourceCloseReverted hsourceCloseReturned hcontinue'
      hdepth hperm
  · exact clipperTakeFromFluxEquiv
      (sliceLocals := clipperTakeLocalsSlice evmLock evmPrice I false price slice)
      (fluxLocals := fluxLocals) (owe := owe) v hpatch hcode hdispatch hdec
      (by simpa [owe] using rd4223) hbaseSize hbaseRead64
      hAccountsPost hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis
      hevmPriceBlocks hevmPriceEnv hdataLenZero hdataLenEq hdataStartEq hlenMax
      hpayload hwhoClean hfluxDogAbsent hfluxOwe hfluxSlice hfluxTab hfluxLot
      hfluxWho hfluxUsr hfluxData hfluxId hfluxLocked hfluxVow hfluxSales
      hsourceVatNoCode hsourceVatFailure hsourceFluxSuccess hsourceCloseReverted
      hsourceCloseReturned hcontinue' hdepth hperm

end Benchmarks.Dss.Clipper
