import Benchmarks.Dss.Clipper.TakeCallbackSource
import Benchmarks.Dss.Clipper.TakeOweVatMoveSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- Synchronize the successful `vat.flux` call once, before splitting on the
   optional callback.  The callback, `vat.move`, and later dog calls all need
   the same post-flux account equivalence, so keeping it existentially packaged
   avoids repeating the state reconstruction in every callback outcome. -/
theorem clipperTakeVatFluxCallSyncFromPostAccounts
    (v : ClipperImmutables)
    {cA cAPost gh bl σ_evm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat : AccountMap}
    {cAVat : Batteries.RBSet AccountAddress compare} {AVat : Substate}
    {evmPriceSolm : EVM.State} {outVat : ByteArray}
    {price tab who : UInt256}
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true) :
    ∃ evmVatSolm : EVM.State,
      typedCallViaEVM (config v) evmPriceSolm (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceSolm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat)]
        (true, evmVatSolm, outVat) true ∧
      accountMapEquiv σVat evmVatSolm.accountMap ∧
      evmVatSolm.σ₀ = σ₀ ∧
      evmVatSolm.createdAccounts = cAVat ∧
      evmVatSolm.genesisBlockHeader = gh ∧
      evmVatSolm.blocks = bl ∧
      evmVatSolm.executionEnv = I := by
  let evmPostEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σPost, createdAccounts := cAPost }
  have hAccountsState :
      accountMapEquiv evmPostEvm.accountMap evmPriceSolm.accountMap := by
    simpa [evmPostEvm, hevmPriceAccounts] using hAccountsPost
  obtain ⟨σVatSolm, AVatSolm, hcallVatSolmRaw, hAccountsVat⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmPriceSolm) (hcall := hcallVatEvm) hAccountsState
      (by simpa [evmPostEvm, initState] using hevmPriceSigma0.symm)
      (by simpa [evmPostEvm, initState] using hevmPriceCreated)
      (by simpa [evmPostEvm, initState] using hevmPriceGenesis)
      (by simpa [evmPostEvm, initState] using hevmPriceBlocks)
      (by simpa [evmPostEvm, initState] using hevmPriceEnv)
  let evmVatSolm : EVM.State :=
    { evmPriceSolm with
      accountMap := σVatSolm
      substate := AVatSolm
      createdAccounts := cAVat }
  refine ⟨evmVatSolm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [evmVatSolm, hevmPriceEnv, htab, hwho] using hcallVatSolmRaw
  · simpa [evmVatSolm] using hAccountsVat
  · simp [evmVatSolm, hevmPriceSigma0]
  · simp [evmVatSolm]
  · simp [evmVatSolm, hevmPriceGenesis]
  · simp [evmVatSolm, hevmPriceBlocks]
  · simp [evmVatSolm, hevmPriceEnv]

theorem clipperTakeDogWord_eq_of_accountMapEquiv
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I) :
    UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask =
      clipperTakeDogEVMWord evm := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  simp [clipperTakeDogEVMWord, solcSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, henv, hslot]

theorem clipperTakeCallbackSkipStmtOfEvmWords
    (v : ClipperImmutables) (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256)
    {σ : AccountMap}
    (hAccounts : accountMapEquiv σ evmVat.accountMap)
    (henv : evmVat.executionEnv = I)
    (hskip :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v ∨
      UInt256.land (clipperTakeWhoWord I) solcAddrMask =
        UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmVat) := by
  rcases hskip with hvat | hdog
  · exact clipperTakeCallbackSkipWhoVatStmt v evmLoc evmRead evmVat I
      price slice owe0 owe slice' tabNew lotNew hvat
  · have hdogWord :=
      clipperTakeDogWord_eq_of_accountMapEquiv hAccounts henv
    have hdogClean :
        UInt256.land (clipperTakeDogEVMWord evmVat) solcAddrMask =
          clipperTakeDogEVMWord evmVat := by
      rw [← hdogWord]
      exact solcAddrMask_clean
        (solcAddrMask_result_canonical (solcSlotWord σ I ⟨1⟩))
    apply clipperTakeCallbackSkipWhoDogStmt v evmLoc evmRead evmVat I
      price slice owe0 owe slice' tabNew lotNew
    simpa [hdogClean, hdogWord] using hdog

/- A failed callback ends the `take` before `vat.move`.  Keeping this assembly
   separate lets both the missing-code and failed-call cases share the same
   source-to-EVM equivalence argument. -/
theorem clipperTakeOweGtTabCallbackRevertTailBlock
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice : UInt256) {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)]
        (true, evmVat, outVat) true)
    (hcallback :
      let owe0 := UInt256.mul slice price
      let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
      let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
        (clipperTakeSalesTabEVMWord evmRead I)
      let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
            slice' tabNew lotNew))
        evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        .reverted) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v ++
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") (vatExpr v))
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet"))
      .reverted := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let fluxFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
        slice' tabNew lotNew)
  have hflux :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++
          clipperTakePostOweFluxStmts v)
        (.ok fluxFrame evmVat) := by
    simpa [sliceFrame, fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeOweGtTabVatFluxCallSuccessTailBlock v evmLoc evmRead evmVat I price
        slice hmul hgt hsliceLot hvatCode hcallVat
  have hletDog :
      ExecStmt (config v) fluxFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [fluxFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := fluxFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [fluxFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0
                slice' tabNew lotNew)
              (by
                simp [clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
                  clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
                  clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
                  clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
                  clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
                  clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
                  clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])))
  have hafterFlux :
      ExecBlock (config v) fluxFrame evmVat
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") (vatExpr v))
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    simpa [dogFrame, owe0, slice', tabNew, lotNew] using
      ExecBlock.consNormal hletDog (ExecBlock.consRevert hcallback)
  simpa [sliceFrame, fluxFrame, List.append_assoc] using
    execBlockAppendOk hflux hafterFlux

theorem clipperTakeOweGtTabCallbackRevertEquivFromPostWords
    (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPriceSolm evmVatSolm : EVM.State} {outVat : ByteArray}
    {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hrev : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat <
      UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmPriceSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmPriceSolm (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceSolm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat)]
        (true, evmVatSolm, outVat) true)
    (hcallback :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let slice :=
        clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)
      let owe0 := UInt256.mul slice price
      let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price
      let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmPriceSolm I)
        (clipperTakeSalesTabEVMWord evmPriceSolm I)
      let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmPriceSolm I) slice'
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLock evmPriceSolm evmVatSolm I price slice
            owe0 owe0 slice' tabNew lotNew))
        evmVatSolm
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        .reverted)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract v,
            locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let slice :=
    clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I) (clipperTakeAmtWord I)
  have hsrcMul : slice.toNat * price.toNat < UInt256.size := by
    simpa [slice, Nat.mul_comm] using
      clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceSolm)
        (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
        (UInt256.mul slice price).toNat := by
    simpa [slice] using
      clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceSolm)
        (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words
      (I := I) (evmPrice := evmPriceSolm) (price := price) (tab := tab) (lot := lot)
      htab hlot hmul hgt
  have htail :=
    clipperTakeOweGtTabCallbackRevertTailBlock v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨13⟩ ⟨1⟩)
      evmPriceSolm evmVatSolm I price slice hsrcMul hsrcGt hsliceLot hvatCode
      hcallVat (by simpa [slice] using hcallback)
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessTailSourceReverts
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
        (evmPrice := evmPriceSolm) price hmax (by simpa [slice] using htail) hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabCallbackNoCodeRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat : AccountMap}
    {cAVat : Batteries.RBSet AccountAddress compare} {AVat : Substate}
    {evmPriceSolm : EVM.State} {outVat : ByteArray}
    {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price
        (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true)
    (hdataLen : clipperTakeDataLenWord I ≠ ⟨0⟩)
    (hpayload : (clipperTakeDataBytes I).length =
      (clipperTakeDataLenWord I).toNat)
    (hwhoVat : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      clipperTakeVatTarget v)
    (hwhoDog : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)
    (hcallbackNoCode :
      Reasoning.Theory.extCodeSizeWord σVat
        (UInt256.land (clipperTakeWhoWord I) solcAddrMask) = ⟨0⟩)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract v,
            locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨evmVatSolm, hcallVatSolm, hAccountsVat, _, _, _, _, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis
      hevmPriceBlocks hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmPriceSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        (target := clipperTakeVatTarget v) (addr := v.vat)
        hAccountsPost (clipperTakeVatTargetAddress v).symm hvatCodeEvm
  have hdogWord :=
    clipperTakeDogWord_eq_of_accountMapEquiv hAccountsVat hevmVatEnv
  have hdogClean :
      UInt256.land (clipperTakeDogEVMWord evmVatSolm) solcAddrMask =
        clipperTakeDogEVMWord evmVatSolm := by
    rw [← hdogWord]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
  have hwhoDogSolm :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
        UInt256.land (clipperTakeDogEVMWord evmVatSolm) solcAddrMask := by
    simpa [hdogClean, hdogWord] using hwhoDog
  have hguard :=
    clipperEvalTakeCallbackGuardTrue v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceSolm evmVatSolm I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceSolm I)
        (clipperTakeSalesTabEVMWord evmPriceSolm I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price))
      hdataLen hpayload hwhoVat hwhoDogSolm
  have haddr :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
        AccountAddress.ofUInt256
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact clipperTakeAddressOfWord_eq_masked (clipperTakeWhoWord I)
  have hnoCodeSolm :
      (UInt256.ofNat
        ((evmVatSolm.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
        hAccountsVat haddr hcallbackNoCode
  have hcallback :=
    clipperTakeCallbackNoCodeStmt v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceSolm evmVatSolm I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceSolm I)
        (clipperTakeSalesTabEVMWord evmPriceSolm I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price))
      hguard hnoCodeSolm
  exact
    clipperTakeOweGtTabCallbackRevertEquivFromPostWords v
      hcode hwv hdispatch hdec hlockedSolm hstoppedSolmLt husrSolm
      htab hlot hrev hmax hmul hgt hvatCodeSolm hcallVatSolm
      (by simpa using hcallback) hstatus

theorem clipperTakeOweGtTabCallbackSkipVatMoveNoCodeRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat : AccountMap}
    {cAVat : Batteries.RBSet AccountAddress compare} {AVat : Substate}
    {evmPriceSolm : EVM.State} {outVat : ByteArray}
    {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price
        (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true)
    (hskip :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v ∨
      UInt256.land (clipperTakeWhoWord I) solcAddrMask =
        UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)
    (hvatMoveNoCodeEvm :
      Reasoning.Theory.extCodeSizeWord σVat (clipperTakeVatTarget v) = ⟨0⟩)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract v,
            locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨evmVatSolm, hcallVatSolm, hAccountsVat, _, _, _, _, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis
      hevmPriceBlocks hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmPriceSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        (target := clipperTakeVatTarget v) (addr := v.vat)
        hAccountsPost (clipperTakeVatTargetAddress v).symm hvatCodeEvm
  have hcallback :=
    clipperTakeCallbackSkipStmtOfEvmWords v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceSolm evmVatSolm I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceSolm I)
        (clipperTakeSalesTabEVMWord evmPriceSolm I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price))
      hAccountsVat hevmVatEnv hskip
  have hnoVatCodeSolm :
      (UInt256.ofNat
        ((evmVatSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
        (target := clipperTakeVatTarget v) (addr := v.vat)
        hAccountsVat (clipperTakeVatTargetAddress v).symm hvatMoveNoCodeEvm
  exact
    clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveNoCodeRevertEquivFromPostWords
      v hcode hwv hdispatch hdec hlockedSolm hstoppedSolmLt husrSolm
      htab hlot hrev hmax hmul hgt hvatCodeSolm hcallVatSolm
      (by simpa using hcallback) hnoVatCodeSolm hstatus

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem clipperTakeOweGtTabCallbackFailureRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat σCb : AccountMap}
    {cAVat cACb : Batteries.RBSet AccountAddress compare}
    {AVat ACb : Substate} {evmPriceSolm : EVM.State}
    {outVat outCb : ByteArray} {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price
        (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true)
    (hcallCbEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat, substate := AVat, createdAccounts := cAVat }
        (EVM.address
          (AccountAddress.ofNat (UInt256.land who solcAddrMask).toNat))
        "clipperCall" 0
        [.address I.source, .int (Int.ofNat tab.toNat),
          .int (Int.ofNat (tab.div price).toNat), clipperTakeDataValue I]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σCb, substate := ACb, createdAccounts := cACb },
          outCb) true)
    (hdataLen : clipperTakeDataLenWord I ≠ ⟨0⟩)
    (hpayload : (clipperTakeDataBytes I).length =
      (clipperTakeDataLenWord I).toNat)
    (hwhoVat : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      clipperTakeVatTarget v)
    (hwhoDog : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)
    (hcallbackCode :
      Reasoning.Theory.extCodeSizeWord σVat
        (UInt256.land (clipperTakeWhoWord I) solcAddrMask) ≠ ⟨0⟩)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract v,
            locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨evmVatSolm, hcallVatSolm, hAccountsVat, hevmVatSigma0,
      hevmVatCreated, hevmVatGenesis, hevmVatBlocks, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis
      hevmPriceBlocks hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmPriceSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        (target := clipperTakeVatTarget v) (addr := v.vat)
        hAccountsPost (clipperTakeVatTargetAddress v).symm hvatCodeEvm
  have hdogWord :=
    clipperTakeDogWord_eq_of_accountMapEquiv hAccountsVat hevmVatEnv
  have hdogClean :
      UInt256.land (clipperTakeDogEVMWord evmVatSolm) solcAddrMask =
        clipperTakeDogEVMWord evmVatSolm := by
    rw [← hdogWord]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
  have hwhoDogSolm :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
        UInt256.land (clipperTakeDogEVMWord evmVatSolm) solcAddrMask := by
    simpa [hdogClean, hdogWord] using hwhoDog
  have hguard :=
    clipperEvalTakeCallbackGuardTrue v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceSolm evmVatSolm I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceSolm I)
        (clipperTakeSalesTabEVMWord evmPriceSolm I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price))
      hdataLen hpayload hwhoVat hwhoDogSolm
  have haddr :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
        AccountAddress.ofUInt256
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact clipperTakeAddressOfWord_eq_masked (clipperTakeWhoWord I)
  have hcodeSolm :
      0 < (UInt256.ofNat
        ((evmVatSolm.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        hAccountsVat haddr hcallbackCode
  let evmVatEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σVat, substate := AVat, createdAccounts := cAVat }
  have hAccountsState :
      accountMapEquiv evmVatEvm.accountMap evmVatSolm.accountMap := by
    simpa [evmVatEvm] using hAccountsVat
  obtain ⟨σCbSolm, ACbSolm, hcallCbSolmRaw, _hAccountsCb⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmVatSolm) (hcall := hcallCbEvm) hAccountsState
      (by simpa [evmVatEvm, initState] using hevmVatSigma0.symm)
      (by simpa [evmVatEvm, initState] using hevmVatCreated)
      (by simpa [evmVatEvm, initState] using hevmVatGenesis)
      (by simpa [evmVatEvm, initState] using hevmVatBlocks)
      (by simpa [evmVatEvm, initState] using hevmVatEnv)
  let evmCbSolm : EVM.State :=
    { evmVatSolm with
      accountMap := σCbSolm
      substate := ACbSolm
      createdAccounts := cACb }
  have hcallCbSolm :
      typedCallViaEVM (config v) evmVatSolm
        (EVM.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat))
        "clipperCall" 0
        [.address evmVatSolm.executionEnv.source,
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat),
          clipperTakeDataValue I]
        (false, evmCbSolm, outCb) true := by
    have hwhoClean : UInt256.land who solcAddrMask = who := by
      rw [hwho]
      exact solcAddrMask_clean
        (solcAddrMask_result_canonical (clipperTakeWhoWord I))
    have htargetAddr :
        AccountAddress.ofNat (UInt256.land who solcAddrMask).toNat =
          AccountAddress.ofNat (clipperTakeWhoWord I).toNat := by
      rw [hwhoClean, hwho]
      exact (clipperTakeAddressOfWord_eq_masked (clipperTakeWhoWord I)).symm
    rw [htargetAddr] at hcallCbSolmRaw
    simpa only [evmCbSolm, hevmVatEnv, htab] using hcallCbSolmRaw
  have hcallback :=
    clipperTakeCallbackCallFailureStmt v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceSolm evmVatSolm evmCbSolm I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceSolm I)
        (clipperTakeSalesTabEVMWord evmPriceSolm I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price))
      hguard hcodeSolm hcallCbSolm
  exact
    clipperTakeOweGtTabCallbackRevertEquivFromPostWords v
      hcode hwv hdispatch hdec hlockedSolm hstoppedSolmLt husrSolm
      htab hlot hrev hmax hmul hgt hvatCodeSolm hcallVatSolm
      (by simpa using hcallback) hstatus

theorem clipperTakeOweGtTabCallbackSkipVatMoveFailureRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat σMove : AccountMap}
    {cAVat cAMove : Batteries.RBSet AccountAddress compare}
    {AVat AMove : Substate} {evmPriceSolm : EVM.State}
    {outVat outMove : ByteArray} {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true)
    (hskip :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v ∨
      UInt256.land (clipperTakeWhoWord I) solcAddrMask =
        UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)
    (hvatMoveCodeEvm :
      Reasoning.Theory.extCodeSizeWord σVat (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallMoveEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat, createdAccounts := cAVat }
        (EVM.address v.vat) "move" 0
        [.address I.source,
          .address (AccountAddress.ofNat (clipperTakeVowTarget σVat I).toNat),
          .int (Int.ofNat tab.toNat)]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σMove, substate := AMove, createdAccounts := cAMove },
          outMove) true)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk (contract v)
          (clipperTakeLocalsSt evmLock I false price)) evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨evmVatSolm, hcallVatSolm, hAccountsVat, hevmVatSigma0,
      hevmVatCreated, hevmVatGenesis, hevmVatBlocks, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceCreated hevmPriceGenesis
      hevmPriceBlocks hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmPriceSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        (target := clipperTakeVatTarget v) (addr := v.vat)
        hAccountsPost (clipperTakeVatTargetAddress v).symm hvatCodeEvm
  have hcallback :=
    clipperTakeCallbackSkipStmtOfEvmWords v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceSolm evmVatSolm I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceSolm I)
        (clipperTakeSalesTabEVMWord evmPriceSolm I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price))
      hAccountsVat hevmVatEnv hskip
  have hvatMoveCodeSolm :
      0 < (UInt256.ofNat
        ((evmVatSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        (target := clipperTakeVatTarget v) (addr := v.vat)
        hAccountsVat (clipperTakeVatTargetAddress v).symm hvatMoveCodeEvm
  have hvow : clipperTakeVowTarget σVat I =
      clipperTakeVowEVMWord evmVatSolm := by
    have hslot := accountMapEquiv_storage_findD
      hAccountsVat I.codeOwner ⟨2⟩ ⟨0⟩
    simp [clipperTakeVowTarget, clipperTakeVowEVMWord, hevmVatEnv,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hslot]
  let evmVatEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σVat, createdAccounts := cAVat }
  have hAccountsMoveState :
      accountMapEquiv evmVatEvm.accountMap evmVatSolm.accountMap := by
    simpa [evmVatEvm] using hAccountsVat
  obtain ⟨σMoveSolm, AMoveSolm, hcallMoveSolmRaw, _hAccountsMove⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmVatSolm) (hcall := hcallMoveEvm)
      hAccountsMoveState
      (by simpa [evmVatEvm, initState] using hevmVatSigma0.symm)
      (by simp [evmVatEvm, initState, hevmVatCreated])
      (by simpa [evmVatEvm, initState] using hevmVatGenesis)
      (by simpa [evmVatEvm, initState] using hevmVatBlocks)
      (by simpa [evmVatEvm, initState] using hevmVatEnv)
  let evmMoveSolm : EVM.State :=
    { evmVatSolm with
      accountMap := σMoveSolm
      substate := AMoveSolm
      createdAccounts := cAMove }
  have hcallMoveSolm :
      typedCallViaEVM (config v) evmVatSolm (EVM.address v.vat) "move" 0
        [.address evmVatSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (clipperTakeVowEVMWord evmVatSolm).toNat),
          .int (Int.ofNat
            (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat)]
        (false, evmMoveSolm, outMove) true := by
    simpa [evmMoveSolm, htab, hvow, hevmVatEnv] using hcallMoveSolmRaw
  exact
    clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveCallFailureRevertEquivFromPostWords
      v hcode hwv hdispatch hdec hlockedSolm hstoppedSolmLt husrSolm
      htab hlot hrev hmax hmul hgt hvatCodeSolm hcallVatSolm
      (by simpa using hcallback) hvatMoveCodeSolm hcallMoveSolm hstatus

end Benchmarks.Dss.Clipper
