import Benchmarks.Dss.Clipper.TakeCallbackSource
import Benchmarks.Dss.Clipper.TakeOweVatMoveSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- Synchronize the successful `vat.flux` call once, before splitting on the
   optional callback.  The callback, `vat.move`, and later dog calls all need
   the same post-flux account-map equality, so keeping it existentially packaged
   avoids repeating the state reconstruction in every callback outcome. -/
theorem clipperTakeVatFluxCallSyncFromPostAccounts
    (v : ClipperImmutables)
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat : AccountMap}
    {AVat : Substate}
    {evmPriceStele : EVM.State} {outVat : ByteArray}
    {price tab who : UInt256}
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hcallVatEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat, substate := AVat }, outVat) true) :
    ∃ evmVatStele : EVM.State,
      typedCallViaEVM fork config evmPriceStele (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceStele.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat)]
        (true, evmVatStele, outVat) true ∧
      σVat = evmVatStele.accountMap ∧
      evmVatStele.σ₀ = σ₀ ∧
      evmVatStele.executionEnv = I := by
  let evmPostEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with accountMap := σPost }
  have hAccountsState : evmPostEvm.accountMap = evmPriceStele.accountMap := by
    simpa [evmPostEvm, hevmPriceAccounts] using hAccountsPost
  obtain ⟨σVatStele, AVatStele, hcallVatSteleRaw, hAccountsVat⟩ :=
    Reasoning.Theory.typedCallViaEVM_sameInputs
      (evm_stele := evmPriceStele) (hcall := hcallVatEvm) hAccountsState
      (by simpa [evmPostEvm, initState] using hevmPriceSigma0.symm)
      (by simpa [evmPostEvm, initState] using hevmPriceEnv.symm)
  let evmVatStele : EVM.State :=
    { evmPriceStele with accountMap := σVatStele, substate := AVatStele }
  refine ⟨evmVatStele, ?_, ?_, ?_, ?_⟩
  · simpa [evmVatStele, hevmPriceEnv, htab, hwho] using hcallVatSteleRaw
  · simpa [evmVatStele] using hAccountsVat
  · simp [evmVatStele, hevmPriceSigma0]
  · simp [evmVatStele, hevmPriceEnv]

theorem clipperTakeDogWord_eq
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : σ = evm.accountMap)
    (henv : evm.executionEnv = I) :
    UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask =
      clipperTakeDogEVMWord evm := by
  subst σ
  subst I
  simp [clipperTakeDogEVMWord, solcSlotWord, Stele.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

theorem clipperTakeCallbackSkipStmtOfEvmWords
    (v : ClipperImmutables) (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256)
    {σ : AccountMap}
    (hAccounts : Eq σ evmVat.accountMap)
    (henv : evmVat.executionEnv = I)
    (hskip :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v ∨
      UInt256.land (clipperTakeWhoWord I) solcAddrMask =
        UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask) :
    ExecStmt fork config
      (Frame.mk contract (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew) (immStore v))
      evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok
        (Frame.mk contract (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew) (immStore v))
        evmVat) := by
  rcases hskip with hvat | hdog
  · exact clipperTakeCallbackSkipWhoVatStmt v evmLoc evmRead evmVat I
      price slice owe0 owe slice' tabNew lotNew hvat
  · have hdogWord :=
      clipperTakeDogWord_eq hAccounts henv
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
      typedCallViaEVM fork config evmRead (EVM.address v.vat) "flux" 0
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
      ExecStmt fork config
        (Frame.mk contract (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
            slice' tabNew lotNew) (immStore v))
        evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") vatExpr)
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        .reverted) :
    ExecBlock fork config
      (Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts ++
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") vatExpr)
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet"))
      .reverted := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v)
  let fluxFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew) (immStore v)
  let dogFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
        slice' tabNew lotNew) (immStore v)
  have hflux :
      ExecBlock fork config sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++
          clipperTakePostOweFluxStmts)
        (.ok fluxFrame evmVat) := by
    simpa [sliceFrame, fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeOweGtTabVatFluxCallSuccessTailBlock v evmLoc evmRead evmVat I price
        slice hmul hgt hsliceLot hvatCode hcallVat
  have hletDog :
      ExecStmt fork config fluxFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [fluxFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config) (stele := fluxFrame) (evm := evmVat) (name := "dog_")
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
      ExecBlock fork config fluxFrame evmVat
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") vatExpr)
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    simpa [dogFrame, owe0, slice', tabNew, lotNew] using
      ExecBlock.consNormal hletDog (ExecBlock.consRevert hcallback)
  simpa [sliceFrame, fluxFrame, List.append_assoc] using
    execBlockAppendOk hflux hafterFlux

theorem clipperTakeOweGtTabCallbackRevertEquivFromPostWords
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (List.map Param.name takeTransition.params)
        (transitionSignature takeTransition).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedStele : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstoppedSteleLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrStele :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPriceStele evmVatStele : EVM.State} {outVat : ByteArray}
    {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
    (hrev : RDrev fork code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat <
      UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmPriceStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM fork config evmPriceStele (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceStele.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat)]
        (true, evmVatStele, outVat) true)
    (hcallback :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let slice :=
        clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)
      let owe0 := UInt256.mul slice price
      let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price
      let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I)
      let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I) slice'
      ExecStmt fork config
        (Frame.mk contract (clipperTakeLocalsDogLoaded evmLock evmPriceStele evmVatStele I price slice
            owe0 owe0 slice' tabNew lotNew) (immStore v))
        evmVatStele
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") vatExpr)
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        .reverted)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract,
            locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  let slice :=
    clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I) (clipperTakeAmtWord I)
  have hsrcMul : slice.toNat * price.toNat < UInt256.size := by
    simpa [slice, Nat.mul_comm] using
      clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceStele)
        (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceStele I).toNat <
        (UInt256.mul slice price).toNat := by
    simpa [slice] using
      clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceStele)
        (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceStele I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words
      (I := I) (evmPrice := evmPriceStele) (price := price) (tab := tab) (lot := lot)
      htab hlot hmul hgt
  have htail :=
    clipperTakeOweGtTabCallbackRevertTailBlock v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele I price slice hsrcMul hsrcGt hsliceLot hvatCode
      hcallVat (by simpa [slice] using hcallback)
  have hbody :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessTailSourceReverts (fork := fork) (hperm := by assumption)
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedStele hstoppedSteleLt husrStele
        (evmPrice := evmPriceStele) price hmax (by simpa [slice] using htail) hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabCallbackNoCodeRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat : AccountMap}
    {AVat : Substate}
    {evmPriceStele : EVM.State} {outVat : ByteArray}
    {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (List.map Param.name takeTransition.params)
        (transitionSignature takeTransition).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedStele : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstoppedSteleLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrStele :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev fork code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
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
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
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
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract,
            locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract
      σ σ₀ g A I (immStore v) := by
  obtain ⟨evmVatStele, hcallVatStele, hAccountsVat, hevmVatSigma0, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeStele :
      0 < (UInt256.ofNat
        ((evmPriceStele.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (target := clipperTakeVatTarget v) (addr := v.vat)
        (clipperTakeVatTargetAddress v).symm
        (by simpa only [← hAccountsPost] using hvatCodeEvm)
  have hdogWord :=
    clipperTakeDogWord_eq hAccountsVat hevmVatEnv
  have hdogClean :
      UInt256.land (clipperTakeDogEVMWord evmVatStele) solcAddrMask =
        clipperTakeDogEVMWord evmVatStele := by
    rw [← hdogWord]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
  have hwhoDogStele :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
        UInt256.land (clipperTakeDogEVMWord evmVatStele) solcAddrMask := by
    simpa [hdogClean, hdogWord] using hwhoDog
  have hguard :=
    clipperEvalTakeCallbackGuardTrue v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hdataLen hpayload hwhoVat hwhoDogStele
  have haddr :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
        AccountAddress.ofUInt256
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact addressOfNat_eq_of_masked_word (clipperTakeWhoWord I)
  have hnoCodeStele :
      (UInt256.ofNat
        ((evmVatStele.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      extCodeSizeWord_zero_lookup_code_zero haddr
        (by simpa only [← hAccountsVat] using hcallbackNoCode)
  have hcallback :=
    clipperTakeCallbackNoCodeStmt (fork := fork) v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hguard hnoCodeStele
  exact
    clipperTakeOweGtTabCallbackRevertEquivFromPostWords (hperm := by assumption) v
      hcode hwv hdispatch hdec hlockedStele hstoppedSteleLt husrStele
      htab hlot hrev hmax hmul hgt hvatCodeStele hcallVatStele
      (by simpa using hcallback) hstatus

theorem clipperTakeOweGtTabCallbackSkipVatMoveNoCodeRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat : AccountMap}
    {AVat : Substate}
    {evmPriceStele : EVM.State} {outVat : ByteArray}
    {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (List.map Param.name takeTransition.params)
        (transitionSignature takeTransition).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedStele : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstoppedSteleLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrStele :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev fork code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
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
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
          outVat) true)
    (hskip :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v ∨
      UInt256.land (clipperTakeWhoWord I) solcAddrMask =
        UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)
    (hvatMoveNoCodeEvm :
      Reasoning.Theory.extCodeSizeWord σVat (clipperTakeVatTarget v) = ⟨0⟩)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract,
            locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract
      σ σ₀ g A I (immStore v) := by
  obtain ⟨evmVatStele, hcallVatStele, hAccountsVat, hevmVatSigma0, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeStele :
      0 < (UInt256.ofNat
        ((evmPriceStele.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (target := clipperTakeVatTarget v) (addr := v.vat)
        (clipperTakeVatTargetAddress v).symm
        (by simpa only [← hAccountsPost] using hvatCodeEvm)
  have hcallback :=
    clipperTakeCallbackSkipStmtOfEvmWords (fork := fork) v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hAccountsVat hevmVatEnv hskip
  have hnoVatCodeStele :
      (UInt256.ofNat
        ((evmVatStele.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      extCodeSizeWord_zero_lookup_code_zero
        (target := clipperTakeVatTarget v) (addr := v.vat)
        (clipperTakeVatTargetAddress v).symm
        (by simpa only [← hAccountsVat] using hvatMoveNoCodeEvm)
  exact
    clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveNoCodeRevertEquivFromPostWords (hperm := by assumption)
      v hcode hwv hdispatch hdec hlockedStele hstoppedSteleLt husrStele
      htab hlot hrev hmax hmul hgt hvatCodeStele hcallVatStele
      (by simpa using hcallback) hnoVatCodeStele hstatus

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem clipperTakeOweGtTabCallbackFailureRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat σCb : AccountMap}

    {AVat ACb : Substate} {evmPriceStele : EVM.State}
    {outVat outCb : ByteArray} {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (List.map Param.name takeTransition.params)
        (transitionSignature takeTransition).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedStele : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstoppedSteleLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrStele :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev fork code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
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
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
          outVat) true)
    (hcallCbEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat, substate := AVat }
        (EVM.address
          (AccountAddress.ofNat (UInt256.land who solcAddrMask).toNat))
        "clipperCall" 0
        [.address I.source, .int (Int.ofNat tab.toNat),
          .int (Int.ofNat (tab.div price).toNat), clipperTakeDataValue I]
        (false,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σCb, substate := ACb },
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
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract,
            locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract
      σ σ₀ g A I (immStore v) := by
  obtain ⟨evmVatStele, hcallVatStele, hAccountsVat, hevmVatSigma0, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeStele :
      0 < (UInt256.ofNat
        ((evmPriceStele.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (target := clipperTakeVatTarget v) (addr := v.vat)
        (clipperTakeVatTargetAddress v).symm
        (by simpa only [← hAccountsPost] using hvatCodeEvm)
  have hdogWord :=
    clipperTakeDogWord_eq hAccountsVat hevmVatEnv
  have hdogClean :
      UInt256.land (clipperTakeDogEVMWord evmVatStele) solcAddrMask =
        clipperTakeDogEVMWord evmVatStele := by
    rw [← hdogWord]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
  have hwhoDogStele :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
        UInt256.land (clipperTakeDogEVMWord evmVatStele) solcAddrMask := by
    simpa [hdogClean, hdogWord] using hwhoDog
  have hguard :=
    clipperEvalTakeCallbackGuardTrue v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hdataLen hpayload hwhoVat hwhoDogStele
  have haddr :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
        AccountAddress.ofUInt256
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact addressOfNat_eq_of_masked_word (clipperTakeWhoWord I)
  have hcodeStele :
      0 < (UInt256.ofNat
        ((evmVatStele.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        haddr
        (by simpa only [← hAccountsVat] using hcallbackCode)
  let evmVatEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σVat, substate := AVat }
  have hAccountsState :
      Eq evmVatEvm.accountMap evmVatStele.accountMap := by
    simpa [evmVatEvm] using hAccountsVat
  obtain ⟨σCbStele, ACbStele, hcallCbSteleRaw, _hAccountsCb⟩ :=
    Reasoning.Theory.typedCallViaEVM_sameInputs
      (evm_stele := evmVatStele) (hcall := hcallCbEvm) hAccountsState
      (by simpa [evmVatEvm, initState] using hevmVatSigma0.symm)
      (by simpa [evmVatEvm, initState] using hevmVatEnv.symm)
  let evmCbStele : EVM.State :=
    { evmVatStele with
      accountMap := σCbStele
      substate := ACbStele
       }
  have hcallCbStele :
      typedCallViaEVM fork config evmVatStele
        (EVM.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat))
        "clipperCall" 0
        [.address evmVatStele.executionEnv.source,
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceStele I).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat),
          clipperTakeDataValue I]
        (false, evmCbStele, outCb) true := by
    have hwhoClean : UInt256.land who solcAddrMask = who := by
      rw [hwho]
      exact solcAddrMask_clean
        (solcAddrMask_result_canonical (clipperTakeWhoWord I))
    have htargetAddr :
        AccountAddress.ofNat (UInt256.land who solcAddrMask).toNat =
          AccountAddress.ofNat (clipperTakeWhoWord I).toNat := by
      rw [hwhoClean, hwho]
      exact (addressOfNat_eq_of_masked_word (clipperTakeWhoWord I)).symm
    rw [htargetAddr] at hcallCbSteleRaw
    simpa only [evmCbStele, hevmVatEnv, htab] using hcallCbSteleRaw
  have hcallback :=
    clipperTakeCallbackCallFailureStmt v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele evmCbStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hguard hcodeStele hcallCbStele
  exact
    clipperTakeOweGtTabCallbackRevertEquivFromPostWords (hperm := by assumption) v
      hcode hwv hdispatch hdec hlockedStele hstoppedSteleLt husrStele
      htab hlot hrev hmax hmul hgt hvatCodeStele hcallVatStele
      (by simpa using hcallback) hstatus

theorem clipperTakeOweGtTabCallbackSkipVatMoveFailureRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat σMove : AccountMap}

    {AVat AMove : Substate} {evmPriceStele : EVM.State}
    {outVat outMove : ByteArray} {price tab lot who : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (List.map Param.name takeTransition.params)
        (transitionSignature takeTransition).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedStele : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstoppedSteleLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrStele :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hrev : RDrev fork code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallVatEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
          outVat) true)
    (hskip :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v ∨
      UInt256.land (clipperTakeWhoWord I) solcAddrMask =
        UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)
    (hvatMoveCodeEvm :
      Reasoning.Theory.extCodeSizeWord σVat (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallMoveEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat }
        (EVM.address v.vat) "move" 0
        [.address I.source,
          .address (AccountAddress.ofNat (clipperTakeVowTarget σVat I).toNat),
          .int (Int.ofNat tab.toNat)]
        (false,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σMove, substate := AMove },
          outMove) true)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk contract (clipperTakeLocalsSt evmLock I false price) (immStore v)) evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract
      σ σ₀ g A I (immStore v) := by
  obtain ⟨evmVatStele, hcallVatStele, hAccountsVat, hevmVatSigma0, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeStele :
      0 < (UInt256.ofNat
        ((evmPriceStele.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (target := clipperTakeVatTarget v) (addr := v.vat)
        (clipperTakeVatTargetAddress v).symm
        (by simpa only [← hAccountsPost] using hvatCodeEvm)
  have hcallback :=
    clipperTakeCallbackSkipStmtOfEvmWords (fork := fork) v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hAccountsVat hevmVatEnv hskip
  have hvatMoveCodeStele :
      0 < (UInt256.ofNat
        ((evmVatStele.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (target := clipperTakeVatTarget v) (addr := v.vat)
        (clipperTakeVatTargetAddress v).symm
        (by simpa only [← hAccountsVat] using hvatMoveCodeEvm)
  have hvow : clipperTakeVowTarget σVat I =
      clipperTakeVowEVMWord evmVatStele := by
    have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccountsVat
    simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, hevmVatEnv,
      Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hslot]
  let evmVatEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σVat }
  have hAccountsMoveState :
      Eq evmVatEvm.accountMap evmVatStele.accountMap := by
    simpa [evmVatEvm] using hAccountsVat
  obtain ⟨σMoveStele, AMoveStele, hcallMoveSteleRaw, _hAccountsMove⟩ :=
    Reasoning.Theory.typedCallViaEVM_sameInputs
      (evm_stele := evmVatStele) (hcall := hcallMoveEvm)
      hAccountsMoveState
      (by simpa [evmVatEvm, initState] using hevmVatSigma0.symm)
      (by simpa [evmVatEvm, initState] using hevmVatEnv.symm)
  let evmMoveStele : EVM.State :=
    { evmVatStele with
      accountMap := σMoveStele
      substate := AMoveStele
       }
  have hcallMoveStele :
      typedCallViaEVM fork config evmVatStele (EVM.address v.vat) "move" 0
        [.address evmVatStele.executionEnv.source,
          .address (AccountAddress.ofNat
            (clipperTakeVowEVMWord evmVatStele).toNat),
          .int (Int.ofNat
            (clipperTakeSalesTabEVMWord evmPriceStele I).toNat)]
        (false, evmMoveStele, outMove) true := by
    simpa [evmMoveStele, htab, hvow, hevmVatEnv] using hcallMoveSteleRaw
  exact
    clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveCallFailureRevertEquivFromPostWords (hperm := by assumption)
      v hcode hwv hdispatch hdec hlockedStele hstoppedSteleLt husrStele
      htab hlot hrev hmax hmul hgt hvatCodeStele hcallVatStele
      (by simpa using hcallback) hvatMoveCodeStele hcallMoveStele hstatus

end Benchmarks.Dss.Clipper
