import Benchmarks.Dss.Clipper.TakeOweVatFlux

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeOweGtTabVatFluxSuccessVatMoveNoCodeTailBlockOfCallbackFalse
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
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
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
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
              slice' tabNew lotNew))
          evmVat))
    (hnoVatCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
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
  have hmove :
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
    simpa [fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeVatMoveNoCodeBlockOfCallbackFalse v evmLoc evmRead evmVat I price
        slice owe0 owe0 slice' tabNew lotNew hcallback hnoVatCode
  simpa [sliceFrame, fluxFrame, List.append_assoc] using execBlockAppendOk hflux hmove

theorem clipperTakeOweGtTabVatFluxSuccessVatMoveCallFailureTailBlockOfCallbackFalse
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice : UInt256) {outVat outMove : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
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
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
              slice' tabNew lotNew))
          evmVat))
    (hvatMoveCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (false, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
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
  have hmove :
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
    simpa [fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeVatMoveCallFailureBlockOfCallbackFalse v evmLoc evmRead evmVat evmMove I
        price slice owe0 owe0 slice' tabNew lotNew hcallback hvatMoveCode hcallMove
  simpa [sliceFrame, fluxFrame, List.append_assoc] using execBlockAppendOk hflux hmove

theorem clipperTakeOweGtTabVatFluxSuccessTailSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (htail :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsSlice evmLock evmPrice I false price slice))
        evmPrice
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
        .reverted)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body
      .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
  let doneFrame : Frame := { contract := contract v, locals := clipperTakeLocalsDone evmLock I false price }
  let priceFrame : Frame := { contract := contract v, locals := clipperTakeLocalsPrice evmLock I false price }
  let lotFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsLot evmLock evmPrice I false price }
  let tabFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsTab evmLock evmPrice I false price }
  let sliceFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? (config v) priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt (config v) priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt (config v) lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt (config v) tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeSolm :=
          { contract := contract v, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I) })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction v)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail' :
      ExecBlock (config v) sliceFrame evmPrice
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
    simpa [evm0, evmLock, lot, slice, sliceFrame] using htail
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, clipperTakePostOweFluxStmts, List.append_assoc] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal hletDone ?_
        refine ExecBlock.consNormal hletPrice ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hmaxEval) ?_
        refine ExecBlock.consNormal hletLot ?_
        refine ExecBlock.consNormal hletTab ?_
        refine ExecBlock.consNormal hminCall ?_
        exact execBlockAppendReverted htail')
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmVat : EVM.State} {outVat : ByteArray} (price : UInt256)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
        (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmPrice I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
            (clipperTakeAmtWord I))
          price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPrice I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
        (true, evmVat, outVat) true)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hnoVatCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
  let doneFrame : Frame := { contract := contract v, locals := clipperTakeLocalsDone evmLock I false price }
  let priceFrame : Frame := { contract := contract v, locals := clipperTakeLocalsPrice evmLock I false price }
  let lotFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsLot evmLock evmPrice I false price }
  let tabFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsTab evmLock evmPrice I false price }
  let sliceFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? (config v) priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt (config v) priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt (config v) lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt (config v) tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeSolm :=
          { contract := contract v, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I) })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction v)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail :
      ExecBlock (config v) sliceFrame evmPrice
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
    simpa [sliceFrame, slice, lot] using
      clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeTailBlock v evmLock
        evmPrice evmVat I price slice hmul hgt hsliceLot hvatCode hcallVat hdataLen
        hnoVatCode
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, clipperTakePostOweFluxStmts, List.append_assoc] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal hletDone ?_
        refine ExecBlock.consNormal hletPrice ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hmaxEval) ?_
        refine ExecBlock.consNormal hletLot ?_
        refine ExecBlock.consNormal hletTab ?_
        refine ExecBlock.consNormal hminCall ?_
        exact execBlockAppendReverted htail)
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmVat evmMove : EVM.State} {outVat outMove : ByteArray}
    (price : UInt256)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
        (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmPrice I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
            (clipperTakeAmtWord I))
          price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPrice I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
        (true, evmVat, outVat) true)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatMoveCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (false, evmMove, outMove) true)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body
      .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
  let doneFrame : Frame := { contract := contract v, locals := clipperTakeLocalsDone evmLock I false price }
  let priceFrame : Frame := { contract := contract v, locals := clipperTakeLocalsPrice evmLock I false price }
  let lotFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsLot evmLock evmPrice I false price }
  let tabFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsTab evmLock evmPrice I false price }
  let sliceFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? (config v) priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt (config v) priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt (config v) lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt (config v) tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeSolm :=
          { contract := contract v, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I) })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction v)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail :
      ExecBlock (config v) sliceFrame evmPrice
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
    simpa [sliceFrame, slice, lot] using
      clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureTailBlock v
        evmLock evmPrice evmVat evmMove I price slice hmul hgt hsliceLot hvatCode
        hcallVat hdataLen hvatMoveCode hcallMove
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, clipperTakePostOweFluxStmts, List.append_assoc] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal hletDone ?_
        refine ExecBlock.consNormal hletPrice ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hmaxEval) ?_
        refine ExecBlock.consNormal hletLot ?_
        refine ExecBlock.consNormal hletTab ?_
        refine ExecBlock.consNormal hminCall ?_
        exact execBlockAppendReverted htail)
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeRevertEquivFromPostWords
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
    (hrev : RDrev code (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hnoVatCode :
      (UInt256.ofNat
        ((evmVatSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceSolm)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeSourceReverts
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
        (evmPrice := evmPriceSolm) (evmVat := evmVatSolm) (outVat := outVat) price
        hmax hsrcMul hsrcGt hsliceLot hvatCode hcallVat hdataLen hnoVatCode hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat : AccountMap} {cAVat : Batteries.RBSet AccountAddress compare}
    {AVat : Substate} {evmPriceSolm : EVM.State}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {zVat : Bool}
    {R : List UInt256} {mem outVat : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
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
    (rd :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw outVat (cAVat, σVat) k C)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (zVat,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hwho : who = (clipperTakeWhoWord I).land solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdataLenStack : dataLen = ⟨0⟩)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hvatMoveNoCodeEvm :
      Reasoning.Theory.extCodeSizeWord σVat (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  subst zVat
  subst aw
  have hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCode (v := v)
      (hpatch := hpatch) (by simpa using rd) rfl rfl hdataLenStack hmem hread64
      hvatMoveNoCodeEvm (by omega)
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          ((evmPriceSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        (σ := σPost) (τ := σPostSolm) (target := clipperTakeVatTarget v)
        (addr := v.vat) hAccountsPost (clipperTakeVatTargetAddress v).symm hvatCodeEvm
  let evmPostEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σPost, createdAccounts := cAPost }
  have hAccountsState : accountMapEquiv evmPostEvm.accountMap evmPriceSolm.accountMap := by
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
  have hcallVatSolm :
      typedCallViaEVM (config v) evmPriceSolm (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceSolm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat)]
        (true, evmVatSolm, outVat) true := by
    simpa [evmVatSolm, hevmPriceEnv, htab, hwho] using hcallVatSolmRaw
  have hvatMoveNoCodeSolm :
      (UInt256.ofNat
        ((evmVatSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evmVatSolm, State.lookupAccount] using
      clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
        (σ := σVat) (τ := σVatSolm) (target := clipperTakeVatTarget v)
        (addr := v.vat) hAccountsVat (clipperTakeVatTargetAddress v).symm
        hvatMoveNoCodeEvm
  exact
    clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeRevertEquivFromPostWords
      (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (evmPriceSolm := evmPriceSolm) (evmVatSolm := evmVatSolm)
      (outVat := outVat) (price := price) (tab := tab) (lot := lot)
      hcode hwv hdispatch hdec hlockedSolm hstoppedSolmLt husrSolm htab hlot hrev
      hmax hmul hgt hvatCodeSolm hcallVatSolm hdataLen hvatMoveNoCodeSolm hstatus

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat : AccountMap} {cAVat : Batteries.RBSet AccountAddress compare}
    {AVat : Substate} {evmPriceSolm : EVM.State}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {zVat : Bool}
    {R : List UInt256} {mem outVat : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
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
    (rd :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw outVat (cAVat, σVat) k C)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (zVat,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true)
    {σMove : AccountMap} {cAMove : Batteries.RBSet AccountAddress compare}
    {AMove : Substate} {zMove : Bool} {outMove : ByteArray} {kMove CMove : ℕ}
    (rdMove :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask ::
            tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
              tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
                id :: R)
        (outMove.write 0 (clipperTakeVatMoveCalldataMem σVat I tab mem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outMove.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outMove (cAMove, σMove) kMove CMove)
    (hcallMoveEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat, createdAccounts := cAVat }
        (EVM.address v.vat) "move" 0
        [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σVat I).toNat),
          .int (Int.ofNat tab.toNat)]
        (zMove,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σMove, substate := AMove, createdAccounts := cAMove },
          outMove) true)
    (hzMove : zMove = false)
    (houtMove : outMove.size < UInt256.size)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hwho : who = (clipperTakeWhoWord I).land solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatMoveCodeEvm :
      Reasoning.Theory.extCodeSizeWord σVat (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  subst zVat
  subst aw
  exact by
    have hrev :
        RDrev code (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
      RD.clipperTakeOweGtTabVatMoveCallFailure (v := v) (hpatch := hpatch)
        (by simpa using rdMove) hzMove houtMove hov
    have hvatCodeSolm :
        0 <
          (UInt256.ofNat
            ((evmPriceSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount, hevmPriceAccounts] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          (σ := σPost) (τ := σPostSolm) (target := clipperTakeVatTarget v)
          (addr := v.vat) hAccountsPost (clipperTakeVatTargetAddress v).symm hvatCodeEvm
    let evmPostEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σPost, createdAccounts := cAPost }
    have hAccountsState : accountMapEquiv evmPostEvm.accountMap evmPriceSolm.accountMap := by
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
    have hcallVatSolm :
        typedCallViaEVM (config v) evmPriceSolm (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmPriceSolm.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat
              (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat)]
          (true, evmVatSolm, outVat) true := by
      simpa [evmVatSolm, hevmPriceEnv, htab, hwho] using hcallVatSolmRaw
    have hvatMoveCodeSolm :
        0 <
          (UInt256.ofNat
            ((evmVatSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [evmVatSolm, State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          (σ := σVat) (τ := σVatSolm) (target := clipperTakeVatTarget v)
          (addr := v.vat) hAccountsVat (clipperTakeVatTargetAddress v).symm
          hvatMoveCodeEvm
    have hvow :
        clipperTakeVowTarget σVat I = clipperTakeVowEVMWord evmVatSolm := by
      have hslot := accountMapEquiv_storage_findD hAccountsVat I.codeOwner ⟨2⟩ ⟨0⟩
      simp [clipperTakeVowTarget, clipperTakeVowEVMWord, evmVatSolm, hevmPriceEnv,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord, hslot]
    let evmVatEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVat, createdAccounts := cAVat }
    have hAccountsMoveState : accountMapEquiv evmVatEvm.accountMap evmVatSolm.accountMap := by
      simpa [evmVatEvm, evmVatSolm] using hAccountsVat
    obtain ⟨σMoveSolm, AMoveSolm, hcallMoveSolmRaw, _hAccountsMove⟩ :=
      typedCallViaEVM_accountMapEquiv_noSubstate
        (evm_solm := evmVatSolm) (hcall := hcallMoveEvm) hAccountsMoveState
        (by simpa [evmVatEvm, evmVatSolm, initState] using hevmPriceSigma0.symm)
        (by simp [evmVatSolm])
        (by simpa [evmVatEvm, evmVatSolm, initState] using hevmPriceGenesis)
        (by simpa [evmVatEvm, evmVatSolm, initState] using hevmPriceBlocks)
        (by simpa [evmVatEvm, evmVatSolm, initState] using hevmPriceEnv)
    let evmMoveSolm : EVM.State :=
      { evmVatSolm with
        accountMap := σMoveSolm
        substate := AMoveSolm
        createdAccounts := cAMove }
    have hcallMoveSolm :
        typedCallViaEVM (config v) evmVatSolm (EVM.address v.vat) "move" 0
          [.address evmVatSolm.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVatSolm).toNat),
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat)]
          (false, evmMoveSolm, outMove) true := by
      simpa [evmMoveSolm, evmVatSolm, hevmPriceEnv, hvow, htab, hzMove] using
        hcallMoveSolmRaw
    have hsrcMul :
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
            (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
      clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceSolm)
        (price := price) (lot := lot) hlot hmul
    have hsrcGt :
        (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
          (UInt256.mul
            (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
              (clipperTakeAmtWord I))
            price).toNat :=
      clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceSolm)
        (price := price) (tab := tab) (lot := lot) htab hlot hgt
    have hsliceLot :
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
          (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat :=
      clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceSolm)
        (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
    have hbody :
        ExecTransitionBody (config v) (contract v)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperTakeStore I) (takeTransition v).body .reverted := by
      simpa using
        (clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureSourceReverts
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
          (evmPrice := evmPriceSolm) (evmVat := evmVatSolm) (evmMove := evmMoveSolm)
          (outVat := outVat) (outMove := outMove) price hmax hsrcMul hsrcGt hsliceLot
          hvatCodeSolm hcallVatSolm hdataLen hvatMoveCodeSolm hcallMoveSolm hstatus)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveNoCodeRevertEquivFromPostWords
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
    (hrev : RDrev code (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
        clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I) (clipperTakeAmtWord I)
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
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLock evmPriceSolm evmVatSolm I price slice
              owe0 owe0 slice' tabNew lotNew))
          evmVatSolm))
    (hnoVatCode :
      (UInt256.ofNat
        ((evmVatSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceSolm)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have htail :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPriceSolm I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsSlice evmLock evmPriceSolm I false price slice))
        evmPriceSolm
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
    dsimp only
    exact
      clipperTakeOweGtTabVatFluxSuccessVatMoveNoCodeTailBlockOfCallbackFalse v
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩)
        evmPriceSolm evmVatSolm I price
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I) (clipperTakeAmtWord I))
        hsrcMul hsrcGt hsliceLot hvatCode hcallVat hcallback hnoVatCode
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessTailSourceReverts
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
        (evmPrice := evmPriceSolm) price hmax htail hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveCallFailureRevertEquivFromPostWords
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
    {evmPriceSolm evmVatSolm evmMoveSolm : EVM.State} {outVat outMove : ByteArray}
    {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hrev : RDrev code (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
        clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I) (clipperTakeAmtWord I)
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
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLock evmPriceSolm evmVatSolm I price slice
              owe0 owe0 slice' tabNew lotNew))
          evmVatSolm))
    (hvatMoveCode :
      0 <
        (UInt256.ofNat
          ((evmVatSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVatSolm (EVM.address v.vat) "move" 0
        [.address evmVatSolm.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVatSolm).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat)]
        (false, evmMoveSolm, outMove) true)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceSolm)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have htail :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPriceSolm I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsSlice evmLock evmPriceSolm I false price slice))
        evmPriceSolm
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
    dsimp only
    exact
      clipperTakeOweGtTabVatFluxSuccessVatMoveCallFailureTailBlockOfCallbackFalse v
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩)
        evmPriceSolm evmVatSolm evmMoveSolm I price
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I) (clipperTakeAmtWord I))
        hsrcMul hsrcGt hsliceLot hvatCode hcallVat hcallback hvatMoveCode hcallMove
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessTailSourceReverts
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
        (evmPrice := evmPriceSolm) price hmax htail hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureRevertEquivFromPostWords
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
    {evmPriceSolm evmVatSolm evmMoveSolm : EVM.State} {outVat outMove : ByteArray}
    {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hrev : RDrev code (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatMoveCode :
      0 <
        (UInt256.ofNat
          ((evmVatSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVatSolm (EVM.address v.vat) "move" 0
        [.address evmVatSolm.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVatSolm).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat)]
        (false, evmMoveSolm, outMove) true)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceSolm)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceSolm)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureSourceReverts
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
        (evmPrice := evmPriceSolm) (evmVat := evmVatSolm) (evmMove := evmMoveSolm)
        (outVat := outVat) (outMove := outMove) price hmax hsrcMul hsrcGt hsliceLot
        hvatCode hcallVat hdataLen hvatMoveCode hcallMove hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

abbrev clipperTakeAfterFluxStmts (v : ClipperImmutables) : List Stmt :=
  [ .letDecl "dog_" (some addr) (.storage dogRef),
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
      [sender, .storage vowRef, .var "owe"] "_moveRet"

abbrev clipperTakeAfterMoveStmts (v : ClipperImmutables) : List Stmt :=
  [ .ite
      (.binary .eq (.var "lot") (.intLit 0))
      (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
        checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "digsAmt"] "_digsRet")
      (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
        [ilkExpr v, .var "owe"] "_digsRet"),
    .ite
      (.binary .eq (.var "lot") (.intLit 0))
      [ .internalCall "_remove" [.var "id"] "_removeRet" ]
      [ .ite
          (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
    .assign .storage lockedRef (.intLit 0) ]

abbrev clipperTakeAfterSliceStmts (v : ClipperImmutables) : List Stmt :=
  checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
    [ .letDecl "owe" (some uint256) (.var "owe0"),
      clipperTakeOweAdjustmentStmt ] ++
    clipperTakePostOweFluxStmts v ++
    clipperTakeAfterFluxStmts v ++
    clipperTakeAfterMoveStmts v

theorem clipperTakeSourcePrefixToSlice
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmPrice : EVM.State}
    {result : ExecResult} (v : ClipperImmutables) (price : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v,
               locals := clipperTakeLocalsSt evmLock I false price } evmPrice))
    (htail :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock (config v)
        { contract := contract v,
          locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
        evmPrice (clipperTakeAfterSliceStmts v) result) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock (config v) { contract := contract v, locals := locals } evm0
      (takeTransition v).body result := by
  intro locals evm0
  let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
  let doneFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsDone evmLock I false price }
  let priceFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsPrice evmLock I false price }
  let lotFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsLot evmLock evmPrice I false price }
  let tabFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsTab evmLock evmPrice I false price }
  let sliceFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address
          (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? (config v) priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using
      clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt (config v) priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt (config v) lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, clipperTakeSalesTabEVMWord, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat))
        (by simpa [lotFrame] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt (config v) tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := tabFrame) (evm := evmPrice)
        (calleeEvm := evmPrice) (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeSolm :=
          { contract := contract v,
            locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I) })
        (value := some
          [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction v)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail' :
      ExecBlock (config v) sliceFrame evmPrice (clipperTakeAfterSliceStmts v)
        result := by
    simpa [evm0, evmLock, lot, slice, sliceFrame] using htail
  simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
    clipperTakeAfterSliceStmts, clipperTakeAfterFluxStmts,
    clipperTakeAfterMoveStmts, clipperTakeOweAdjustmentStmt,
    clipperTakePostOweFluxStmts, checkedMulUintInto, List.append_assoc] using
    (by
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
      refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
      refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
      refine ExecBlock.consNormal hletUsr ?_
      refine ExecBlock.consNormal hletTic ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
      refine ExecBlock.consNormal hstatus' ?_
      refine ExecBlock.consNormal hletDone ?_
      refine ExecBlock.consNormal hletPrice ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue hmaxEval) ?_
      refine ExecBlock.consNormal hletLot ?_
      refine ExecBlock.consNormal hletTab ?_
      refine ExecBlock.consNormal hminCall ?_
      exact htail')

theorem clipperTakeSourceRevertsOfAfterSlice
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmPrice : EVM.State}
    (v : ClipperImmutables) (price : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v,
               locals := clipperTakeLocalsSt evmLock I false price } evmPrice))
    (htail :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock (config v)
        { contract := contract v,
          locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
        evmPrice (clipperTakeAfterSliceStmts v) .reverted) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) (takeTransition v).body .reverted := by
  have hblock := clipperTakeSourcePrefixToSlice
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (evmPrice := evmPrice) (result := .reverted)
    v price hwv hlocked hstopped husr hmax hstatus htail
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert
    (by simpa using hblock)

theorem clipperTakeSourceOkOfAfterSlice
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmPrice evmFinal : EVM.State}
    {finalFrame : Frame} (v : ClipperImmutables) (price : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v,
               locals := clipperTakeLocalsSt evmLock I false price } evmPrice))
    (htail :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock (config v)
        { contract := contract v,
          locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
        evmPrice (clipperTakeAfterSliceStmts v) (.ok finalFrame evmFinal)) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) (takeTransition v).body
      (.returned finalFrame evmFinal none) := by
  have hblock := clipperTakeSourcePrefixToSlice
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (evmPrice := evmPrice)
    (result := .ok finalFrame evmFinal)
    v price hwv hlocked hstopped husr hmax hstatus htail
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK
    (by simpa using hblock)

end Benchmarks.Dss.Clipper
