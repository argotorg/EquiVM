import Benchmarks.Dss.Clipper.TakeOweVatFlux

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
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
        (.ok
          (Frame.mk contract (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
              slice' tabNew lotNew) (immStore v))
          evmVat))
    (hnoVatCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
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
  have hmove :
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
        (.ok
          (Frame.mk contract (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0
              slice' tabNew lotNew) (immStore v))
          evmVat))
    (hvatMoveCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM fork config evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (false, evmMove, outMove) true) :
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
  have hmove :
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
    simpa [fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeVatMoveCallFailureBlockOfCallbackFalse v evmLoc evmRead evmVat evmMove I
        price slice owe0 owe0 slice' tabNew lotNew hcallback hvatMoveCode hcallMove
  simpa [sliceFrame, fluxFrame, List.append_assoc] using execBlockAppendOk hflux hmove

theorem clipperTakeOweGtTabVatFluxSuccessTailSourceReverts
    {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (htail :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock fork config
        (Frame.mk contract (clipperTakeLocalsSlice evmLock evmPrice I false price slice) (immStore v))
        evmPrice
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
        .reverted)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPrice))
    (hperm : I.perm = true) :
    let locals := clipperTakeStore I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody fork config contract evm0 locals takeTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  let usrFrame : Frame := { contract := contract, locals := clipperTakeLocalsUsr evmLock I, immutables := immStore v }
  let ticFrame : Frame := { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
  let stFrame : Frame := { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
  let doneFrame : Frame := { contract := contract, locals := clipperTakeLocalsDone evmLock I false price, immutables := immStore v }
  let priceFrame : Frame := { contract := contract, locals := clipperTakeLocalsPrice evmLock I false price, immutables := immStore v }
  let lotFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsLot evmLock evmPrice I false price, immutables := immStore v }
  let tabFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsTab evmLock evmPrice I false price, immutables := immStore v }
  let sliceFrame : Frame :=
    { contract := contract,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice, immutables := immStore v }
  have hlockedEval :
      evalExpr? config startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Stele.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? config startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? config startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Stele.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt fork config startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config) (stele := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt fork config usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config) (stele := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? config ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt fork config ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt fork config stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config) (stele := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt fork config doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config) (stele := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? config priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? config priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt fork config priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config) (stele := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt fork config lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config) (stele := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt fork config tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeStele :=
          { contract := contract, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I), immutables := immStore v })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail' :
      ExecBlock fork config sliceFrame evmPrice
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
    simpa [evm0, evmLock, lot, slice, sliceFrame] using htail
  have hblock :
      ExecBlock fork config startFrame evm0 takeTransition.body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, clipperTakePostOweFluxStmts, List.append_assoc] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inr hperm) hlockRhs hlockAssign) ?_
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
    {σ σ₀ A I} {g : UInt256}
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
      typedCallViaEVM fork config evmPrice (EVM.address v.vat) "flux" 0
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
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPrice))
    (hperm : I.perm = true) :
    let locals := clipperTakeStore I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody fork config contract evm0 locals takeTransition.body .reverted (immStore v) := by
  intro locals evm0
  let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  let usrFrame : Frame := { contract := contract, locals := clipperTakeLocalsUsr evmLock I, immutables := immStore v }
  let ticFrame : Frame := { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
  let stFrame : Frame := { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
  let doneFrame : Frame := { contract := contract, locals := clipperTakeLocalsDone evmLock I false price, immutables := immStore v }
  let priceFrame : Frame := { contract := contract, locals := clipperTakeLocalsPrice evmLock I false price, immutables := immStore v }
  let lotFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsLot evmLock evmPrice I false price, immutables := immStore v }
  let tabFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsTab evmLock evmPrice I false price, immutables := immStore v }
  let sliceFrame : Frame :=
    { contract := contract,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice, immutables := immStore v }
  have hlockedEval :
      evalExpr? config startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Stele.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? config startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? config startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Stele.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt fork config startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config) (stele := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt fork config usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config) (stele := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? config ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt fork config ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt fork config stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config) (stele := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt fork config doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config) (stele := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? config priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? config priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt fork config priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config) (stele := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt fork config lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config) (stele := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt fork config tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeStele :=
          { contract := contract, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I), immutables := immStore v })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail :
      ExecBlock fork config sliceFrame evmPrice
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
    simpa [sliceFrame, slice, lot] using
      clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeTailBlock v evmLock
        evmPrice evmVat I price slice hmul hgt hsliceLot hvatCode hcallVat hdataLen
        hnoVatCode
  have hblock :
      ExecBlock fork config startFrame evm0 takeTransition.body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, clipperTakePostOweFluxStmts, List.append_assoc] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inr hperm) hlockRhs hlockAssign) ?_
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
    {σ σ₀ A I} {g : UInt256}
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
      typedCallViaEVM fork config evmPrice (EVM.address v.vat) "flux" 0
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
      typedCallViaEVM fork config evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (false, evmMove, outMove) true)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPrice))
    (hperm : I.perm = true) :
    let locals := clipperTakeStore I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody fork config contract evm0 locals takeTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  let usrFrame : Frame := { contract := contract, locals := clipperTakeLocalsUsr evmLock I, immutables := immStore v }
  let ticFrame : Frame := { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
  let stFrame : Frame := { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
  let doneFrame : Frame := { contract := contract, locals := clipperTakeLocalsDone evmLock I false price, immutables := immStore v }
  let priceFrame : Frame := { contract := contract, locals := clipperTakeLocalsPrice evmLock I false price, immutables := immStore v }
  let lotFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsLot evmLock evmPrice I false price, immutables := immStore v }
  let tabFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsTab evmLock evmPrice I false price, immutables := immStore v }
  let sliceFrame : Frame :=
    { contract := contract,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice, immutables := immStore v }
  have hlockedEval :
      evalExpr? config startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Stele.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? config startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? config startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Stele.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt fork config startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config) (stele := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt fork config usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config) (stele := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? config ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt fork config ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt fork config stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config) (stele := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt fork config doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config) (stele := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? config priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? config priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt fork config priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config) (stele := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt fork config lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config) (stele := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt fork config tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeStele :=
          { contract := contract, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I), immutables := immStore v })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail :
      ExecBlock fork config sliceFrame evmPrice
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
    simpa [sliceFrame, slice, lot] using
      clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureTailBlock v
        evmLock evmPrice evmVat evmMove I price slice hmul hgt hsliceLot hvatCode
        hcallVat hdataLen hvatMoveCode hcallMove
  have hblock :
      ExecBlock fork config startFrame evm0 takeTransition.body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, clipperTakePostOweFluxStmts, List.append_assoc] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inr hperm) hlockRhs hlockAssign) ?_
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
    (hrev : RDrev fork code (Sat256.ofUInt256 g) (initState σ σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hnoVatCode :
      (UInt256.ofNat
        ((evmVatStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceStele)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceStele I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceStele I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have hbody :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeSourceReverts (fork := fork) (hperm := by assumption)
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedStele hstoppedSteleLt husrStele
        (evmPrice := evmPriceStele) (evmVat := evmVatStele) (outVat := outVat) price
        hmax hsrcMul hsrcGt hsliceLot hvatCode hcallVat hdataLen hnoVatCode hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat : AccountMap} {AVat : Substate} {evmPriceStele : EVM.State}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {zVat : Bool}
    {R : List UInt256} {mem outVat : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
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
    (rd :
      RD fork code I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw outVat σVat k C)
    (hcallVatEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (zVat,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
          outVat) true)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
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
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  subst zVat
  subst aw
  have hrev :
      RDrev fork code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCode (v := v)
      (hpatch := hpatch) (by simpa using rd) rfl rfl hdataLenStack hmem hread64
      hvatMoveNoCodeEvm (by omega)
  have hvatCodeStele :
      0 <
        (UInt256.ofNat
          ((evmPriceStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
    have hcode :
        Reasoning.Theory.extCodeSizeWord σPostStele (clipperTakeVatTarget v) ≠ ⟨0⟩ := by
      simpa only [← hAccountsPost] using hvatCodeEvm
    simpa [State.lookupAccount, hevmPriceAccounts] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σPostStele) (target := clipperTakeVatTarget v)
        (addr := v.vat) (clipperTakeVatTargetAddress v).symm hcode
  let evmPostEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σPost }
  have hAccountsState : Eq evmPostEvm.accountMap evmPriceStele.accountMap := by
    simpa [evmPostEvm, hevmPriceAccounts] using hAccountsPost
  obtain ⟨σVatStele, AVatStele, hcallVatSteleRaw, hAccountsVat⟩ :=
    Reasoning.Theory.typedCallViaEVM_sameInputs
      (evm_stele := evmPriceStele) (hcall := hcallVatEvm) hAccountsState
      (by simpa [evmPostEvm, initState] using hevmPriceSigma0.symm)
      (by simpa [evmPostEvm, initState] using hevmPriceEnv.symm)
  let evmVatStele : EVM.State :=
    { evmPriceStele with
      accountMap := σVatStele
      substate := AVatStele
       }
  have hcallVatStele :
      typedCallViaEVM fork config evmPriceStele (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceStele.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat)]
        (true, evmVatStele, outVat) true := by
    simpa [evmVatStele, hevmPriceEnv, htab, hwho] using hcallVatSteleRaw
  have hvatMoveNoCodeStele :
      (UInt256.ofNat
        ((evmVatStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    have hnoCode :
        Reasoning.Theory.extCodeSizeWord σVatStele (clipperTakeVatTarget v) = ⟨0⟩ := by
      simpa only [← hAccountsVat] using hvatMoveNoCodeEvm
    simpa [evmVatStele, State.lookupAccount] using
      extCodeSizeWord_zero_lookup_code_zero
        (σ := σVatStele) (target := clipperTakeVatTarget v)
        (addr := v.vat) (clipperTakeVatTargetAddress v).symm hnoCode
  exact
    clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeRevertEquivFromPostWords (hperm := by assumption)
      (v := v) (code := code)
      (σ := σ)  (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (evmPriceStele := evmPriceStele) (evmVatStele := evmVatStele)
      (outVat := outVat) (price := price) (tab := tab) (lot := lot)
      hcode hwv hdispatch hdec hlockedStele hstoppedSteleLt husrStele htab hlot hrev
      hmax hmul hgt hvatCodeStele hcallVatStele hdataLen hvatMoveNoCodeStele hstatus

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat : AccountMap} {AVat : Substate} {evmPriceStele : EVM.State}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {zVat : Bool}
    {R : List UInt256} {mem outVat : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
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
    (rd :
      RD fork code I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw outVat σVat k C)
    (hcallVatEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (zVat,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
          outVat) true)
    {σMove : AccountMap} {AMove : Substate} {zMove : Bool} {outMove : ByteArray} {kMove CMove : ℕ}
    (rdMove :
      RD fork code I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4829⟩
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
        outMove σMove kMove CMove)
    (hcallMoveEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat }
        (EVM.address v.vat) "move" 0
        [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σVat I).toNat),
          .int (Int.ofNat tab.toNat)]
        (zMove,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σMove, substate := AMove },
          outMove) true)
    (hzMove : zMove = false)
    (houtMove : outMove.size < UInt256.size)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
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
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  subst zVat
  subst aw
  exact by
    have hrev :
        RDrev fork code (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
      RD.clipperTakeOweGtTabVatMoveCallFailure (v := v) (hpatch := hpatch)
        (by simpa using rdMove) hzMove houtMove hov
    have hvatCodeStele :
        0 <
          (UInt256.ofNat
            ((evmPriceStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      have hcode :
          Reasoning.Theory.extCodeSizeWord σPostStele (clipperTakeVatTarget v) ≠ ⟨0⟩ := by
        simpa only [← hAccountsPost] using hvatCodeEvm
      simpa [State.lookupAccount, hevmPriceAccounts] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          (σ := σPostStele) (target := clipperTakeVatTarget v)
          (addr := v.vat) (clipperTakeVatTargetAddress v).symm hcode
    let evmPostEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σPost }
    have hAccountsState : Eq evmPostEvm.accountMap evmPriceStele.accountMap := by
      simpa [evmPostEvm, hevmPriceAccounts] using hAccountsPost
    obtain ⟨σVatStele, AVatStele, hcallVatSteleRaw, hAccountsVat⟩ :=
      Reasoning.Theory.typedCallViaEVM_sameInputs
        (evm_stele := evmPriceStele) (hcall := hcallVatEvm) hAccountsState
        (by simpa [evmPostEvm, initState] using hevmPriceSigma0.symm)
        (by simpa [evmPostEvm, initState] using hevmPriceEnv.symm)
    let evmVatStele : EVM.State :=
      { evmPriceStele with
        accountMap := σVatStele
        substate := AVatStele
         }
    have hcallVatStele :
        typedCallViaEVM fork config evmPriceStele (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmPriceStele.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat
              (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat)]
          (true, evmVatStele, outVat) true := by
      simpa [evmVatStele, hevmPriceEnv, htab, hwho] using hcallVatSteleRaw
    have hvatMoveCodeStele :
        0 <
          (UInt256.ofNat
            ((evmVatStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      have hcode :
          Reasoning.Theory.extCodeSizeWord σVatStele (clipperTakeVatTarget v) ≠ ⟨0⟩ := by
        simpa only [← hAccountsVat] using hvatMoveCodeEvm
      simpa [evmVatStele, State.lookupAccount] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          (σ := σVatStele) (target := clipperTakeVatTarget v)
          (addr := v.vat) (clipperTakeVatTargetAddress v).symm hcode
    have hvow :
        clipperTakeVowTarget σVat I = clipperTakeVowEVMWord evmVatStele := by
      have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccountsVat
      simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, evmVatStele, hevmPriceEnv,
        Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord, hslot]
    let evmVatEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVat }
    have hAccountsMoveState : Eq evmVatEvm.accountMap evmVatStele.accountMap := by
      simpa [evmVatEvm, evmVatStele] using hAccountsVat
    obtain ⟨σMoveStele, AMoveStele, hcallMoveSteleRaw, _hAccountsMove⟩ :=
      Reasoning.Theory.typedCallViaEVM_sameInputs
        (evm_stele := evmVatStele) (hcall := hcallMoveEvm) hAccountsMoveState
        (by simpa [evmVatEvm, evmVatStele, initState] using hevmPriceSigma0.symm)
        (by simpa [evmVatEvm, evmVatStele, initState] using hevmPriceEnv.symm)
    let evmMoveStele : EVM.State :=
      { evmVatStele with
        accountMap := σMoveStele
        substate := AMoveStele
         }
    have hcallMoveStele :
        typedCallViaEVM fork config evmVatStele (EVM.address v.vat) "move" 0
          [.address evmVatStele.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVatStele).toNat),
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceStele I).toNat)]
          (false, evmMoveStele, outMove) true := by
      simpa [evmMoveStele, evmVatStele, hevmPriceEnv, hvow, htab, hzMove] using
        hcallMoveSteleRaw
    have hsrcMul :
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
            (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
      clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceStele)
        (price := price) (lot := lot) hlot hmul
    have hsrcGt :
        (clipperTakeSalesTabEVMWord evmPriceStele I).toNat <
          (UInt256.mul
            (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
              (clipperTakeAmtWord I))
            price).toNat :=
      clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceStele)
        (price := price) (tab := tab) (lot := lot) htab hlot hgt
    have hsliceLot :
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat ≤
          (clipperTakeSalesLotEVMWord evmPriceStele I).toNat :=
      clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceStele)
        (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
    have hbody :
        ExecTransitionBody fork config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
      simpa using
        (clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureSourceReverts (fork := fork) (hperm := by assumption)
          (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) v hwv hlockedStele hstoppedSteleLt husrStele
          (evmPrice := evmPriceStele) (evmVat := evmVatStele) (evmMove := evmMoveStele)
          (outVat := outVat) (outMove := outMove) price hmax hsrcMul hsrcGt hsliceLot
          hvatCodeStele hcallVatStele hdataLen hvatMoveCodeStele hcallMoveStele hstatus)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveNoCodeRevertEquivFromPostWords
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
    (hrev : RDrev fork code (Sat256.ofUInt256 g) (initState σ σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
        clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I) (clipperTakeAmtWord I)
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
        (.ok
          (Frame.mk contract (clipperTakeLocalsDogLoaded evmLock evmPriceStele evmVatStele I price slice
              owe0 owe0 slice' tabNew lotNew) (immStore v))
          evmVatStele))
    (hnoVatCode :
      (UInt256.ofNat
        ((evmVatStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceStele)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceStele I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceStele I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have htail :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPriceStele I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock fork config
        (Frame.mk contract (clipperTakeLocalsSlice evmLock evmPriceStele I false price slice) (immStore v))
        evmPriceStele
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
    dsimp only
    exact
      clipperTakeOweGtTabVatFluxSuccessVatMoveNoCodeTailBlockOfCallbackFalse v
        (Stele.EVM.storageStore
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩)
        evmPriceStele evmVatStele I price
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I) (clipperTakeAmtWord I))
        hsrcMul hsrcGt hsliceLot hvatCode hcallVat hcallback hnoVatCode
  have hbody :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessTailSourceReverts (fork := fork) (hperm := by assumption)
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedStele hstoppedSteleLt husrStele
        (evmPrice := evmPriceStele) price hmax htail hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessCallbackFalseVatMoveCallFailureRevertEquivFromPostWords
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
    {evmPriceStele evmVatStele evmMoveStele : EVM.State} {outVat outMove : ByteArray}
    {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
    (hrev : RDrev fork code (Sat256.ofUInt256 g) (initState σ σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
        clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I) (clipperTakeAmtWord I)
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
        (.ok
          (Frame.mk contract (clipperTakeLocalsDogLoaded evmLock evmPriceStele evmVatStele I price slice
              owe0 owe0 slice' tabNew lotNew) (immStore v))
          evmVatStele))
    (hvatMoveCode :
      0 <
        (UInt256.ofNat
          ((evmVatStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM fork config evmVatStele (EVM.address v.vat) "move" 0
        [.address evmVatStele.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVatStele).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceStele I).toNat)]
        (false, evmMoveStele, outMove) true)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceStele)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceStele I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceStele I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have htail :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPriceStele I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock fork config
        (Frame.mk contract (clipperTakeLocalsSlice evmLock evmPriceStele I false price slice) (immStore v))
        evmPriceStele
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
    dsimp only
    exact
      clipperTakeOweGtTabVatFluxSuccessVatMoveCallFailureTailBlockOfCallbackFalse v
        (Stele.EVM.storageStore
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩)
        evmPriceStele evmVatStele evmMoveStele I price
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I) (clipperTakeAmtWord I))
        hsrcMul hsrcGt hsliceLot hvatCode hcallVat hcallback hvatMoveCode hcallMove
  have hbody :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessTailSourceReverts (fork := fork) (hperm := by assumption)
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedStele hstoppedSteleLt husrStele
        (evmPrice := evmPriceStele) price hmax htail hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureRevertEquivFromPostWords
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
    {evmPriceStele evmVatStele evmMoveStele : EVM.State} {outVat outMove : ByteArray}
    {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
    (hrev : RDrev fork code (Sat256.ofUInt256 g) (initState σ σ₀
      (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
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
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatMoveCode :
      0 <
        (UInt256.ofNat
          ((evmVatStele.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM fork config evmVatStele (EVM.address v.vat) "move" 0
        [.address evmVatStele.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVatStele).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceStele I).toNat)]
        (false, evmMoveStele, outMove) true)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele))
    (hperm : I.perm = true) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot (I := I) (evmPrice := evmPriceStele)
      (price := price) (lot := lot) hlot hmul
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceStele I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
            (clipperTakeAmtWord I))
          price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceStele I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words (I := I) (evmPrice := evmPriceStele)
      (price := price) (tab := tab) (lot := lot) htab hlot hmul hgt
  have hbody :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
    simpa using
      (clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureSourceReverts (fork := fork) (hperm := by assumption)
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedStele hstoppedSteleLt husrStele
        (evmPrice := evmPriceStele) (evmVat := evmVatStele) (evmMove := evmMoveStele)
        (outVat := outVat) (outMove := outMove) price hmax hsrcMul hsrcGt hsliceLot
        hvatCode hcallVat hdataLen hvatMoveCode hcallMove hstatus)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

abbrev clipperTakeAfterFluxStmts : List Stmt :=
  [ .letDecl "dog_" (some addr) (.storage dogRef),
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
      [sender, .storage vowRef, .var "owe"] "_moveRet"

abbrev clipperTakeAfterMoveStmts : List Stmt :=
  [ .ite
      (.binary .eq (.var "lot") (.intLit 0))
      (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
        checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr, .var "digsAmt"] "_digsRet")
      (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
        [ilkExpr, .var "owe"] "_digsRet"),
    .ite
      (.binary .eq (.var "lot") (.intLit 0))
      [ .internalCall "_remove" [.var "id"] "_removeRet" ]
      [ .ite
          (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
            [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
    .assign .storage lockedRef (.intLit 0) ]

abbrev clipperTakeAfterSliceStmts : List Stmt :=
  checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
    [ .letDecl "owe" (some uint256) (.var "owe0"),
      clipperTakeOweAdjustmentStmt ] ++
    clipperTakePostOweFluxStmts ++
    clipperTakeAfterFluxStmts ++
    clipperTakeAfterMoveStmts

theorem clipperTakeSourcePrefixToSlice
    {σ σ₀ A I} {g : UInt256} {evmPrice : EVM.State}
    {result : ExecResult} (v : ClipperImmutables) (price : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract,
               locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v } evmPrice))
    (htail :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock fork config
        { contract := contract,
          locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice, immutables := immStore v }
        evmPrice (clipperTakeAfterSliceStmts) result)
    (hperm : I.perm = true) :
    let locals := clipperTakeStore I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock fork config { contract := contract, locals := locals, immutables := immStore v } evm0
      takeTransition.body result := by
  intro locals evm0
  let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  let usrFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsUsr evmLock I, immutables := immStore v }
  let ticFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
  let stFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
  let doneFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsDone evmLock I false price, immutables := immStore v }
  let priceFrame : Frame :=
    { contract := contract, locals := clipperTakeLocalsPrice evmLock I false price, immutables := immStore v }
  let lotFrame : Frame :=
    { contract := contract,
      locals := clipperTakeLocalsLot evmLock evmPrice I false price, immutables := immStore v }
  let tabFrame : Frame :=
    { contract := contract,
      locals := clipperTakeLocalsTab evmLock evmPrice I false price, immutables := immStore v }
  let sliceFrame : Frame :=
    { contract := contract,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice, immutables := immStore v }
  have hlockedEval :
      evalExpr? config startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? config startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? config startFrame evmLock
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
      ExecStmt fork config startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config) (stele := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address
          (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt fork config usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config) (stele := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? config ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt fork config ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt fork config stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config) (stele := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt fork config doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config) (stele := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? config priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? config priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using
      clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt fork config priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config) (stele := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt fork config lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, clipperTakeSalesTabEVMWord, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config) (stele := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat))
        (by simpa [lotFrame] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt fork config tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config) (caller := tabFrame) (evm := evmPrice)
        (calleeEvm := evmPrice) (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeStele :=
          { contract := contract,
            locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I), immutables := immStore v })
        (value := some
          [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail' :
      ExecBlock fork config sliceFrame evmPrice (clipperTakeAfterSliceStmts)
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
      refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inr hperm) hlockRhs hlockAssign) ?_
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
    {σ σ₀ A I} {g : UInt256} {evmPrice : EVM.State}
    (v : ClipperImmutables) (price : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract,
               locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v } evmPrice))
    (htail :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock fork config
        { contract := contract,
          locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice, immutables := immStore v }
        evmPrice (clipperTakeAfterSliceStmts) .reverted)
    (hperm : I.perm = true) :
    ExecTransitionBody fork config contract
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
  have hblock := clipperTakeSourcePrefixToSlice (fork := fork) (hperm := by assumption)
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (evmPrice := evmPrice) (result := .reverted)
    v price hwv hlocked hstopped husr hmax hstatus htail
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert
    (by simpa using hblock)

theorem clipperTakeSourceOkOfAfterSlice
    {σ σ₀ A I} {g : UInt256} {evmPrice evmFinal : EVM.State}
    {finalFrame : Frame} (v : ClipperImmutables) (price : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract,
               locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v } evmPrice))
    (htail :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let lot := clipperTakeSalesLotEVMWord evmPrice I
      let slice := clipperMinWord lot (clipperTakeAmtWord I)
      ExecBlock fork config
        { contract := contract,
          locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice, immutables := immStore v }
        evmPrice (clipperTakeAfterSliceStmts) (.ok finalFrame evmFinal))
    (hperm : I.perm = true) :
    ExecTransitionBody fork config contract
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) takeTransition.body
      (.returned finalFrame evmFinal none) (immStore v) := by
  have hblock := clipperTakeSourcePrefixToSlice (fork := fork) (hperm := by assumption)
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (evmPrice := evmPrice)
    (result := .ok finalFrame evmFinal)
    v price hwv hlocked hstopped husr hmax hstatus htail
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK
    (by simpa using hblock)

end Benchmarks.Dss.Clipper
