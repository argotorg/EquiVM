import Benchmarks.Dss.Clipper.TakeChostSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 1200000

abbrev clipperTakeLocalsPostTabNew (locals : Store) (tabNew : UInt256) : Store :=
  locals.insert "tabNew" (.int (Int.ofNat tabNew.toNat))

abbrev clipperTakeLocalsPostLotNew (locals : Store) (tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsPostTabNew locals tabNew).insert "lotNew"
    (.int (Int.ofNat lotNew.toNat))

abbrev clipperTakeLocalsPostTabAssigned
    (locals : Store) (tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsPostLotNew locals tabNew lotNew).insert "tab"
    (.int (Int.ofNat tabNew.toNat))

abbrev clipperTakeLocalsPostLotAssigned
    (locals : Store) (tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsPostTabAssigned locals tabNew lotNew).insert "lot"
    (.int (Int.ofNat lotNew.toNat))

abbrev clipperTakeLocalsPostFluxBuyerRet
    (locals : Store) (tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsPostLotAssigned locals tabNew lotNew).insert "_fluxBuyerRet" .unit

theorem clipperTakePostOweSubBlockOfEvals (v : ClipperImmutables)
    (evmRead : EVM.State) (locals : Store) (tabNew lotNew : UInt256)
    (htabNew :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotNew :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)))
    (htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)))
    (hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead))
    (hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead)) :
    ExecBlock (config v)
      (Frame.mk (contract v) locals)
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ])
      (.ok
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead) := by
  let startFrame : Frame := Frame.mk (contract v) locals
  let tabNewFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew)
  let lotNewFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew)
  let tabFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew)
  let lotFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew)
  have hletTabNew :
      ExecStmt (config v) startFrame evmRead
        (.letDecl "tabNew" (some uint256)
          (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
        (.ok tabNewFrame evmRead) := by
    simpa [startFrame, tabNewFrame, clipperTakeLocalsPostTabNew] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmRead) (name := "tabNew")
        (ty := some uint256) (expr := wrap256 (.binary .sub (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat tabNew.toNat)) htabNew)
  have hletLotNew :
      ExecStmt (config v) tabNewFrame evmRead
        (.letDecl "lotNew" (some uint256)
          (wrap256 (.binary .sub (.var "lot") (.var "slice"))))
        (.ok lotNewFrame evmRead) := by
    simpa [tabNewFrame, lotNewFrame, clipperTakeLocalsPostLotNew] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := tabNewFrame) (evm := evmRead) (name := "lotNew")
        (ty := some uint256) (expr := wrap256 (.binary .sub (.var "lot") (.var "slice")))
        (value := .int (Int.ofNat lotNew.toNat)) hlotNew)
  have hassignTab :
      ExecStmt (config v) lotNewFrame evmRead
        (.assign .localVar (varRef "tab") (.var "tabNew"))
        (.ok tabFrame evmRead) := by
    exact ExecStmt.assign htabNewVar (by simpa [lotNewFrame, tabFrame] using hassignTabOk)
  have hassignLot :
      ExecStmt (config v) tabFrame evmRead
        (.assign .localVar (varRef "lot") (.var "lotNew"))
        (.ok lotFrame evmRead) := by
    exact ExecStmt.assign hlotNewVar (by simpa [tabFrame, lotFrame] using hassignLotOk)
  simpa [wrappingSubInto, startFrame, lotFrame] using
    (ExecBlock.consNormal hletTabNew
      (ExecBlock.consNormal hletLotNew
        (ExecBlock.consNormal hassignTab
          (ExecBlock.consNormal hassignLot ExecBlock.nil))))

theorem clipperTakeVatFluxBuyerNoCodeBlockOfLocals (v : ClipperImmutables)
    (evmRead : EVM.State) (locals : Store) (tabNew lotNew : UInt256)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool false) := by
    exact clipperEvalTakeVatCodeGuard_false v evmRead
      (clipperTakeLocalsPostLotAssigned locals tabNew lotNew) hnoVatCode
  simpa [checkedExternalCallStmts] using
    (ExecBlock.consRevert (ExecStmt.requireFalse hguard))

theorem clipperTakeVatFluxBuyerCallFailureBlockOfLocals (v : ClipperImmutables)
    (evmRead evmVat : EVM.State) (locals : Store) (tabNew lotNew : UInt256)
    {outVat : ByteArray} {argVals : List Value}
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0 argVals
        (false, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) := by
    exact clipperEvalTakeVatCodeGuard_true v evmRead
      (clipperTakeLocalsPostLotAssigned locals tabNew lotNew) hvatCode
  simpa [checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      (ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (clipperEvalVat v evmRead (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
          (by simp [evalExpr?, pure]) hargs hcallVat)))

theorem clipperTakeVatFluxBuyerCallSuccessBlockOfLocals (v : ClipperImmutables)
    (evmRead evmVat : EVM.State) (locals : Store) (tabNew lotNew : UInt256)
    {outVat : ByteArray} {argVals : List Value}
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0 argVals
        (true, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      (.ok
        (Frame.mk (contract v) (clipperTakeLocalsPostFluxBuyerRet locals tabNew lotNew))
        evmVat) := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) := by
    exact clipperEvalTakeVatCodeGuard_true v evmRead
      (clipperTakeLocalsPostLotAssigned locals tabNew lotNew) hvatCode
  simpa [checkedExternalCallStmts, clipperTakeLocalsPostFluxBuyerRet, collapseReturns] using
    (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalVat v evmRead (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
          (by simp [evalExpr?, pure]) hargs hcallVat
          (clipperTakeDecodeFluxVoid v outVat))
        ExecBlock.nil))

theorem clipperTakeVatFluxNoCodeTailBlockOfLocals (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (locals : Store) (tabNew lotNew : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hite :
      let owe0 := UInt256.mul slice price
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt (.ok (Frame.mk (contract v) locals) evmRead))
    (htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)))
    (htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)))
    (hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead))
    (hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead))
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    let owe0 := UInt256.mul slice price
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  intro owe0
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let postSubFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hsubBlock :
      ExecBlock (config v) (Frame.mk (contract v) locals) evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [postSubFrame] using
      clipperTakePostOweSubBlockOfEvals v evmRead locals tabNew lotNew
        htabSub hlotSub htabNewVar hlotNewVar hassignTabOk hassignLotOk
  have hvatRevert :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [postSubFrame] using
      clipperTakeVatFluxBuyerNoCodeBlockOfLocals v evmRead locals tabNew lotNew hnoVatCode
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts v) .reverted := by
    exact ExecBlock.consNormal (by simpa [oweFrame, owe0] using hite)
      (by
        simpa [clipperTakePostOweFluxStmts] using
          execBlockAppendRevert hsubBlock hvatRevert)
  simpa [sliceFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendRevert hmulBlock hafterIte

theorem clipperTakeVatFluxCallFailureTailBlockOfLocals (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray} (locals : Store) (tabNew lotNew fluxSlice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hite :
      let owe0 := UInt256.mul slice price
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt (.ok (Frame.mk (contract v) locals) evmRead))
    (htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)))
    (htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)))
    (hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead))
    (hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead))
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat fluxSlice.toNat)])
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat fluxSlice.toNat)]
        (false, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  intro owe0
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let postSubFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hsubBlock :
      ExecBlock (config v) (Frame.mk (contract v) locals) evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [postSubFrame] using
      clipperTakePostOweSubBlockOfEvals v evmRead locals tabNew lotNew
        htabSub hlotSub htabNewVar hlotNewVar hassignTabOk hassignLotOk
  have hvatRevert :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [postSubFrame] using
      clipperTakeVatFluxBuyerCallFailureBlockOfLocals v evmRead evmVat locals tabNew
        lotNew hvatCode hargs hcallVat
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts v) .reverted := by
    exact ExecBlock.consNormal (by simpa [oweFrame, owe0] using hite)
      (by
        simpa [clipperTakePostOweFluxStmts] using
          execBlockAppendRevert hsubBlock hvatRevert)
  simpa [sliceFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendRevert hmulBlock hafterIte

theorem clipperTakeVatFluxCallSuccessTailBlockOfLocals (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray} (locals : Store) (tabNew lotNew fluxSlice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hite :
      let owe0 := UInt256.mul slice price
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt (.ok (Frame.mk (contract v) locals) evmRead))
    (htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)))
    (htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)))
    (hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)))
    (hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead))
    (hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead))
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat fluxSlice.toNat)])
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat fluxSlice.toNat)]
        (true, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      (.ok
        (Frame.mk (contract v) (clipperTakeLocalsPostFluxBuyerRet locals tabNew lotNew))
        evmVat) := by
  intro owe0
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let postSubFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew)
  let fluxFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsPostFluxBuyerRet locals tabNew lotNew)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hsubBlock :
      ExecBlock (config v) (Frame.mk (contract v) locals) evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [postSubFrame] using
      clipperTakePostOweSubBlockOfEvals v evmRead locals tabNew lotNew
        htabSub hlotSub htabNewVar hlotNewVar hassignTabOk hassignLotOk
  have hvatOk :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        (.ok fluxFrame evmVat) := by
    simpa [postSubFrame, fluxFrame] using
      clipperTakeVatFluxBuyerCallSuccessBlockOfLocals v evmRead evmVat locals tabNew
        lotNew hvatCode hargs hcallVat
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts v)
        (.ok fluxFrame evmVat) := by
    exact ExecBlock.consNormal (by simpa [oweFrame, owe0] using hite)
      (by
        simpa [clipperTakePostOweFluxStmts] using execBlockAppendOk hsubBlock hvatOk)
  simpa [sliceFrame, fluxFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendOk hmulBlock hafterIte

theorem clipperEvalTakeVarOweAtRemainingTab (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmEval (.var "owe") = .ok (.int (Int.ofNat owe.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
    store_get_self]
  rfl

theorem clipperEvalTakeTabSubOweAtRemainingTab (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmRead (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe).toNat)) := by
  let tab := clipperTakeSalesTabEVMWord evmRead I
  have hsubNat : (UInt256.sub tab owe).toNat = tab.toNat - owe.toNat := by
    exact usub_toNat howeTab
  have hdiff :
      Int.ofNat tab.toNat - Int.ofNat owe.toNat = Int.ofNat (tab.toNat - owe.toNat) := by
    exact (Int.ofNat_sub howeTab).symm
  have hltNat : tab.toNat - owe.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le tab.toNat owe.toNat) tab.val.isLt
  have hlt : Int.ofNat (tab.toNat - owe.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (tab.toNat - owe.toNat) % wordModulus =
        Int.ofNat (tab.toNat - owe.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat - Int.ofNat owe.toNat) %
          wordModulus =
        Int.ofNat ((clipperTakeSalesTabEVMWord evmRead I).toNat - owe.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
        Int.ofNat owe.toNat = Int.ofNat (tab.toNat - owe.toNat) by
      simpa [tab] using hdiff]
    simpa [tab] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarTabAtRemainingTab v evmLoc evmRead evmRead I price slice owe0 owe
      chost remainingTab,
    clipperEvalTakeVarOweAtRemainingTab v evmLoc evmRead evmRead I price slice owe0 owe
      chost remainingTab,
    evalBinaryOp?, hsubNat, hwordNonzero, tab]
  exact hmodLoad

theorem clipperEvalTakeLotSubSliceAtPostRemainingTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab tabNew : UInt256)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals :=
          clipperTakeLocalsPostTabNew
            (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
              remainingTab) tabNew }
      evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice).toNat)) := by
  have hlot :
      evalExpr? (config v)
        { contract := contract v,
          locals :=
            clipperTakeLocalsPostTabNew
              (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
                remainingTab) tabNew }
        evmRead (.var "lot") =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
      store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
      store_get_ne _ _ (by decide), clipperTakeLocalsLot, store_get_self]
    rfl
  have hslice :
      evalExpr? (config v)
        { contract := contract v,
          locals :=
            clipperTakeLocalsPostTabNew
              (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
                remainingTab) tabNew }
        evmRead (.var "slice") = .ok (.int (Int.ofNat slice.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
      store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_self]
    rfl
  let lot := clipperTakeSalesLotEVMWord evmRead I
  have hsubNat : (UInt256.sub lot slice).toNat = lot.toNat - slice.toNat := by
    exact usub_toNat hsliceLot
  have hdiff :
      Int.ofNat lot.toNat - Int.ofNat slice.toNat =
        Int.ofNat (lot.toNat - slice.toNat) := by
    exact (Int.ofNat_sub hsliceLot).symm
  have hltNat : lot.toNat - slice.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le lot.toNat slice.toNat) lot.val.isLt
  have hlt : Int.ofNat (lot.toNat - slice.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (lot.toNat - slice.toNat) % wordModulus =
        Int.ofNat (lot.toNat - slice.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
          Int.ofNat slice.toNat) % wordModulus =
        Int.ofNat ((clipperTakeSalesLotEVMWord evmRead I).toNat - slice.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
        Int.ofNat slice.toNat = Int.ofNat (lot.toNat - slice.toNat) by
      simpa [lot] using hdiff]
    simpa [lot] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind, hlot, hslice, evalBinaryOp?, hsubNat,
    hwordNonzero, lot]
  exact hmodLoad

theorem clipperEvalTakeVatFluxBuyerArgsAtPostRemaining (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsPostLotAssigned
          (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
            remainingTab) tabNew lotNew))
      evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
        .ok
          [v.ilk, .address evmRead.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat slice.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  have hwho :
      Value.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat) =
        Value.address (AccountAddress.ofNat
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat) := by
    rw [solcAddressValue_masked (clipperTakeWhoWord I)]
    rw [u256_land_comm solcAddrMask (clipperTakeWhoWord I)]
  have hilkEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
              remainingTab) tabNew lotNew))
        evmRead (ilkExpr v) = .ok v.ilk := by
    simp [ilkExpr, hilk, evalExpr?, pure]
  have hthisEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
              remainingTab) tabNew lotNew))
        evmRead thisAddr = .ok (.address evmRead.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hwhoRaw :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
              remainingTab) tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
      store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
      store_get_ne _ _ (by decide), clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
      clipperTakeStore, store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hwhoEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
              remainingTab) tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat)) := by
    simpa [hwho] using hwhoRaw
  have hsliceEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
              remainingTab) tabNew lotNew))
        evmRead (.var "slice") = .ok (.int (Int.ofNat slice.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
      store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_self]
    rfl
  simp only [evalExprs?, hilkEval, hthisEval, hwhoEval, hsliceEval, EvalResult.bind, bind,
    pure]

theorem clipperTakeChostNoAdjustVatFluxNoCodeTailBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (slice.mul price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (slice.mul price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hchostLe :
      (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat ≤
        ((clipperTakeSalesTabEVMWord evmRead I).sub (slice.mul price)).toNat)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    let owe0 := UInt256.mul slice price
    let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := (clipperTakeSalesTabEVMWord evmRead I).sub owe0
    let locals :=
      clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe0
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  intro owe0 chost remainingTab locals tabNew lotNew
  have hite :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok (Frame.mk (contract v) locals) evmRead) := by
    simpa [owe0, chost, remainingTab, locals] using
      clipperTakeOweLtTabSliceLtLotChostNoAdjustIte v evmLoc evmRead I price slice
        hle hlt hsliceLt hchostLe
  have htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [locals, tabNew, owe0, chost, remainingTab] using
      clipperEvalTakeTabSubOweAtRemainingTab v evmLoc evmRead I price slice owe0 owe0
        chost remainingTab hle
  have hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [locals, tabNew, lotNew, owe0, chost, remainingTab] using
      clipperEvalTakeLotSubSliceAtPostRemainingTabNew v evmLoc evmRead I price slice
        owe0 owe0 chost remainingTab tabNew (Nat.le_of_lt hsliceLt)
  have htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_self]
    rfl
  have hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_self]
    rfl
  have hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostTabAssigned, pure, bind, EvalResult.bind]
  have hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostLotAssigned, pure, bind, EvalResult.bind]
  simpa [owe0] using
    clipperTakeVatFluxNoCodeTailBlockOfLocals v evmLoc evmRead I price slice locals
      tabNew lotNew hmul hite htabSub hlotSub htabNewVar hlotNewVar hassignTabOk
      hassignLotOk hnoVatCode

theorem clipperTakeChostNoAdjustVatFluxCallFailureTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (slice.mul price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (slice.mul price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hchostLe :
      (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat ≤
        ((clipperTakeSalesTabEVMWord evmRead I).sub (slice.mul price)).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := (clipperTakeSalesTabEVMWord evmRead I).sub owe0
    let locals :=
      clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe0
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  intro owe0 chost remainingTab locals tabNew lotNew
  have hite :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok (Frame.mk (contract v) locals) evmRead) := by
    simpa [owe0, chost, remainingTab, locals] using
      clipperTakeOweLtTabSliceLtLotChostNoAdjustIte v evmLoc evmRead I price slice
        hle hlt hsliceLt hchostLe
  have htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [locals, tabNew, owe0, chost, remainingTab] using
      clipperEvalTakeTabSubOweAtRemainingTab v evmLoc evmRead I price slice owe0 owe0
        chost remainingTab hle
  have hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [locals, tabNew, lotNew, owe0, chost, remainingTab] using
      clipperEvalTakeLotSubSliceAtPostRemainingTabNew v evmLoc evmRead I price slice
        owe0 owe0 chost remainingTab tabNew (Nat.le_of_lt hsliceLt)
  have htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_self]
    rfl
  have hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_self]
    rfl
  have hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostTabAssigned, pure, bind, EvalResult.bind]
  have hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostLotAssigned, pure, bind, EvalResult.bind]
  have hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice.toNat)] := by
    simpa [locals, owe0, chost, remainingTab] using
      clipperEvalTakeVatFluxBuyerArgsAtPostRemaining v evmLoc evmRead I price slice
        owe0 owe0 chost remainingTab tabNew lotNew
  simpa [owe0] using
    clipperTakeVatFluxCallFailureTailBlockOfLocals v evmLoc evmRead evmVat I price
      slice locals tabNew lotNew slice hmul hite htabSub hlotSub htabNewVar hlotNewVar
      hassignTabOk hassignLotOk hargs hvatCode hcallVat

theorem clipperTakeChostNoAdjustVatFluxCallSuccessTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (slice.mul price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (slice.mul price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hchostLe :
      (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat ≤
        ((clipperTakeSalesTabEVMWord evmRead I).sub (slice.mul price)).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := (clipperTakeSalesTabEVMWord evmRead I).sub owe0
    let locals :=
      clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe0
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      (.ok
        (Frame.mk (contract v) (clipperTakeLocalsPostFluxBuyerRet locals tabNew lotNew))
        evmVat) := by
  intro owe0 chost remainingTab locals tabNew lotNew
  have hite :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok (Frame.mk (contract v) locals) evmRead) := by
    simpa [owe0, chost, remainingTab, locals] using
      clipperTakeOweLtTabSliceLtLotChostNoAdjustIte v evmLoc evmRead I price slice
        hle hlt hsliceLt hchostLe
  have htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [locals, tabNew, owe0, chost, remainingTab] using
      clipperEvalTakeTabSubOweAtRemainingTab v evmLoc evmRead I price slice owe0 owe0
        chost remainingTab hle
  have hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [locals, tabNew, lotNew, owe0, chost, remainingTab] using
      clipperEvalTakeLotSubSliceAtPostRemainingTabNew v evmLoc evmRead I price slice
        owe0 owe0 chost remainingTab tabNew (Nat.le_of_lt hsliceLt)
  have htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_self]
    rfl
  have hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_self]
    rfl
  have hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostTabAssigned, pure, bind, EvalResult.bind]
  have hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostLotAssigned, pure, bind, EvalResult.bind]
  have hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice.toNat)] := by
    simpa [locals, owe0, chost, remainingTab] using
      clipperEvalTakeVatFluxBuyerArgsAtPostRemaining v evmLoc evmRead I price slice
        owe0 owe0 chost remainingTab tabNew lotNew
  simpa [owe0] using
    clipperTakeVatFluxCallSuccessTailBlockOfLocals v evmLoc evmRead evmVat I price
      slice locals tabNew lotNew slice hmul hite htabSub hlotSub htabNewVar hlotNewVar
      hassignTabOk hassignLotOk hargs hvatCode hcallVat

theorem clipperEvalTakeVarTabAtChostOweSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted sliceAdjusted : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals :=
          clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
            remainingTab oweAdjusted sliceAdjusted }
      evmEval (.var "tab") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsChostOweSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsChostOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweAdjusted, store_get_ne _ _ (by decide),
    clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
    store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
    store_get_self]
  rfl

theorem clipperEvalTakeVarOweAtChostOweSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted sliceAdjusted : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals :=
          clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
            remainingTab oweAdjusted sliceAdjusted }
      evmEval (.var "owe") = .ok (.int (Int.ofNat oweAdjusted.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsChostOweSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsChostOwe, store_get_self]
  rfl

theorem clipperEvalTakeTabSubOweAtChostOweSlice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted sliceAdjusted : UInt256)
    (howeTab : oweAdjusted.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals :=
          clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
            remainingTab oweAdjusted sliceAdjusted }
      evmRead (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok
        (.int (Int.ofNat
          (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) oweAdjusted).toNat)) := by
  let tab := clipperTakeSalesTabEVMWord evmRead I
  have hsubNat : (UInt256.sub tab oweAdjusted).toNat = tab.toNat - oweAdjusted.toNat := by
    exact usub_toNat howeTab
  have hdiff :
      Int.ofNat tab.toNat - Int.ofNat oweAdjusted.toNat =
        Int.ofNat (tab.toNat - oweAdjusted.toNat) := by
    exact (Int.ofNat_sub howeTab).symm
  have hltNat : tab.toNat - oweAdjusted.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le tab.toNat oweAdjusted.toNat) tab.val.isLt
  have hlt : Int.ofNat (tab.toNat - oweAdjusted.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (tab.toNat - oweAdjusted.toNat) % wordModulus =
        Int.ofNat (tab.toNat - oweAdjusted.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
          Int.ofNat oweAdjusted.toNat) % wordModulus =
        Int.ofNat ((clipperTakeSalesTabEVMWord evmRead I).toNat - oweAdjusted.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
        Int.ofNat oweAdjusted.toNat = Int.ofNat (tab.toNat - oweAdjusted.toNat) by
      simpa [tab] using hdiff]
    simpa [tab] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarTabAtChostOweSlice v evmLoc evmRead evmRead I price slice owe0
      owe chost remainingTab oweAdjusted sliceAdjusted,
    clipperEvalTakeVarOweAtChostOweSlice v evmLoc evmRead evmRead I price slice owe0
      owe chost remainingTab oweAdjusted sliceAdjusted,
    evalBinaryOp?, hsubNat, hwordNonzero, tab]
  exact hmodLoad

theorem clipperEvalTakeLotSubSliceAtPostChostOweSliceTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted sliceAdjusted tabNew : UInt256)
    (hsliceLot : sliceAdjusted.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals :=
          clipperTakeLocalsPostTabNew
            (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
              remainingTab oweAdjusted sliceAdjusted) tabNew }
      evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok
        (.int (Int.ofNat
          (UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) sliceAdjusted).toNat)) := by
  have hlot :
      evalExpr? (config v)
        { contract := contract v,
          locals :=
            clipperTakeLocalsPostTabNew
              (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
                remainingTab oweAdjusted sliceAdjusted) tabNew }
        evmRead (.var "lot") =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsChostOweSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsChostOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweAdjusted, store_get_ne _ _ (by decide),
      clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
      store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
      store_get_ne _ _ (by decide), clipperTakeLocalsLot, store_get_self]
    rfl
  have hslice :
      evalExpr? (config v)
        { contract := contract v,
          locals :=
            clipperTakeLocalsPostTabNew
              (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
                remainingTab oweAdjusted sliceAdjusted) tabNew }
        evmRead (.var "slice") = .ok (.int (Int.ofNat sliceAdjusted.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsChostOweSlice, store_get_self]
    rfl
  let lot := clipperTakeSalesLotEVMWord evmRead I
  have hsubNat : (UInt256.sub lot sliceAdjusted).toNat =
      lot.toNat - sliceAdjusted.toNat := by
    exact usub_toNat hsliceLot
  have hdiff :
      Int.ofNat lot.toNat - Int.ofNat sliceAdjusted.toNat =
        Int.ofNat (lot.toNat - sliceAdjusted.toNat) := by
    exact (Int.ofNat_sub hsliceLot).symm
  have hltNat : lot.toNat - sliceAdjusted.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le lot.toNat sliceAdjusted.toNat) lot.val.isLt
  have hlt : Int.ofNat (lot.toNat - sliceAdjusted.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (lot.toNat - sliceAdjusted.toNat) % wordModulus =
        Int.ofNat (lot.toNat - sliceAdjusted.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
          Int.ofNat sliceAdjusted.toNat) % wordModulus =
        Int.ofNat ((clipperTakeSalesLotEVMWord evmRead I).toNat - sliceAdjusted.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
        Int.ofNat sliceAdjusted.toNat = Int.ofNat (lot.toNat - sliceAdjusted.toNat) by
      simpa [lot] using hdiff]
    simpa [lot] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind, hlot, hslice, evalBinaryOp?, hsubNat,
    hwordNonzero, lot]
  exact hmodLoad

theorem clipperEvalTakeVatFluxBuyerArgsAtPostChostOweSlice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted sliceAdjusted tabNew lotNew :
      UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsPostLotAssigned
          (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
            remainingTab oweAdjusted sliceAdjusted) tabNew lotNew))
      evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
        .ok
          [v.ilk, .address evmRead.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat sliceAdjusted.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  have hwho :
      Value.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat) =
        Value.address (AccountAddress.ofNat
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat) := by
    rw [solcAddressValue_masked (clipperTakeWhoWord I)]
    rw [u256_land_comm solcAddrMask (clipperTakeWhoWord I)]
  have hilkEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
              remainingTab oweAdjusted sliceAdjusted) tabNew lotNew))
        evmRead (ilkExpr v) = .ok v.ilk := by
    simp [ilkExpr, hilk, evalExpr?, pure]
  have hthisEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
              remainingTab oweAdjusted sliceAdjusted) tabNew lotNew))
        evmRead thisAddr = .ok (.address evmRead.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hwhoRaw :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
              remainingTab oweAdjusted sliceAdjusted) tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsChostOweSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsChostOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweAdjusted, store_get_ne _ _ (by decide),
      clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
      store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
      store_get_ne _ _ (by decide), clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
      clipperTakeStore, store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hwhoEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
              remainingTab oweAdjusted sliceAdjusted) tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat)) := by
    simpa [hwho] using hwhoRaw
  have hsliceEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsPostLotAssigned
            (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
              remainingTab oweAdjusted sliceAdjusted) tabNew lotNew))
        evmRead (.var "slice") = .ok (.int (Int.ofNat sliceAdjusted.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsChostOweSlice, store_get_self]
    rfl
  simp only [evalExprs?, hilkEval, hthisEval, hwhoEval, hsliceEval, EvalResult.bind, bind,
    pure]

theorem clipperTakeChostAdjustVatFluxNoCodeTailBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (slice.mul price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (slice.mul price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hremainingLt :
      ((clipperTakeSalesTabEVMWord evmRead I).sub (slice.mul price)).toNat <
        (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat)
    (hchostTab :
      (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat <
        (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hprice : price ≠ ⟨0⟩)
    (hsliceAdjustedLot :
      (((clipperTakeSalesTabEVMWord evmRead I).sub
          (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩)).div price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    let owe0 := UInt256.mul slice price
    let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := (clipperTakeSalesTabEVMWord evmRead I).sub owe0
    let oweAdjusted := (clipperTakeSalesTabEVMWord evmRead I).sub chost
    let sliceAdjusted := oweAdjusted.div price
    let locals :=
      clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab oweAdjusted sliceAdjusted
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) oweAdjusted
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) sliceAdjusted
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  intro owe0 chost remainingTab oweAdjusted sliceAdjusted locals tabNew lotNew
  have hite :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok (Frame.mk (contract v) locals) evmRead) := by
    simpa [owe0, chost, remainingTab, oweAdjusted, sliceAdjusted, locals] using
      clipperTakeOweLtTabSliceLtLotChostAdjustIte v evmLoc evmRead I price slice
        hle hlt hsliceLt hremainingLt hchostTab hprice
  have howeAdjustedTab : oweAdjusted.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat := by
    have hchostLe :
        chost.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat := Nat.le_of_lt hchostTab
    have hsub := usub_toNat (a := clipperTakeSalesTabEVMWord evmRead I) (b := chost)
      hchostLe
    rw [show oweAdjusted = (clipperTakeSalesTabEVMWord evmRead I).sub chost by rfl, hsub]
    omega
  have htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [locals, tabNew, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeTabSubOweAtChostOweSlice v evmLoc evmRead I price slice owe0 owe0
        chost remainingTab oweAdjusted sliceAdjusted howeAdjustedTab
  have hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [locals, tabNew, lotNew, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeLotSubSliceAtPostChostOweSliceTabNew v evmLoc evmRead I price
        slice owe0 owe0 chost remainingTab oweAdjusted sliceAdjusted tabNew
        (by simpa [chost, oweAdjusted, sliceAdjusted] using hsliceAdjustedLot)
  have htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_self]
    rfl
  have hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_self]
    rfl
  have hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostTabAssigned, pure, bind, EvalResult.bind]
  have hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostLotAssigned, pure, bind, EvalResult.bind]
  simpa [owe0] using
    clipperTakeVatFluxNoCodeTailBlockOfLocals v evmLoc evmRead I price slice locals
      tabNew lotNew hmul hite htabSub hlotSub htabNewVar hlotNewVar hassignTabOk
      hassignLotOk hnoVatCode

theorem clipperTakeChostAdjustVatFluxCallFailureTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (slice.mul price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (slice.mul price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hremainingLt :
      ((clipperTakeSalesTabEVMWord evmRead I).sub (slice.mul price)).toNat <
        (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat)
    (hchostTab :
      (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat <
        (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hprice : price ≠ ⟨0⟩)
    (hsliceAdjustedLot :
      (((clipperTakeSalesTabEVMWord evmRead I).sub
          (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩)).div price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
      let oweAdjusted := (clipperTakeSalesTabEVMWord evmRead I).sub chost
      let sliceAdjusted := oweAdjusted.div price
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat sliceAdjusted.toNat)]
        (false, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := (clipperTakeSalesTabEVMWord evmRead I).sub owe0
    let oweAdjusted := (clipperTakeSalesTabEVMWord evmRead I).sub chost
    let sliceAdjusted := oweAdjusted.div price
    let locals :=
      clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab oweAdjusted sliceAdjusted
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) oweAdjusted
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) sliceAdjusted
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  intro owe0 chost remainingTab oweAdjusted sliceAdjusted locals tabNew lotNew
  have hite :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok (Frame.mk (contract v) locals) evmRead) := by
    simpa [owe0, chost, remainingTab, oweAdjusted, sliceAdjusted, locals] using
      clipperTakeOweLtTabSliceLtLotChostAdjustIte v evmLoc evmRead I price slice
        hle hlt hsliceLt hremainingLt hchostTab hprice
  have howeAdjustedTab : oweAdjusted.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat := by
    have hchostLe :
        chost.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat := Nat.le_of_lt hchostTab
    have hsub := usub_toNat (a := clipperTakeSalesTabEVMWord evmRead I) (b := chost)
      hchostLe
    rw [show oweAdjusted = (clipperTakeSalesTabEVMWord evmRead I).sub chost by rfl, hsub]
    omega
  have htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [locals, tabNew, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeTabSubOweAtChostOweSlice v evmLoc evmRead I price slice owe0 owe0
        chost remainingTab oweAdjusted sliceAdjusted howeAdjustedTab
  have hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [locals, tabNew, lotNew, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeLotSubSliceAtPostChostOweSliceTabNew v evmLoc evmRead I price
        slice owe0 owe0 chost remainingTab oweAdjusted sliceAdjusted tabNew
        (by simpa [chost, oweAdjusted, sliceAdjusted] using hsliceAdjustedLot)
  have htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_self]
    rfl
  have hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_self]
    rfl
  have hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostTabAssigned, pure, bind, EvalResult.bind]
  have hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostLotAssigned, pure, bind, EvalResult.bind]
  have hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat sliceAdjusted.toNat)] := by
    simpa [locals, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeVatFluxBuyerArgsAtPostChostOweSlice v evmLoc evmRead I price
        slice owe0 owe0 chost remainingTab oweAdjusted sliceAdjusted tabNew lotNew
  simpa [owe0, chost, oweAdjusted, sliceAdjusted] using
    clipperTakeVatFluxCallFailureTailBlockOfLocals v evmLoc evmRead evmVat I price
      slice locals tabNew lotNew sliceAdjusted hmul hite htabSub hlotSub htabNewVar
      hlotNewVar hassignTabOk hassignLotOk hargs hvatCode
      (by simpa [chost, oweAdjusted, sliceAdjusted] using hcallVat)

theorem clipperTakeChostAdjustVatFluxCallSuccessTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hle : (slice.mul price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (slice.mul price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hremainingLt :
      ((clipperTakeSalesTabEVMWord evmRead I).sub (slice.mul price)).toNat <
        (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat)
    (hchostTab :
      (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat <
        (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hprice : price ≠ ⟨0⟩)
    (hsliceAdjustedLot :
      (((clipperTakeSalesTabEVMWord evmRead I).sub
          (EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩)).div price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
      let oweAdjusted := (clipperTakeSalesTabEVMWord evmRead I).sub chost
      let sliceAdjusted := oweAdjusted.div price
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat sliceAdjusted.toNat)]
        (true, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    let chost := EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := (clipperTakeSalesTabEVMWord evmRead I).sub owe0
    let oweAdjusted := (clipperTakeSalesTabEVMWord evmRead I).sub chost
    let sliceAdjusted := oweAdjusted.div price
    let locals :=
      clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab oweAdjusted sliceAdjusted
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) oweAdjusted
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) sliceAdjusted
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      (.ok
        (Frame.mk (contract v) (clipperTakeLocalsPostFluxBuyerRet locals tabNew lotNew))
        evmVat) := by
  intro owe0 chost remainingTab oweAdjusted sliceAdjusted locals tabNew lotNew
  have hite :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok (Frame.mk (contract v) locals) evmRead) := by
    simpa [owe0, chost, remainingTab, oweAdjusted, sliceAdjusted, locals] using
      clipperTakeOweLtTabSliceLtLotChostAdjustIte v evmLoc evmRead I price slice
        hle hlt hsliceLt hremainingLt hchostTab hprice
  have howeAdjustedTab : oweAdjusted.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat := by
    have hchostLe :
        chost.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat := Nat.le_of_lt hchostTab
    have hsub := usub_toNat (a := clipperTakeSalesTabEVMWord evmRead I) (b := chost)
      hchostLe
    rw [show oweAdjusted = (clipperTakeSalesTabEVMWord evmRead I).sub chost by rfl, hsub]
    omega
  have htabSub :
      evalExpr? (config v) (Frame.mk (contract v) locals) evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [locals, tabNew, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeTabSubOweAtChostOweSlice v evmLoc evmRead I price slice owe0 owe0
        chost remainingTab oweAdjusted sliceAdjusted howeAdjustedTab
  have hlotSub :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabNew locals tabNew))
        evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [locals, tabNew, lotNew, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeLotSubSliceAtPostChostOweSliceTabNew v evmLoc evmRead I price
        slice owe0 owe0 chost remainingTab oweAdjusted sliceAdjusted tabNew
        (by simpa [chost, oweAdjusted, sliceAdjusted] using hsliceAdjustedLot)
  have htabNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostTabNew, store_get_self]
    rfl
  have hlotNewVar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsPostTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsPostLotNew, store_get_self]
    rfl
  have hassignTabOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotNew locals tabNew lotNew))
        evmRead .localVar (varRef "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostTabAssigned, pure, bind, EvalResult.bind]
  have hassignLotOk :
      assignStorageRef? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostTabAssigned locals tabNew lotNew))
        evmRead .localVar (varRef "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok
          (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew),
            evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, locals,
      clipperTakeLocalsPostLotAssigned, pure, bind, EvalResult.bind]
  have hargs :
      evalExprs? (config v)
        (Frame.mk (contract v) (clipperTakeLocalsPostLotAssigned locals tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat sliceAdjusted.toNat)] := by
    simpa [locals, owe0, chost, remainingTab, oweAdjusted, sliceAdjusted] using
      clipperEvalTakeVatFluxBuyerArgsAtPostChostOweSlice v evmLoc evmRead I price
        slice owe0 owe0 chost remainingTab oweAdjusted sliceAdjusted tabNew lotNew
  simpa [owe0, chost, oweAdjusted, sliceAdjusted] using
    clipperTakeVatFluxCallSuccessTailBlockOfLocals v evmLoc evmRead evmVat I price
      slice locals tabNew lotNew sliceAdjusted hmul hite htabSub hlotSub htabNewVar
      hlotNewVar hassignTabOk hassignLotOk hargs hvatCode
      (by simpa [chost, oweAdjusted, sliceAdjusted] using hcallVat)

end Benchmarks.Dss.Clipper
