import Benchmarks.Dss.Clipper.TakeNoAdjustSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeOweGtTabVatFluxCallFailureSourceReverts {σ σ₀ A I}
    {g : UInt256}
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
      typedCallViaEVM config evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
        (false, evmVat, outVat) true)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt config { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract, locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals takeTransition.body .reverted (immStore v) := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
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
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
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
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt config startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt config usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? config ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt config ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt config stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt config doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config) (solm := doneFrame) (evm := evmPrice) (name := "price")
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
      ExecStmt config priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config) (solm := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt config lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config) (solm := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt config tabFrame evmPrice
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
        (calleeSolm :=
          { contract := contract, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I), immutables := immStore v })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail :
      ExecBlock config sliceFrame evmPrice
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            .ite
              (.binary .gt (.var "owe") (.var "tab"))
              [ .assign .localVar (varRef "owe") (.var "tab"),
                .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
              [ .ite
                (.binary .and (.binary .lt (.var "owe") (.var "tab"))
                  (.binary .lt (.var "slice") (.var "lot")))
                ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
                  wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
                  [ .ite
                    (.binary .lt (.var "remainingTab") (.var "_chost"))
                    ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                      wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                      [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                        .assign .localVar (varRef "slice")
                          (.binary .div (.var "owe") (.var "price")) ])
                    [] ])
                [] ] ] ++
          wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ] ++
          checkedExternalCallStmts vatExpr "flux" (.intLit 0)
            [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [sliceFrame, slice, lot, tab] using
      clipperTakeOweGtTabVatFluxCallFailureTailBlock v evmLock evmPrice evmVat I price
        slice hmul hgt hsliceLot hvatCode hcallVat
  have hblock :
      ExecBlock config startFrame evm0 takeTransition.body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, List.append_assoc] using
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

theorem clipperTakeOweGtTabVatFluxCallSuccessTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
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
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)]
        (true, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
      (clipperTakeSalesTabEVMWord evmRead I)
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts)
      (.ok
        (Frame.mk contract (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0
            slice' tabNew lotNew) (immStore v))
        evmVat) := by
  intro owe0 slice' tabNew lotNew
  let sliceFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v)
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v)
  let adjustedFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe0 slice') (immStore v)
  let postSubFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe0 slice'
        tabNew lotNew) (immStore v)
  let fluxFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew) (immStore v)
  have hmulBlock :
      ExecBlock config sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hite :
      ExecStmt config oweFrame evmRead clipperTakeOweAdjustmentStmt
        (.ok adjustedFrame evmRead) := by
    simpa [oweFrame, adjustedFrame, owe0, slice', clipperTakeOweAdjustmentStmt] using
      clipperTakeOweGtTabIte v evmLoc evmRead I price slice hgt
  have hsubBlock :
      ExecBlock config adjustedFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [adjustedFrame, postSubFrame, slice', tabNew, lotNew] using
      clipperTakePostOweGtTabSubBlock v evmLoc evmRead I price slice owe0 hsliceLot
  have hargs :
      evalExprs? config postSubFrame evmRead
        [ilkExpr, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice'.toNat)] := by
    simpa [postSubFrame, slice'] using
      clipperEvalTakeVatFluxBuyerArgs v evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew
  have hvatOk :
      ExecBlock config postSubFrame evmRead
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        (.ok fluxFrame evmVat) := by
    simpa [postSubFrame, fluxFrame, slice'] using
      clipperTakeVatFluxBuyerCallSuccessBlock v evmLoc evmRead evmVat I price slice
        owe0 owe0 slice' tabNew lotNew hvatCode hargs hcallVat
  have hafterIte :
      ExecBlock config oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts)
        (.ok fluxFrame evmVat) := by
    simpa [clipperTakePostOweFluxStmts] using
      ExecBlock.consNormal hite (execBlockAppendOk hsubBlock hvatOk)
  simpa [sliceFrame, fluxFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendOk hmulBlock hafterIte

end Benchmarks.Dss.Clipper
