import Benchmarks.Dss.Clipper.TakeCallbackTailSource
import Benchmarks.Dss.Clipper.TakeOweVatMoveSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeOweGtTabCallbackTailSource
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb : EVM.State) (I : ExecutionEnv)
    (price slice : UInt256) {outVat : ByteArray}
    {callbackFrame : Frame} {result : ExecResult}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0
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
      ExecStmt config
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
        (.ok callbackFrame evmCb))
    (htail : ExecBlock config callbackFrame evmCb
      (checkedExternalCallStmts vatExpr "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet" ++
        clipperTakeAfterMoveStmts) result) :
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v))
      evmRead (clipperTakeAfterSliceStmts) result := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame := Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v)
  let fluxFrame := Frame.mk contract (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 slice'
      tabNew lotNew) (immStore v)
  let dogFrame := Frame.mk contract (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0 slice'
      tabNew lotNew) (immStore v)
  have hflux : ExecBlock config sliceFrame evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts)
      (.ok fluxFrame evmVat) := by
    simpa [sliceFrame, fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeOweGtTabVatFluxCallSuccessTailBlock v evmLoc evmRead evmVat I
        price slice hmul hgt hsliceLot hvatCode hcallVat
  have hletDog : ExecStmt config fluxFrame evmVat
      (.letDecl "dog_" (some addr) (.storage dogRef))
      (.ok dogFrame evmVat) := by
    simpa [fluxFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config) (solm := fluxFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [fluxFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0
                slice' tabNew lotNew)
              (by
                simp [clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
                  clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
                  clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
                  clipperTakeLocalsOweTab, clipperTakeLocalsOwe,
                  clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
                  clipperTakeLocalsTab, clipperTakeLocalsLot,
                  clipperTakeLocalsPrice, clipperTakeLocalsDone,
                  clipperTakeLocalsSt, clipperTakeLocalsTic,
                  clipperTakeLocalsUsr, clipperTakeStore])))
  have hcallback' : ExecStmt config dogFrame evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok callbackFrame evmCb) := by
    simpa [dogFrame, owe0, slice', tabNew, lotNew] using hcallback
  have hrest : ExecBlock config fluxFrame evmVat
      (clipperTakeAfterFluxStmts ++ clipperTakeAfterMoveStmts) result := by
    simpa [clipperTakeAfterFluxStmts, List.append_assoc] using
      ExecBlock.consNormal hletDog
        (ExecBlock.consNormal hcallback' htail)
  simpa [clipperTakeAfterSliceStmts, sliceFrame, List.append_assoc] using
    execBlockAppendOk hflux hrest

end Benchmarks.Dss.Clipper
