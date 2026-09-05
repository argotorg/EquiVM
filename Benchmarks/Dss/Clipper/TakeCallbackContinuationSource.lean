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
        (.ok callbackFrame evmCb))
    (htail : ExecBlock (config v) callbackFrame evmCb
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet" ++
        clipperTakeAfterMoveStmts v) result) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead (clipperTakeAfterSliceStmts v) result := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame := Frame.mk (contract v)
    (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let fluxFrame := Frame.mk (contract v)
    (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 slice'
      tabNew lotNew)
  let dogFrame := Frame.mk (contract v)
    (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe0 slice'
      tabNew lotNew)
  have hflux : ExecBlock (config v) sliceFrame evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      (.ok fluxFrame evmVat) := by
    simpa [sliceFrame, fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeOweGtTabVatFluxCallSuccessTailBlock v evmLoc evmRead evmVat I
        price slice hmul hgt hsliceLot hvatCode hcallVat
  have hletDog : ExecStmt (config v) fluxFrame evmVat
      (.letDecl "dog_" (some addr) (.storage dogRef))
      (.ok dogFrame evmVat) := by
    simpa [fluxFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := fluxFrame) (evm := evmVat) (name := "dog_")
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
  have hcallback' : ExecStmt (config v) dogFrame evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok callbackFrame evmCb) := by
    simpa [dogFrame, owe0, slice', tabNew, lotNew] using hcallback
  have hrest : ExecBlock (config v) fluxFrame evmVat
      (clipperTakeAfterFluxStmts v ++ clipperTakeAfterMoveStmts v) result := by
    simpa [clipperTakeAfterFluxStmts, List.append_assoc] using
      ExecBlock.consNormal hletDog
        (ExecBlock.consNormal hcallback' htail)
  simpa [clipperTakeAfterSliceStmts, sliceFrame, List.append_assoc] using
    execBlockAppendOk hflux hrest

end Benchmarks.Dss.Clipper
