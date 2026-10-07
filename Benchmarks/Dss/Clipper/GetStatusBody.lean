import Benchmarks.Dss.Clipper.GetStatusSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperGetStatusBodyReturnsRdivBranch (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM config evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : config.externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperGetStatusTopWord evm I ≠ ⟨0⟩) (done : Bool)
    (hdone :
      evalExpr? config
        { contract := contract,
          locals := clipperStatusRatioLocals (clipperGetStatusTicWord evm I)
            (clipperGetStatusTopWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)) price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I))
            (UInt256.div (UInt256.mul price clipperRayWord) (clipperGetStatusTopWord evm I)), immutables := immStore v }
        evmPrice (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool done)) :
    ExecTransitionBody config contract evm (clipperGetStatusStore I)
      getStatusTransition.body
      (.returned
        { contract := contract, locals := clipperGetStatusLocalsNeedsRedo evm I done price, immutables := immStore v }
        evmPrice
        (some [ .bool (clipperGetStatusNeedsRedo evm I done),
          .int (Int.ofNat price.toNat),
          .int (Int.ofNat (clipperGetStatusLotWord evmPrice I).toNat),
          .int (Int.ofNat (clipperGetStatusTabWord evmPrice I).toNat)])) (immStore v) := by
  let startFrame : Frame := { contract := contract, locals := clipperGetStatusStore I, immutables := immStore v }
  let usrFrame : Frame := { contract := contract, locals := clipperGetStatusLocalsUsr evm I, immutables := immStore v }
  let ticFrame : Frame := { contract := contract, locals := clipperGetStatusLocalsTic evm I, immutables := immStore v }
  let stFrame : Frame := { contract := contract, locals := clipperGetStatusLocalsSt evm I done price, immutables := immStore v }
  let doneFrame : Frame := { contract := contract, locals := clipperGetStatusLocalsDone evm I done price, immutables := immStore v }
  let priceFrame : Frame := { contract := contract, locals := clipperGetStatusLocalsPrice evm I done price, immutables := immStore v }
  let needsFrame : Frame := { contract := contract, locals := clipperGetStatusLocalsNeedsRedo evm I done price, immutables := immStore v }
  have hletUsr :
      ExecStmt config startFrame evm
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evm) := by
    simpa [startFrame, usrFrame, clipperGetStatusLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config) (solm := startFrame) (evm := evm) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat))
        (by simpa [startFrame, clipperGetStatusUsrWord] using
          clipperEvalGetStatusSalesUsr v evm I))
  have hletTic :
      ExecStmt config usrFrame evm
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evm) := by
    simpa [usrFrame, ticFrame, clipperGetStatusLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config) (solm := usrFrame) (evm := evm) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperGetStatusTicWord evm I).toNat))
        (by simpa [usrFrame] using clipperEvalGetStatusSalesTicAfterUsr v evm I))
  have hstatus :
      ExecStmt config ticFrame evm
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame] using
      clipperGetStatusStatusCallReturnsRdivBranch v I price hlePrice hcode hcall hdec
        hleDone htail hmul htop done hdone
  have hletDone :
      ExecStmt config stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperGetStatusLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool done)
        (by simpa [stFrame] using
          clipperEvalGetStatusDoneFromStatusAt v evm evmPrice I done price))
  have hletPrice :
      ExecStmt config doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperGetStatusLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalGetStatusPriceFromStatusAt v evm evmPrice I done price))
  have hletNeeds :
      ExecStmt config priceFrame evmPrice
        (.letDecl "needsRedo" (some boolTy)
          (.binary .and (.binary .ne (.var "usr") zeroAddr) (.var "done")))
        (.ok needsFrame evmPrice) := by
    simpa [priceFrame, needsFrame, clipperGetStatusLocalsNeedsRedo] using
      (ExecStmt.letDecl
        (cfg := config) (solm := priceFrame) (evm := evmPrice) (name := "needsRedo")
        (ty := some boolTy)
        (expr := .binary .and (.binary .ne (.var "usr") zeroAddr) (.var "done"))
        (value := .bool (clipperGetStatusNeedsRedo evm I done))
        (by simpa [priceFrame] using
          clipperEvalGetStatusNeedsRedoAt v evm evmPrice I done price))
  have hret :
      ExecBlock config needsFrame evmPrice
        [ .return [ .var "needsRedo", .var "price",
            .storage (salesF (.var "id") "lot"),
            .storage (salesF (.var "id") "tab") ] ]
        (.returned needsFrame evmPrice
          (some [ .bool (clipperGetStatusNeedsRedo evm I done),
            .int (Int.ofNat price.toNat),
            .int (Int.ofNat (clipperGetStatusLotWord evmPrice I).toNat),
            .int (Int.ofNat (clipperGetStatusTabWord evmPrice I).toNat)])) := by
    exact ExecBlock.consReturn
      (ExecStmt.return
        (by simpa [needsFrame] using
          clipperEvalGetStatusReturnValues v evm evmPrice I done price))
  simpa [getStatusTransition, nonpayable, startFrame, needsFrame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (solm' := startFrame) (evm' := evm)
        (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (solm' := usrFrame) (evm' := evm) hletUsr <|
      ExecBlock.consNormal (solm' := ticFrame) (evm' := evm) hletTic <|
      ExecBlock.consNormal (solm' := stFrame) (evm' := evmPrice) hstatus <|
      ExecBlock.consNormal (solm' := doneFrame) (evm' := evmPrice) hletDone <|
      ExecBlock.consNormal (solm' := priceFrame) (evm' := evmPrice) hletPrice <|
      ExecBlock.consNormal (solm' := needsFrame) (evm' := evmPrice) hletNeeds hret)

end Benchmarks.Dss.Clipper
