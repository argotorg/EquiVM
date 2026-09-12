import Benchmarks.Dss.Clipper.TakeCallbackContinuationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeVatMoveNoCodeBlockAtDogLoaded (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmVat
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (clipperEvalTakeVatCodeGuard_false v evmVat _ hnoCode))

theorem clipperTakeVatMoveCallFailureBlockAtDogLoaded (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
      [.address evmVat.executionEnv.source,
        .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
        .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (false, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmVat
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  let dogFrame := Frame.mk (contract v)
    (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hargs := clipperEvalTakeVatMoveArgs v evmLoc evmRead evmVat I price slice
    owe0 owe slice' tabNew lotNew
  simpa [checkedExternalCallStmts, dogFrame] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (clipperEvalTakeVatCodeGuard_true v evmVat dogFrame.locals hcode))
      (ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (clipperEvalVat v evmVat dogFrame.locals)
          (by simp [evalExpr?, pure]) (by simpa [dogFrame] using hargs) hcall))

theorem clipperTakeVatMoveCallSuccessBlockAtDogLoaded (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
      [.address evmVat.executionEnv.source,
        .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
        .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (true, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmVat
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet")
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove) := by
  let dogFrame := Frame.mk (contract v)
    (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hargs := clipperEvalTakeVatMoveArgs v evmLoc evmRead evmVat I price slice
    owe0 owe slice' tabNew lotNew
  simpa [checkedExternalCallStmts, dogFrame, clipperTakeLocalsMoveRet,
    collapseReturns] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (clipperEvalTakeVatCodeGuard_true v evmVat dogFrame.locals hcode))
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalVat v evmVat dogFrame.locals)
          (by simp [evalExpr?, pure]) (by simpa [dogFrame] using hargs) hcall
          (clipperTakeDecodeMoveVoid v outMove))
        ExecBlock.nil)

end Benchmarks.Dss.Clipper
