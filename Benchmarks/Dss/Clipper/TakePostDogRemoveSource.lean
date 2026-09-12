import Benchmarks.Dss.Clipper.TakePostDogRemove

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- The common source tail after a successful `dog.digs` call.  Naming it keeps
   the callback and `_remove` case proofs from repeating the expanded AST. -/
def clipperTakePostDogStmts (v : ClipperImmutables) : List Stmt :=
  [ .ite
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

theorem clipperTakePostDogFluxRetRemoveArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    let fluxRetFrame : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_fluxUsrRet" .unit }
    evalExprs? (config v) fluxRetFrame evmFlux [.var "id"] =
      .ok [clipperYankArgValue I] := by
  intro fluxRetFrame
  have hid :=
    clipperEvalTakeVarIdAtDigsRet v evmLoc evmRead evmVat evmFlux I price slice
      owe0 owe slice' tabNew lotNew
  have hid' :
      evalExpr? (config v) fluxRetFrame evmFlux (.var "id") =
        .ok (clipperYankArgValue I) := by
    dsimp only [fluxRetFrame]
    simp only [evalExpr?]
    rw [store_get_ne
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
      (k := "_fluxUsrRet") (a := "id") .unit (by decide)]
    simpa only [evalExpr?, clipperTakeIdValue, clipperYankArgValue,
      clipperTakeIdWord, clipperYankArgWord] using hid
  exact evalExprs?_singleton hid'

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogTabZeroFluxRemoveSourceRevertsOfBody
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outFlux : ByteArray}
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
          .int (Int.ofNat lotNew.toNat)]
        (true, evmFlux, outFlux) true)
    (hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmFlux
        removeFunction.body .reverted) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog
      [ .ite
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
      .reverted := by
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  let fluxRetFrame : Frame :=
    { contract := contract v,
      locals := digsRetFrame.locals.insert "_fluxUsrRet" .unit }
  have hlotCond := clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroAtDigsRet_true v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have hargs := clipperEvalTakeVatFluxUsrArgsAtDigsRet v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew
  have hguard := clipperEvalTakeVatCodeGuard_true v evmDog digsRetFrame.locals hvatCode
  have hflux :
      ExecBlock (config v) digsRetFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        (.ok fluxRetFrame evmFlux) := by
    simpa [checkedExternalCallStmts, digsRetFrame, fluxRetFrame, collapseReturns] using
      (checkedExternalCallSuccess hguard
        (clipperEvalVat v evmDog digsRetFrame.locals) hargs hcallFlux
        (clipperTakeDecodeFluxVoid v outFlux))
  have hremove :
      ExecStmt (config v) fluxRetFrame evmFlux
        (.internalCall "_remove" [.var "id"] "_removeRet2") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config v) (caller := fluxRetFrame) (evm := evmFlux)
      (name := "_remove") (retVar := "_removeRet2") (args := [.var "id"])
      (argVals := [clipperYankArgValue I]) (callee := removeFunction)
      (locals := clipperYankRemoveStore I)
      (by
        simpa [fluxRetFrame, digsRetFrame] using
          (clipperTakePostDogFluxRetRemoveArgs v evmLoc evmRead evmVat evmFlux I
            price slice owe0 owe slice' tabNew lotNew))
      (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremoveBody
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        .reverted := by
    exact ExecStmt.iteTrue (by simpa [digsRetFrame] using htabCond)
      (execBlockAppendOk hflux (ExecBlock.consRevert hremove))
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        .reverted := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consRevert htabIte)
  exact ExecBlock.consRevert hlotIte

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogTabZeroFluxRemoveSourceOkOfBody
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux evmRemove : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256)
    {outFlux : ByteArray} {calleeSolm : Frame}
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
          .int (Int.ofNat lotNew.toNat)]
        (true, evmFlux, outFlux) true)
    (hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmFlux
        removeFunction.body (.returned calleeSolm evmRemove none)) :
    let frameRemoveRet : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_fluxUsrRet" .unit |>.insert
              "_removeRet2" .unit }
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog
      [ .ite
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
      (.ok frameRemoveRet
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro frameRemoveRet
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  let fluxRetFrame : Frame :=
    { contract := contract v,
      locals := digsRetFrame.locals.insert "_fluxUsrRet" .unit }
  have hlotCond := clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroAtDigsRet_true v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have hargs := clipperEvalTakeVatFluxUsrArgsAtDigsRet v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew
  have hguard := clipperEvalTakeVatCodeGuard_true v evmDog digsRetFrame.locals hvatCode
  have hflux :
      ExecBlock (config v) digsRetFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        (.ok fluxRetFrame evmFlux) := by
    simpa [checkedExternalCallStmts, digsRetFrame, fluxRetFrame, collapseReturns] using
      (checkedExternalCallSuccess hguard
        (clipperEvalVat v evmDog digsRetFrame.locals) hargs hcallFlux
        (clipperTakeDecodeFluxVoid v outFlux))
  have hremove :
      ExecStmt (config v) fluxRetFrame evmFlux
        (.internalCall "_remove" [.var "id"] "_removeRet2")
        (.ok frameRemoveRet evmRemove) := by
    simpa [resumeAfterInternalCall, fluxRetFrame, digsRetFrame, frameRemoveRet] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := fluxRetFrame) (evm := evmFlux)
        (name := "_remove") (retVar := "_removeRet2") (args := [.var "id"])
        (argVals := [clipperYankArgValue I]) (callee := removeFunction)
        (locals := clipperYankRemoveStore I) (calleeSolm := calleeSolm)
        (calleeEvm := evmRemove) (value := none)
        (by
          simpa [fluxRetFrame, digsRetFrame] using
            (clipperTakePostDogFluxRetRemoveArgs v evmLoc evmRead evmVat evmFlux I
              price slice owe0 owe slice' tabNew lotNew))
        (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremoveBody)
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteTrue (by simpa [digsRetFrame] using htabCond)
      (execBlockAppendOk hflux (ExecBlock.consNormal hremove ExecBlock.nil))
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hzero :
      evalExpr? (config v) frameRemoveRet evmRemove (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, frameRemoveRet]
  have hlocked : frameRemoveRet.locals.get? "locked" = none := by
    simp [frameRemoveRet]
  have hassign :
      assignStorageRef? (config v) frameRemoveRet evmRemove .storage lockedRef (.int 0) =
        .ok (frameRemoveRet,
          Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [frameRemoveRet] using
      assign_clipperLocked v evmRemove frameRemoveRet.locals hlocked ⟨0⟩
  have hunlock :
      ExecStmt (config v) frameRemoveRet evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecStmt.assign hzero hassign
  exact ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)

end Benchmarks.Dss.Clipper
