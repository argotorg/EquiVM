import Benchmarks.Dss.Clipper.TakeGenericContinuationSource
import Benchmarks.Dss.Clipper.TakePostDogRemoveSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeGenericDigsAmt (locals : Store) (tab owe : UInt256) : Store :=
  (clipperTakeGenericMoveRet locals).insert "digsAmt"
    (.int (Int.ofNat (UInt256.add tab owe).toNat))

abbrev clipperTakeGenericDigsAmtRet
    (locals : Store) (tab owe : UInt256) : Store :=
  (clipperTakeGenericDigsAmt locals tab owe).insert "_digsRet" .unit

theorem clipperEvalTakeGenericEqZeroTrue
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {name : Ident}
    (hget : locals.get? name = some (.int 0)) :
    evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .eq (.var name) (.intLit 0)) = .ok (.bool true) := by
  have hvar := clipperEvalTakeGenericVar (v := v) (evm := evm) hget
  simp only [evalExpr?, hvar, EvalResult.bind, bind, pure]
  rfl

theorem clipperEvalTakeGenericWrappedAdd
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {tab owe : UInt256}
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat))) :
    evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (wrap256 (.binary .add (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat (UInt256.add tab owe).toNat)) := by
  have hmodulus : (wordModulus : Int) ≠ 0 := by
    norm_num [wordModulus]
  have htabEval := clipperEvalTakeGenericVar (v := v) (evm := evm) htab
  have howeEval := clipperEvalTakeGenericVar (v := v) (evm := evm) howe
  simp [wrap256, evalExpr?, EvalResult.bind, bind, pure, htabEval, howeEval,
    evalBinaryOp?, hmodulus]
  rw [show (UInt256.add tab owe).toNat =
    (tab.toNat + owe.toNat) % UInt256.size by exact uadd_toNat tab owe]
  norm_num [wordModulus, UInt256.size]

theorem clipperEvalTakeGenericIlkDigsAmtArgs
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {tab owe : UInt256} :
    evalExprs? config
      (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm
      [ilkExpr, .var "digsAmt"] =
        .ok [v.ilk, .int (Int.ofNat (UInt256.add tab owe).toNat)] := by
  rcases v.ilk_wf with ⟨bs, hbs, _⟩
  have hilk : evalExpr? config
      (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm
      ilkExpr = .ok v.ilk := by
    simp [evalExpr_ilkExpr, hbs, evalExpr?, pure]
  have hdigs : evalExpr? config
      (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm
      (.var "digsAmt") =
        .ok (.int (Int.ofNat (UInt256.add tab owe).toNat)) := by
    apply clipperEvalTakeGenericVar
    simp [clipperTakeGenericDigsAmt]
  simp only [evalExprs?, hilk, hdigs, EvalResult.bind, bind, pure]

theorem clipperTakeGenericDogZeroNoCode
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {dog : AccountAddress} {tab owe lot : UInt256}
    (hdog : locals.get? "dog_" = some (.address dog))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hlotZero : lot = ⟨0⟩)
    (hcode : (UInt256.ofNat
      ((evm.lookupAccount dog).option 0 (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr, .var "owe"] "_digsRet") ] .reverted := by
  subst lot
  have hdog' : (clipperTakeGenericMoveRet locals).get? "dog_" =
      some (.address dog) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hdog
  have htab' : (clipperTakeGenericMoveRet locals).get? "tab" =
      some (.int (Int.ofNat tab.toNat)) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using htab
  have howe' : (clipperTakeGenericMoveRet locals).get? "owe" =
      some (.int (Int.ofNat owe.toNat)) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using howe
  have hlot' : (clipperTakeGenericMoveRet locals).get? "lot" = some (.int 0) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hlot
  have hcond := clipperEvalTakeGenericEqZeroTrue (v := v) (evm := evm) hlot'
  have hadd : ExecStmt config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      (.letDecl "digsAmt" (some uint256)
        (wrap256 (.binary .add (.var "tab") (.var "owe"))))
      (.ok (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm) := by
    simpa [clipperTakeGenericDigsAmt] using
      (ExecStmt.letDecl (clipperEvalTakeGenericWrappedAdd
        (v := v) (evm := evm) htab' howe'))
  have hdogAmt : (clipperTakeGenericDigsAmt locals tab owe).get? "dog_" =
      some (.address dog) := by
    rw [clipperTakeGenericDigsAmt, store_get_ne _ _ (by decide), hdog']
  have hguard : evalExpr? config
      (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind,
      clipperEvalTakeGenericDogTarget hdogAmt, evalBinaryOp?, EVM.Word.ofNat,
      hcode]
  have hchecked := clipperTakeCheckedCallNoCodeOfEval
    (retVar := "_digsRet") (name := "digs")
    (args := [ilkExpr, .var "digsAmt"]) hguard
  apply ExecBlock.consRevert
  exact ExecStmt.iteTrue hcond (by
    simpa [wrappingAddInto] using execBlockAppendOk
      (ExecBlock.consNormal hadd ExecBlock.nil) hchecked)

theorem clipperTakeGenericDogZeroFailure
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {dog : AccountAddress} {tab owe lot : UInt256} {out : ByteArray}
    (hdog : locals.get? "dog_" = some (.address dog))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hlotZero : lot = ⟨0⟩)
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount dog).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address dog) "digs" 0
      [v.ilk, .int (Int.ofNat (UInt256.add tab owe).toNat)]
      (false, evm', out) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr, .var "owe"] "_digsRet") ] .reverted := by
  subst lot
  have hdog' : (clipperTakeGenericMoveRet locals).get? "dog_" =
      some (.address dog) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hdog
  have htab' : (clipperTakeGenericMoveRet locals).get? "tab" =
      some (.int (Int.ofNat tab.toNat)) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using htab
  have howe' : (clipperTakeGenericMoveRet locals).get? "owe" =
      some (.int (Int.ofNat owe.toNat)) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using howe
  have hlot' : (clipperTakeGenericMoveRet locals).get? "lot" = some (.int 0) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hlot
  have hcond := clipperEvalTakeGenericEqZeroTrue (v := v) (evm := evm) hlot'
  have hadd : ExecStmt config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      (.letDecl "digsAmt" (some uint256)
        (wrap256 (.binary .add (.var "tab") (.var "owe"))))
      (.ok (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm) := by
    simpa [clipperTakeGenericDigsAmt] using
      (ExecStmt.letDecl (clipperEvalTakeGenericWrappedAdd
        (v := v) (evm := evm) htab' howe'))
  have hdogAmt : (clipperTakeGenericDigsAmt locals tab owe).get? "dog_" =
      some (.address dog) := by
    rw [clipperTakeGenericDigsAmt, store_get_ne _ _ (by decide), hdog']
  have hguard : evalExpr? config
      (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind,
      clipperEvalTakeGenericDogTarget hdogAmt, evalBinaryOp?, EVM.Word.ofNat,
      hcode]
  have hchecked := clipperTakeCheckedCallFailureOfEvals
    (retVar := "_digsRet") hguard
    (clipperEvalTakeGenericDogTarget hdogAmt)
    (clipperEvalTakeGenericIlkDigsAmtArgs
      (v := v) (evm := evm) (locals := locals)) hcall
  apply ExecBlock.consRevert
  exact ExecStmt.iteTrue hcond (by
    simpa [wrappingAddInto] using execBlockAppendOk
      (ExecBlock.consNormal hadd ExecBlock.nil) hchecked)

theorem clipperTakeGenericDogZeroSuccess
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {dog : AccountAddress} {tab owe lot : UInt256} {out : ByteArray}
    (hdog : locals.get? "dog_" = some (.address dog))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hlotZero : lot = ⟨0⟩)
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount dog).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address dog) "digs" 0
      [v.ilk, .int (Int.ofNat (UInt256.add tab owe).toNat)]
      (true, evm', out) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr, .var "owe"] "_digsRet") ]
      (.ok (Frame.mk contract
        (clipperTakeGenericDigsAmtRet locals tab owe) (immStore v)) evm') := by
  subst lot
  have hdog' : (clipperTakeGenericMoveRet locals).get? "dog_" =
      some (.address dog) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hdog
  have htab' : (clipperTakeGenericMoveRet locals).get? "tab" =
      some (.int (Int.ofNat tab.toNat)) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using htab
  have howe' : (clipperTakeGenericMoveRet locals).get? "owe" =
      some (.int (Int.ofNat owe.toNat)) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using howe
  have hlot' : (clipperTakeGenericMoveRet locals).get? "lot" = some (.int 0) := by
    simpa [clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hlot
  have hcond := clipperEvalTakeGenericEqZeroTrue (v := v) (evm := evm) hlot'
  have hadd : ExecStmt config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      (.letDecl "digsAmt" (some uint256)
        (wrap256 (.binary .add (.var "tab") (.var "owe"))))
      (.ok (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm) := by
    simpa [clipperTakeGenericDigsAmt] using
      (ExecStmt.letDecl (clipperEvalTakeGenericWrappedAdd
        (v := v) (evm := evm) htab' howe'))
  have hdogAmt : (clipperTakeGenericDigsAmt locals tab owe).get? "dog_" =
      some (.address dog) := by
    rw [clipperTakeGenericDigsAmt, store_get_ne _ _ (by decide), hdog']
  have hguard : evalExpr? config
      (Frame.mk contract (clipperTakeGenericDigsAmt locals tab owe) (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind,
      clipperEvalTakeGenericDogTarget hdogAmt, evalBinaryOp?, EVM.Word.ofNat,
      hcode]
  have hchecked := clipperTakeCheckedCallSuccessOfEvals
    (retVar := "_digsRet") hguard
    (clipperEvalTakeGenericDogTarget hdogAmt)
    (clipperEvalTakeGenericIlkDigsAmtArgs
      (v := v) (evm := evm) (locals := locals)) hcall
    (clipperTakeDecodeDigsVoid out)
  apply ExecBlock.consNormal
  · exact ExecStmt.iteTrue hcond (by
      simpa [wrappingAddInto, clipperTakeGenericDigsAmtRet] using
        execBlockAppendOk (ExecBlock.consNormal hadd ExecBlock.nil) hchecked)
  · exact ExecBlock.nil

theorem clipperEvalTakeGenericRemoveArgs
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {I : ExecutionEnv}
    (hid : locals.get? "id" = some (clipperTakeIdValue I)) :
    evalExprs? config (Frame.mk contract locals (immStore v)) evm [.var "id"] =
      .ok [clipperYankArgValue I] := by
  apply evalExprs?_singleton
  simpa [clipperTakeIdValue, clipperYankArgValue, clipperTakeIdWord,
    clipperYankArgWord] using
    (clipperEvalTakeGenericVar (v := v) (evm := evm) hid)

theorem clipperTakeGenericPostDogLotZeroReverts
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {I : ExecutionEnv}
    (hlot : locals.get? "lot" = some (.int 0))
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hremove : ExecFuncBody config
      { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
      evm removeFunction.body .reverted) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (clipperTakePostDogStmts) .reverted := by
  have hremoveStmt : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.internalCall "_remove" [.var "id"] "_removeRet") .reverted :=
    internalCallFunctionRevert
      (clipperEvalTakeGenericRemoveArgs (v := v) (evm := evm) hid)
      (clipperYankRemoveLookup) (clipperYankRemoveBind I) hremove
  have hcond := clipperEvalTakeGenericEqZeroTrue
    (v := v) (evm := evm) hlot
  have hite : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
              [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      .reverted := ExecStmt.iteTrue hcond (ExecBlock.consRevert hremoveStmt)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hite

theorem clipperTakeGenericPostDogLotZeroOk
    {v : ClipperImmutables} {locals : Store} {evm evmRemove : EVM.State}
    {I : ExecutionEnv} {callee : Frame}
    (hlot : locals.get? "lot" = some (.int 0))
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hlocked : locals.get? "locked" = none)
    (hremove : ExecFuncBody config
      { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
      evm removeFunction.body (.returned callee evmRemove none)) :
    let resultLocals := locals.insert "_removeRet" .unit
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (clipperTakePostDogStmts)
      (.ok (Frame.mk contract resultLocals (immStore v))
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro resultLocals
  have hremoveStmt : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.internalCall "_remove" [.var "id"] "_removeRet")
      (.ok (Frame.mk contract resultLocals (immStore v)) evmRemove) := by
    simpa [resultLocals, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (clipperEvalTakeGenericRemoveArgs (v := v) (evm := evm) hid)
        (clipperYankRemoveLookup) (clipperYankRemoveBind I) hremove)
  have hcond := clipperEvalTakeGenericEqZeroTrue
    (v := v) (evm := evm) hlot
  have hite : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
              [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      (.ok (Frame.mk contract resultLocals (immStore v)) evmRemove) :=
    ExecStmt.iteTrue hcond (ExecBlock.consNormal hremoveStmt ExecBlock.nil)
  have hlocked' : resultLocals.get? "locked" = none := by
    simpa [resultLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hlocked
  have hunlock : ExecStmt config (Frame.mk contract resultLocals (immStore v)) evmRemove
      (.assign .storage lockedRef (.intLit 0))
      (.ok (Frame.mk contract resultLocals (immStore v))
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    apply ExecStmt.assign (value := .int 0)
    · simp [evalExpr?, pure]
    · simpa using assign_clipperLocked v evmRemove resultLocals hlocked' ⟨0⟩
  simpa only [clipperTakePostDogStmts] using
    ExecBlock.consNormal hite (ExecBlock.consNormal hunlock ExecBlock.nil)

theorem clipperEvalTakeGenericVatFluxUsrArgs
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {usr : AccountAddress} {lot : UInt256}
    (husr : locals.get? "usr" = some (.address usr))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat))) :
    evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [ilkExpr, thisAddr, .var "usr", .var "lot"] =
        .ok [v.ilk, .address evm.executionEnv.codeOwner, .address usr,
          .int (Int.ofNat lot.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hbs, _⟩
  have hilk : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      ilkExpr = .ok v.ilk := by simp [evalExpr_ilkExpr, hbs, evalExpr?, pure]
  have hthis : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      thisAddr = .ok (.address evm.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have husrEval := clipperEvalTakeGenericVar (v := v) (evm := evm) husr
  have hlotEval := clipperEvalTakeGenericVar (v := v) (evm := evm) hlot
  simp only [evalExprs?, hilk, hthis, husrEval, hlotEval, EvalResult.bind,
    bind, pure]

theorem clipperTakeGenericPostDogTabZeroNoCode
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {tab lot : UInt256}
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (htabZero : tab = ⟨0⟩) (hlotNe : lot ≠ ⟨0⟩)
    (hcode : (UInt256.ofNat
      ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (clipperTakePostDogStmts) .reverted := by
  subst tab
  have hlotCond := clipperEvalTakeGenericLotEqZeroFalse
    (v := v) (evm := evm) hlot hlotNe
  have htabCond := clipperEvalTakeGenericEqZeroTrue
    (v := v) (evm := evm) (by simpa using htab)
  have hchecked := clipperTakeCheckedCallNoCodeOfEval
    (retVar := "_fluxUsrRet") (name := "flux")
    (args := [ilkExpr, thisAddr, .var "usr", .var "lot"])
    (clipperEvalTakeVatCodeGuard_false v evm locals hcode)
  have htabIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "tab") (.intLit 0))
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
          [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
        [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
          .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
      .reverted := ExecStmt.iteTrue htabCond (execBlockAppendReverted hchecked)
  have hlotIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
              [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      .reverted := ExecStmt.iteFalse hlotCond (ExecBlock.consRevert htabIte)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hlotIte

theorem clipperTakeGenericPostDogTabZeroFailure
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {usr : AccountAddress} {tab lot : UInt256} {out : ByteArray}
    (husr : locals.get? "usr" = some (.address usr))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (htabZero : tab = ⟨0⟩) (hlotNe : lot ≠ ⟨0⟩)
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address v.vat) "flux" 0
      [v.ilk, .address evm.executionEnv.codeOwner, .address usr,
        .int (Int.ofNat lot.toNat)] (false, evm', out) true) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (clipperTakePostDogStmts) .reverted := by
  subst tab
  have hlotCond := clipperEvalTakeGenericLotEqZeroFalse
    (v := v) (evm := evm) hlot hlotNe
  have htabCond := clipperEvalTakeGenericEqZeroTrue
    (v := v) (evm := evm) (by simpa using htab)
  have hchecked := clipperTakeCheckedCallFailureOfEvals
    (retVar := "_fluxUsrRet")
    (clipperEvalTakeVatCodeGuard_true v evm locals hcode)
    (clipperEvalVat v evm locals)
    (clipperEvalTakeGenericVatFluxUsrArgs (v := v) husr hlot) hcall
  have htabIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "tab") (.intLit 0))
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
          [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
        [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
          .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
      .reverted := ExecStmt.iteTrue htabCond (execBlockAppendReverted hchecked)
  have hlotIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
              [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      .reverted := ExecStmt.iteFalse hlotCond (ExecBlock.consRevert htabIte)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hlotIte

theorem clipperTakeGenericPostDogTabZeroRemoveReverts
    {v : ClipperImmutables} {locals : Store} {evm evmFlux : EVM.State}
    {I : ExecutionEnv} {usr : AccountAddress} {tab lot : UInt256}
    {out : ByteArray}
    (husr : locals.get? "usr" = some (.address usr))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (htabZero : tab = ⟨0⟩) (hlotNe : lot ≠ ⟨0⟩)
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address v.vat) "flux" 0
      [v.ilk, .address evm.executionEnv.codeOwner, .address usr,
        .int (Int.ofNat lot.toNat)] (true, evmFlux, out) true)
    (hremove : ExecFuncBody config
      { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
      evmFlux removeFunction.body .reverted) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (clipperTakePostDogStmts) .reverted := by
  subst tab
  let fluxLocals := locals.insert "_fluxUsrRet" .unit
  have hlotCond := clipperEvalTakeGenericLotEqZeroFalse
    (v := v) (evm := evm) hlot hlotNe
  have htabCond := clipperEvalTakeGenericEqZeroTrue
    (v := v) (evm := evm) (by simpa using htab)
  have hflux := clipperTakeCheckedCallSuccessOfEvals
    (retVar := "_fluxUsrRet")
    (clipperEvalTakeVatCodeGuard_true v evm locals hcode)
    (clipperEvalVat v evm locals)
    (clipperEvalTakeGenericVatFluxUsrArgs (v := v) husr hlot) hcall
    (clipperTakeDecodeFluxVoid out)
  have hid' : fluxLocals.get? "id" = some (clipperTakeIdValue I) := by
    simpa [fluxLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hid
  have hremoveStmt : ExecStmt config (Frame.mk contract fluxLocals (immStore v)) evmFlux
      (.internalCall "_remove" [.var "id"] "_removeRet2") .reverted :=
    internalCallFunctionRevert
      (clipperEvalTakeGenericRemoveArgs (v := v) (evm := evmFlux) hid')
      (clipperYankRemoveLookup) (clipperYankRemoveBind I) hremove
  have htabIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "tab") (.intLit 0))
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
          [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
        [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
          .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
      .reverted := ExecStmt.iteTrue htabCond
        (execBlockAppendOk (by simpa [fluxLocals] using hflux)
          (ExecBlock.consRevert hremoveStmt))
  have hlotIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
              [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      .reverted := ExecStmt.iteFalse hlotCond (ExecBlock.consRevert htabIte)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hlotIte

theorem clipperTakeGenericPostDogTabZeroRemoveOk
    {v : ClipperImmutables} {locals : Store} {evm evmFlux evmRemove : EVM.State}
    {I : ExecutionEnv} {usr : AccountAddress} {tab lot : UInt256}
    {out : ByteArray} {callee : Frame}
    (husr : locals.get? "usr" = some (.address usr))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hlocked : locals.get? "locked" = none)
    (htabZero : tab = ⟨0⟩) (hlotNe : lot ≠ ⟨0⟩)
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address v.vat) "flux" 0
      [v.ilk, .address evm.executionEnv.codeOwner, .address usr,
        .int (Int.ofNat lot.toNat)] (true, evmFlux, out) true)
    (hremove : ExecFuncBody config
      { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
      evmFlux removeFunction.body (.returned callee evmRemove none)) :
    let resultLocals := (locals.insert "_fluxUsrRet" .unit).insert
      "_removeRet2" .unit
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (clipperTakePostDogStmts)
      (.ok (Frame.mk contract resultLocals (immStore v))
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  subst tab
  intro resultLocals
  let fluxLocals := locals.insert "_fluxUsrRet" .unit
  have hlotCond := clipperEvalTakeGenericLotEqZeroFalse
    (v := v) (evm := evm) hlot hlotNe
  have htabCond := clipperEvalTakeGenericEqZeroTrue
    (v := v) (evm := evm) (by simpa using htab)
  have hflux := clipperTakeCheckedCallSuccessOfEvals
    (retVar := "_fluxUsrRet")
    (clipperEvalTakeVatCodeGuard_true v evm locals hcode)
    (clipperEvalVat v evm locals)
    (clipperEvalTakeGenericVatFluxUsrArgs (v := v) husr hlot) hcall
    (clipperTakeDecodeFluxVoid out)
  have hid' : fluxLocals.get? "id" = some (clipperTakeIdValue I) := by
    simpa [fluxLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hid
  have hremoveStmt : ExecStmt config (Frame.mk contract fluxLocals (immStore v)) evmFlux
      (.internalCall "_remove" [.var "id"] "_removeRet2")
      (.ok (Frame.mk contract resultLocals (immStore v)) evmRemove) := by
    simpa [fluxLocals, resultLocals, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (clipperEvalTakeGenericRemoveArgs (v := v) (evm := evmFlux) hid')
        (clipperYankRemoveLookup) (clipperYankRemoveBind I) hremove)
  have htabIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "tab") (.intLit 0))
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
          [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
        [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
          .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
      (.ok (Frame.mk contract resultLocals (immStore v)) evmRemove) :=
    ExecStmt.iteTrue htabCond
      (execBlockAppendOk (by simpa [fluxLocals] using hflux)
        (ExecBlock.consNormal hremoveStmt ExecBlock.nil))
  have hlotIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
              [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      (.ok (Frame.mk contract resultLocals (immStore v)) evmRemove) :=
    ExecStmt.iteFalse hlotCond (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hlocked' : resultLocals.get? "locked" = none := by
    simpa [resultLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hlocked
  have hunlock : ExecStmt config (Frame.mk contract resultLocals (immStore v)) evmRemove
      (.assign .storage lockedRef (.intLit 0))
      (.ok (Frame.mk contract resultLocals (immStore v))
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    apply ExecStmt.assign (value := .int 0)
    · simp [evalExpr?, pure]
    · simpa using assign_clipperLocked v evmRemove resultLocals hlocked' ⟨0⟩
  simpa only [clipperTakePostDogStmts] using
    ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)

end Benchmarks.Dss.Clipper
