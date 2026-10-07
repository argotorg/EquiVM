import Benchmarks.Dss.Clipper.TakeChostVatFluxSource
import Benchmarks.Dss.Clipper.TakeOweVatMoveSource
import Benchmarks.Dss.Clipper.YankSuccessSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- These small combinators deliberately speak only about evaluated expressions.  The
   no-adjust and both chost branches retain different scratch locals, but the rest of
   `take` reads the same live variables.  Factoring the semantic control flow here avoids
   duplicating the callback/move/digs proof for each scratch-store layout. -/

theorem clipperTakeCallbackSkipOfEval
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    (hguard : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") vatExpr)
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool false)) :
    ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok (Frame.mk contract locals (immStore v)) evm) :=
  ExecStmt.iteFalse hguard ExecBlock.nil

theorem clipperTakeCallbackNoCodeOfEvals
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    (hguard : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") vatExpr)
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool true))
    (hcode : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) = .ok (.bool false)) :
    ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      .reverted := by
  apply ExecStmt.iteTrue hguard
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallVarNoCode (cfg := config) (C := contract)
      (receiver := "who") (retVar := "_clipperCallRet") (name := "clipperCall")
      (args := [sender, .var "owe", .var "slice", .var "data"]) hcode)

theorem clipperTakeCallbackFailureOfEvals
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {target : AccountAddress} {args : List Value} {out : ByteArray}
    (hguard : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") vatExpr)
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool true))
    (hcode : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) = .ok (.bool true))
    (htarget : locals.get? "who" = some (.address target))
    (hargs : evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [sender, .var "owe", .var "slice", .var "data"] = .ok args)
    (hcall : typedCallViaEVM config evm (EVM.address target) "clipperCall" 0 args
      (false, evm', out) true) :
    ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      .reverted := by
  apply ExecStmt.iteTrue hguard
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallVarFailure (cfg := config) (C := contract)
      (receiver := "who") (retVar := "_clipperCallRet") (name := "clipperCall")
      hcode htarget hargs hcall)

theorem clipperTakeCallbackSuccessOfEvals
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {target : AccountAddress} {args : List Value} {out : ByteArray}
    (hguard : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") vatExpr)
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool true))
    (hcode : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) = .ok (.bool true))
    (htarget : locals.get? "who" = some (.address target))
    (hargs : evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [sender, .var "owe", .var "slice", .var "data"] = .ok args)
    (hcall : typedCallViaEVM config evm (EVM.address target) "clipperCall" 0 args
      (true, evm', out) true) :
    ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok
        (Frame.mk contract (locals.insert "_clipperCallRet" .unit) (immStore v)) evm') := by
  apply ExecStmt.iteTrue hguard
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallVarSuccess (cfg := config) (C := contract)
      (receiver := "who") (retVar := "_clipperCallRet") (name := "clipperCall")
      hcode htarget hargs hcall (clipperTakeDecodeClipperCallVoid out))

theorem clipperTakeCheckedCallNoCodeOfEval
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {receiver : Expr} {name retVar : Ident} {args : List Expr}
    (hcode : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (checkedExternalCallStmts receiver name (.intLit 0) args retVar) .reverted := by
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallNoCode (cfg := config) (C := contract)
      (receiver := receiver) (retVar := retVar) (name := name) (args := args) hcode)

theorem clipperTakeCheckedCallFailureOfEvals
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {receiver : Expr} {name retVar : Ident} {argsExpr : List Expr}
    {target : AccountAddress} {args : List Value} {out : ByteArray}
    (hcode : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true))
    (htarget : evalExpr? config (Frame.mk contract locals (immStore v)) evm receiver =
      .ok (.address target))
    (hargs : evalExprs? config (Frame.mk contract locals (immStore v)) evm argsExpr = .ok args)
    (hcall : typedCallViaEVM config evm (EVM.address target) name 0 args
      (false, evm', out) true) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (checkedExternalCallStmts receiver name (.intLit 0) argsExpr retVar) .reverted := by
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallFailure (cfg := config) (C := contract)
      (receiver := receiver) (retVar := retVar) (name := name)
      hcode htarget hargs hcall)

theorem clipperTakeCheckedCallSuccessOfEvals
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {receiver : Expr} {name retVar : Ident} {argsExpr : List Expr}
    {target : AccountAddress} {args : List Value} {out : ByteArray}
    (hcode : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true))
    (htarget : evalExpr? config (Frame.mk contract locals (immStore v)) evm receiver =
      .ok (.address target))
    (hargs : evalExprs? config (Frame.mk contract locals (immStore v)) evm argsExpr = .ok args)
    (hcall : typedCallViaEVM config evm (EVM.address target) name 0 args
      (true, evm', out) true)
    (hdecode : config.externalABI.decode? name out = some []) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (checkedExternalCallStmts receiver name (.intLit 0) argsExpr retVar)
      (.ok (Frame.mk contract (locals.insert retVar .unit) (immStore v)) evm') := by
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallSuccess (cfg := config) (C := contract)
      (receiver := receiver) (retVar := retVar) (name := name)
      hcode htarget hargs hcall hdecode)

theorem clipperTakeAfterSliceOfPrefixAndContinuation
    {sliceFrame fluxFrame dogFrame callbackFrame : Frame}
    {evmRead evmVat evmCb : EVM.State} {result : ExecResult}
    (hflux : ExecBlock config sliceFrame evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts)
      (.ok fluxFrame evmVat))
    (hdog : ExecStmt config fluxFrame evmVat
      (.letDecl "dog_" (some addr) (.storage dogRef)) (.ok dogFrame evmVat))
    (hcallback : ExecStmt config dogFrame evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok callbackFrame evmCb))
    (htail : ExecBlock config callbackFrame evmCb
      (checkedExternalCallStmts vatExpr "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet" ++
        clipperTakeAfterMoveStmts) result) :
    ExecBlock config sliceFrame evmRead (clipperTakeAfterSliceStmts) result := by
  have hrest : ExecBlock config fluxFrame evmVat
      (clipperTakeAfterFluxStmts ++ clipperTakeAfterMoveStmts) result := by
    simpa [clipperTakeAfterFluxStmts, List.append_assoc] using
      ExecBlock.consNormal hdog (ExecBlock.consNormal hcallback htail)
  simpa [clipperTakeAfterSliceStmts, List.append_assoc] using
    execBlockAppendOk hflux hrest

theorem clipperTakeAfterSliceOfPrefixAndCallbackRevert
    {sliceFrame fluxFrame dogFrame : Frame}
    {evmRead evmVat : EVM.State}
    (hflux : ExecBlock config sliceFrame evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts)
      (.ok fluxFrame evmVat))
    (hdog : ExecStmt config fluxFrame evmVat
      (.letDecl "dog_" (some addr) (.storage dogRef)) (.ok dogFrame evmVat))
    (hcallback : ExecStmt config dogFrame evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") vatExpr)
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      .reverted) :
    ExecBlock config sliceFrame evmRead (clipperTakeAfterSliceStmts) .reverted := by
  have hrest : ExecBlock config fluxFrame evmVat
      (clipperTakeAfterFluxStmts ++ clipperTakeAfterMoveStmts) .reverted := by
    simpa [clipperTakeAfterFluxStmts] using
      ExecBlock.consNormal hdog (ExecBlock.consRevert hcallback)
  simpa [clipperTakeAfterSliceStmts, List.append_assoc] using
    execBlockAppendOk hflux hrest

/-! ## A scratch-local-independent successful suffix

The adjustment branches leave different, dead scratch variables in the local store.  The
remaining source program only observes the live variables listed below, so its proof is
parameterized by an arbitrary store rather than by any one adjustment layout. -/

abbrev clipperTakeGenericMoveRet (locals : Store) : Store :=
  locals.insert "_moveRet" .unit

abbrev clipperTakeGenericDigsRet (locals : Store) : Store :=
  (clipperTakeGenericMoveRet locals).insert "_digsRet" .unit

theorem clipperEvalTakeGenericVar
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {name : Ident} {value : Value} (hget : locals.get? name = some value) :
    evalExpr? config (Frame.mk contract locals (immStore v)) evm (.var name) = .ok value := by
  simp only [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) = .ok value
  rw [hget]
  rfl

theorem clipperEvalTakeGenericCallbackCodeGuard
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {who : AccountAddress}
    (hwho : locals.get? "who" = some (.address who)) :
    evalExpr? config (Frame.mk contract locals (immStore v)) evm
        (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) =
      .ok (.bool (0 < (UInt256.ofNat
        ((evm.lookupAccount who).option 0 (fun acc => acc.code.size))).toNat)) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, clipperEvalTakeGenericVar hwho,
    evalBinaryOp?, EVM.Word.ofNat]

theorem clipperEvalTakeGenericCallbackArgs
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {I : ExecutionEnv}
    {owe slice : UInt256}
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hslice : locals.get? "slice" = some (.int (Int.ofNat slice.toNat)))
    (hdata : locals.get? "data" = some (clipperTakeDataValue I)) :
    evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [sender, .var "owe", .var "slice", .var "data"] =
        .ok [.address evm.executionEnv.source, .int (Int.ofNat owe.toNat),
          .int (Int.ofNat slice.toNat), clipperTakeDataValue I] := by
  have hsender : evalExpr? config (Frame.mk contract locals (immStore v)) evm sender =
      .ok (.address evm.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  simp only [evalExprs?, hsender, clipperEvalTakeGenericVar howe,
    clipperEvalTakeGenericVar hslice, clipperEvalTakeGenericVar hdata,
    EvalResult.bind, bind, pure]

theorem clipperEvalTakeGenericLotEqZeroFalse
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {lot : UInt256}
    (hget : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hlot : lot ≠ ⟨0⟩) :
    evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
  have hnat : lot.toNat ≠ 0 := by
    intro hz
    apply hlot
    cases lot with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hz
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hget]
  change evalBinaryOp? .eq (.int (Int.ofNat lot.toNat)) (.int 0) = .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat lot.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat lot.toNat) == Value.int 0) = false by simp [hnat]]

theorem clipperEvalTakeGenericTabEqZeroFalse
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {tab : UInt256}
    (hget : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (htab : tab ≠ ⟨0⟩) :
    evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.binary .eq (.var "tab") (.intLit 0)) = .ok (.bool false) := by
  have hnat : tab.toNat ≠ 0 := by
    intro hz
    apply htab
    cases tab with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hz
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hget]
  change evalBinaryOp? .eq (.int (Int.ofNat tab.toNat)) (.int 0) = .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat tab.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat tab.toNat) == Value.int 0) = false by simp [hnat]]

theorem clipperEvalTakeGenericIlkOweArgs
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {owe : UInt256}
    (hget : locals.get? "owe" = some (.int (Int.ofNat owe.toNat))) :
    evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [ilkExpr, .var "owe"] = .ok [v.ilk, .int (Int.ofNat owe.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hbs, _⟩
  have hilk : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      ilkExpr = .ok v.ilk := by
    simp [evalExpr_ilkExpr, hbs, evalExpr?, pure]
  have howe := clipperEvalTakeGenericVar (v := v) (evm := evm) hget
  simp only [evalExprs?, hilk, howe, EvalResult.bind, bind, pure]

theorem clipperEvalTakeGenericVatMoveArgs
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State} {owe : UInt256}
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hvow : locals.get? "vow" = none) :
    evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [sender, .storage vowRef, .var "owe"] =
        .ok [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evm).toNat),
          .int (Int.ofNat owe.toNat)] := by
  have hsender : evalExpr? config (Frame.mk contract locals (immStore v)) evm sender =
      .ok (.address evm.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  have hvowEval : evalExpr? config (Frame.mk contract locals (immStore v)) evm
      (.storage vowRef) =
        .ok (.address (AccountAddress.ofNat (clipperTakeVowEVMWord evm).toNat)) := by
    simpa [clipperTakeVowEVMWord] using clipperEvalVow v evm locals hvow
  have howeEval := clipperEvalTakeGenericVar (v := v) (evm := evm) howe
  simp only [evalExprs?, hsender, hvowEval, howeEval, EvalResult.bind, bind, pure]

theorem clipperEvalTakeGenericDogTarget
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {dog : AccountAddress} (hget : locals.get? "dog_" = some (.address dog)) :
    evalExpr? config (Frame.mk contract locals (immStore v)) evm (.var "dog_") =
      .ok (.address dog) :=
  clipperEvalTakeGenericVar hget

theorem clipperTakeGenericVatMoveNoCode
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    (hcode : (UInt256.ofNat
      ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (checkedExternalCallStmts vatExpr "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet") .reverted := by
  exact clipperTakeCheckedCallNoCodeOfEval
    (clipperEvalTakeVatCodeGuard_false v evm locals hcode)

theorem clipperTakeGenericVatMoveFailure
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {owe : UInt256} {out : ByteArray}
    (hargs : evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [sender, .storage vowRef, .var "owe"] =
        .ok [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evm).toNat),
          .int (Int.ofNat owe.toNat)])
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address v.vat) "move" 0
      [.address evm.executionEnv.source,
        .address (AccountAddress.ofNat (clipperTakeVowEVMWord evm).toNat),
        .int (Int.ofNat owe.toNat)] (false, evm', out) true) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (checkedExternalCallStmts vatExpr "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet") .reverted := by
  exact clipperTakeCheckedCallFailureOfEvals
    (clipperEvalTakeVatCodeGuard_true v evm locals hcode)
    (clipperEvalVat v evm locals) hargs hcall

theorem clipperTakeGenericVatMoveSuccess
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {owe : UInt256} {out : ByteArray}
    (hargs : evalExprs? config (Frame.mk contract locals (immStore v)) evm
      [sender, .storage vowRef, .var "owe"] =
        .ok [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evm).toNat),
          .int (Int.ofNat owe.toNat)])
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address v.vat) "move" 0
      [.address evm.executionEnv.source,
        .address (AccountAddress.ofNat (clipperTakeVowEVMWord evm).toNat),
        .int (Int.ofNat owe.toNat)] (true, evm', out) true) :
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      (checkedExternalCallStmts vatExpr "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet")
      (.ok (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm') := by
  simpa [clipperTakeGenericMoveRet] using
    clipperTakeCheckedCallSuccessOfEvals
      (clipperEvalTakeVatCodeGuard_true v evm locals hcode)
      (clipperEvalVat v evm locals) hargs hcall (clipperTakeDecodeMoveVoid out)

theorem clipperTakeGenericDogNonzeroSuccess
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {dog : AccountAddress} {owe lot : UInt256} {out : ByteArray}
    (hdog : locals.get? "dog_" = some (.address dog))
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hlotNe : lot ≠ ⟨0⟩)
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount dog).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address dog) "digs" 0
      [v.ilk, .int (Int.ofNat owe.toNat)] (true, evm', out) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr, .var "owe"] "_digsRet") ]
      (.ok (Frame.mk contract (clipperTakeGenericDigsRet locals) (immStore v)) evm') := by
  have hdog' : (clipperTakeGenericMoveRet locals).get? "dog_" =
      some (.address dog) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hdog]
  have howe' : (clipperTakeGenericMoveRet locals).get? "owe" =
      some (.int (Int.ofNat owe.toNat)) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), howe]
  have hlot' : (clipperTakeGenericMoveRet locals).get? "lot" =
      some (.int (Int.ofNat lot.toNat)) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hlot]
  have hcond := clipperEvalTakeGenericLotEqZeroFalse (v := v) (evm := evm)
    hlot' hlotNe
  have hguard : evalExpr? config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind,
      clipperEvalTakeGenericDogTarget hdog', evalBinaryOp?, EVM.Word.ofNat, hcode]
  have hchecked := clipperTakeCheckedCallSuccessOfEvals (retVar := "_digsRet")
    hguard
    (clipperEvalTakeGenericDogTarget hdog')
    (clipperEvalTakeGenericIlkOweArgs (v := v) (evm := evm) howe')
    hcall (clipperTakeDecodeDigsVoid out)
  simpa [clipperTakeGenericDigsRet] using
    ExecBlock.consNormal (ExecStmt.iteFalse hcond hchecked) ExecBlock.nil

theorem clipperTakeGenericDogNonzeroNoCode
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {dog : AccountAddress} {lot : UInt256}
    (hdog : locals.get? "dog_" = some (.address dog))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hlotNe : lot ≠ ⟨0⟩)
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
  have hdog' : (clipperTakeGenericMoveRet locals).get? "dog_" =
      some (.address dog) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hdog]
  have hlot' : (clipperTakeGenericMoveRet locals).get? "lot" =
      some (.int (Int.ofNat lot.toNat)) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hlot]
  have hcond := clipperEvalTakeGenericLotEqZeroFalse (v := v) (evm := evm)
    hlot' hlotNe
  have hguard : evalExpr? config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind,
      clipperEvalTakeGenericDogTarget hdog', evalBinaryOp?, EVM.Word.ofNat, hcode]
  have hchecked := clipperTakeCheckedCallNoCodeOfEval
    (retVar := "_digsRet") (name := "digs")
    (args := [ilkExpr, .var "owe"]) hguard
  exact ExecBlock.consRevert (ExecStmt.iteFalse hcond hchecked)

theorem clipperTakeGenericDogNonzeroFailure
    {v : ClipperImmutables} {locals : Store} {evm evm' : EVM.State}
    {dog : AccountAddress} {owe lot : UInt256} {out : ByteArray}
    (hdog : locals.get? "dog_" = some (.address dog))
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hlotNe : lot ≠ ⟨0⟩)
    (hcode : 0 < (UInt256.ofNat
      ((evm.lookupAccount dog).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm (EVM.address dog) "digs" 0
      [v.ilk, .int (Int.ofNat owe.toNat)] (false, evm', out) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr, .var "owe"] "_digsRet") ] .reverted := by
  have hdog' : (clipperTakeGenericMoveRet locals).get? "dog_" =
      some (.address dog) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hdog]
  have howe' : (clipperTakeGenericMoveRet locals).get? "owe" =
      some (.int (Int.ofNat owe.toNat)) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), howe]
  have hlot' : (clipperTakeGenericMoveRet locals).get? "lot" =
      some (.int (Int.ofNat lot.toNat)) := by
    rw [clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hlot]
  have hcond := clipperEvalTakeGenericLotEqZeroFalse (v := v) (evm := evm)
    hlot' hlotNe
  have hguard : evalExpr? config
      (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evm
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind,
      clipperEvalTakeGenericDogTarget hdog', evalBinaryOp?, EVM.Word.ofNat, hcode]
  have hchecked := clipperTakeCheckedCallFailureOfEvals
    (retVar := "_digsRet") hguard
    (clipperEvalTakeGenericDogTarget hdog')
    (clipperEvalTakeGenericIlkOweArgs (v := v) (evm := evm) howe') hcall
  exact ExecBlock.consRevert (ExecStmt.iteFalse hcond hchecked)

theorem clipperTakeGenericAssignSalesTab
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv} {tab : UInt256}
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hsales : locals.get? "sales" = none) :
    assignStorageRef? config (Frame.mk contract locals (immStore v)) evm
      .storage (salesF (.var "id") "tab") (.int (Int.ofNat tab.toNat)) =
      .ok (Frame.mk contract locals (immStore v),
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (clipperTakeSalesTabSlot I) tab) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesTabRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesTabSlot I))
  · exact hsales
  · simp [clipperTakeSalesTabRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeGenericVar (v := v) (evm := evm) hid,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesTabSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesTabSlot I) tab

theorem clipperTakeGenericAssignSalesLot
    {v : ClipperImmutables} {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv} {lot : UInt256}
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hsales : locals.get? "sales" = none) :
    assignStorageRef? config (Frame.mk contract locals (immStore v)) evm
      .storage (salesF (.var "id") "lot") (.int (Int.ofNat lot.toNat)) =
      .ok (Frame.mk contract locals (immStore v),
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (clipperTakeSalesLotSlot I) lot) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesLotRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesLotSlot I))
  · exact hsales
  · simp [clipperTakeSalesLotRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeGenericVar (v := v) (evm := evm) hid,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesLotSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesLotSlot I) lot

theorem clipperTakeGenericPostDogNonzeroStore
    {locals : Store} {evm : EVM.State}
    {I : ExecutionEnv} {tab lot : UInt256}
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lot.toNat)))
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hlocked : locals.get? "locked" = none)
    (hsales : locals.get? "sales" = none)
    (htabNe : tab ≠ ⟨0⟩) (hlotNe : lot ≠ ⟨0⟩) :
    let evmTab := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (clipperTakeSalesTabSlot I) tab
    let evmLot := Solm.EVM.storageStore evmTab evmTab.executionEnv.codeOwner
      (clipperTakeSalesLotSlot I) lot
    ExecBlock config (Frame.mk contract locals (immStore v)) evm
      [ .ite
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
      (.ok (Frame.mk contract locals (immStore v))
        (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro evmTab evmLot
  have hlotCond := clipperEvalTakeGenericLotEqZeroFalse (v := v) (evm := evm)
    hlot hlotNe
  have htabCond := clipperEvalTakeGenericTabEqZeroFalse (v := v) (evm := evm)
    htab htabNe
  have htabEval := clipperEvalTakeGenericVar (v := v) (evm := evm) htab
  have htabStmt : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.assign .storage (salesF (.var "id") "tab") (.var "tab"))
      (.ok (Frame.mk contract locals (immStore v)) evmTab) :=
    ExecStmt.assign htabEval (by
      simpa [evmTab] using
        clipperTakeGenericAssignSalesTab (v := v) (evm := evm) hid hsales)
  have hlotEval := clipperEvalTakeGenericVar (v := v) (evm := evmTab) hlot
  have hlotStmt : ExecStmt config (Frame.mk contract locals (immStore v)) evmTab
      (.assign .storage (salesF (.var "id") "lot") (.var "lot"))
      (.ok (Frame.mk contract locals (immStore v)) evmLot) :=
    ExecStmt.assign hlotEval (by
      simpa [evmLot] using
        clipperTakeGenericAssignSalesLot (v := v) (evm := evmTab) hid hsales)
  have hstores := ExecBlock.consNormal htabStmt
    (ExecBlock.consNormal hlotStmt ExecBlock.nil)
  have htabIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite
        (.binary .eq (.var "tab") (.intLit 0))
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
          [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
        [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
          .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
      (.ok (Frame.mk contract locals (immStore v)) evmLot) :=
    ExecStmt.iteFalse htabCond hstores
  have hlotIte : ExecStmt config (Frame.mk contract locals (immStore v)) evm
      (.ite
        (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite
            (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
              [ilkExpr, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      (.ok (Frame.mk contract locals (immStore v)) evmLot) :=
    ExecStmt.iteFalse hlotCond (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hzero : evalExpr? config (Frame.mk contract locals (immStore v)) evmLot
      (.intLit 0) = .ok (.int 0) := by simp [evalExpr?, pure]
  have hunlockAssign : assignStorageRef? config
      (Frame.mk contract locals (immStore v)) evmLot .storage lockedRef (.int 0) =
      .ok (Frame.mk contract locals (immStore v),
        Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa using assign_clipperLocked v evmLot locals hlocked ⟨0⟩
  have hunlock := ExecStmt.assign hzero hunlockAssign
  exact ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)

end Benchmarks.Dss.Clipper
