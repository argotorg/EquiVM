import Benchmarks.Dss.Clipper.Arithmetic
import Benchmarks.Dss.Clipper.Sales
import Benchmarks.Dss.Clipper.UintEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

abbrev clipperGetStatusArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperGetStatusArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperGetStatusArgWord I).toNat)

abbrev clipperGetStatusStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (clipperGetStatusArgValue I)

abbrev clipperGetStatusArgKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (clipperGetStatusArgWord I).toNat)

abbrev clipperGetStatusSalesBaseSlot (I : ExecutionEnv) : UInt256 :=
  salesBase (clipperGetStatusArgKey I)

abbrev clipperGetStatusSalesTabSlot (I : ExecutionEnv) : UInt256 :=
  clipperGetStatusSalesBaseSlot I + ⟨1⟩

abbrev clipperGetStatusSalesLotSlot (I : ExecutionEnv) : UInt256 :=
  clipperGetStatusSalesBaseSlot I + ⟨2⟩

abbrev clipperGetStatusSalesPackedSlot (I : ExecutionEnv) : UInt256 :=
  clipperGetStatusSalesBaseSlot I + ⟨3⟩

abbrev clipperGetStatusSalesTopSlot (I : ExecutionEnv) : UInt256 :=
  clipperGetStatusSalesBaseSlot I + ⟨4⟩

abbrev clipperGetStatusSalesTabRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperGetStatusArgKey I), .field "tab"] }

abbrev clipperGetStatusSalesLotRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperGetStatusArgKey I), .field "lot"] }

abbrev clipperGetStatusSalesUsrRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperGetStatusArgKey I), .field "usr"] }

abbrev clipperGetStatusSalesTicRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperGetStatusArgKey I), .field "tic"] }

abbrev clipperGetStatusSalesTopRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperGetStatusArgKey I), .field "top"] }

abbrev clipperGetStatusUsrWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperGetStatusSalesPackedSlot I))
    solcAddrMask

abbrev clipperGetStatusTicWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  clipperSalesPackedTicWord
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperGetStatusSalesPackedSlot I))

abbrev clipperGetStatusTopWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperGetStatusSalesTopSlot I)

abbrev clipperGetStatusLotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperGetStatusSalesLotSlot I)

abbrev clipperGetStatusTabWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperGetStatusSalesTabSlot I)

abbrev clipperGetStatusLocalsUsr (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperGetStatusStore I).insert "usr"
    (.address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat))

abbrev clipperGetStatusLocalsTic (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperGetStatusLocalsUsr evm I).insert "tic"
    (.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat))

abbrev clipperGetStatusLocalsSt
    (evm : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) : Store :=
  (clipperGetStatusLocalsTic evm I).insert "st"
    (.tuple [.bool done, .int (Int.ofNat price.toNat)])

abbrev clipperGetStatusLocalsDone
    (evm : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) : Store :=
  (clipperGetStatusLocalsSt evm I done price).insert "done" (.bool done)

abbrev clipperGetStatusLocalsPrice
    (evm : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) : Store :=
  (clipperGetStatusLocalsDone evm I done price).insert "price"
    (.int (Int.ofNat price.toNat))

abbrev clipperGetStatusNeedsRedo (evm : EVM.State) (I : ExecutionEnv)
    (done : Bool) : Bool :=
  (!(Value.address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat) ==
    Value.address (AccountAddress.ofNat 0))) && done

abbrev clipperGetStatusLocalsNeedsRedo
    (evm : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) : Store :=
  (clipperGetStatusLocalsPrice evm I done price).insert "needsRedo"
    (.bool (clipperGetStatusNeedsRedo evm I done))

abbrev clipperStatusLocals (tic top : UInt256) : Store :=
  ((∅ : Store).insert "top" (.int (Int.ofNat top.toNat))).insert "tic"
    (.int (Int.ofNat tic.toNat))

abbrev clipperTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev clipperStatusAgeForPriceLocals (tic top age : UInt256) : Store :=
  (clipperStatusLocals tic top).insert "ageForPrice" (.int (Int.ofNat age.toNat))

abbrev clipperStatusPriceLocals (tic top age price : UInt256) : Store :=
  (clipperStatusAgeForPriceLocals tic top age).insert "price"
    (.int (Int.ofNat price.toNat))

abbrev clipperStatusAgeForDoneLocals (tic top ageForPrice price ageForDone : UInt256) :
    Store :=
  (clipperStatusPriceLocals tic top ageForPrice price).insert "ageForDone"
    (.int (Int.ofNat ageForDone.toNat))

abbrev clipperStatusDoneLocals (tic top ageForPrice price ageForDone : UInt256) :
    Store :=
  (clipperStatusAgeForDoneLocals tic top ageForPrice price ageForDone).insert "done"
    (.bool false)

abbrev clipperStatusDoneTrueLocals (tic top ageForPrice price ageForDone : UInt256) :
    Store :=
  (clipperStatusDoneLocals tic top ageForPrice price ageForDone).insert "done" (.bool true)

abbrev clipperStatusRatioLocals
    (tic top ageForPrice price ageForDone ratio : UInt256) : Store :=
  (clipperStatusDoneLocals tic top ageForPrice price ageForDone).insert "ratio"
    (.int (Int.ofNat ratio.toNat))

abbrev clipperStatusDoneFromRatioLocals
    (tic top ageForPrice price ageForDone ratio : UInt256) (done : Bool) : Store :=
  (clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio).insert "done"
    (.bool done)

abbrev clipperStatusCalcWord (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩) solcAddrMask

abbrev clipperStatusCalcAddress (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofUInt256 (clipperStatusCalcWord evm)

abbrev clipperStatusTailWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩

abbrev clipperStatusCuspWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩

theorem clipperGetStatusLocalsTic_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (clipperGetStatusLocalsTic evm I).get? "id" = some (clipperGetStatusArgValue I) := by
  simp only [clipperGetStatusLocalsTic, clipperGetStatusLocalsUsr, clipperGetStatusStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem clipperEvalTimestamp (v : ClipperImmutables) (evm : EVM.State) (locals : Store) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.env .timestamp) =
      .ok (.int (Int.ofNat (clipperTimestampWord evm).toNat)) := by
  simp [evalExpr?, envValue, clipperTimestampWord, pure]

theorem clipperEvalStatusVarTic (v : ClipperImmutables) (evm : EVM.State)
    (tic top : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperStatusLocals tic top }
      evm (.var "tic") = .ok (.int (Int.ofNat tic.toNat)) := by
  simp only [evalExpr?, clipperStatusLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalStatusVarTop (v : ClipperImmutables) (evm : EVM.State)
    (tic top : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperStatusLocals tic top }
      evm (.var "top") = .ok (.int (Int.ofNat top.toNat)) := by
  simp only [evalExpr?, clipperStatusLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusAgeArgs (v : ClipperImmutables) (evm : EVM.State)
    (tic top : UInt256) :
    evalExprs? (config v) { contract := contract v, locals := clipperStatusLocals tic top }
      evm [.env .timestamp, .var "tic"] =
      .ok [.int (Int.ofNat (clipperTimestampWord evm).toNat),
        .int (Int.ofNat tic.toNat)] := by
  simp only [evalExprs?, clipperEvalTimestamp, clipperEvalStatusVarTic, bind,
    EvalResult.bind, pure]

theorem clipperStatusAgeForPriceCallReturns (v : ClipperImmutables) (evm : EVM.State)
    (tic top : UInt256) (hle : tic.toNat ≤ (clipperTimestampWord evm).toNat) :
    ExecStmt (config v) { contract := contract v, locals := clipperStatusLocals tic top } evm
      (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice")
      (.ok
        { contract := contract v,
          locals :=
            clipperStatusAgeForPriceLocals tic top
              (UInt256.sub (clipperTimestampWord evm) tic) }
        evm) := by
  simpa [resumeAfterInternalCall, clipperStatusAgeForPriceLocals] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperStatusLocals tic top })
      (evm := evm) (calleeEvm := evm)
      (name := "sub") (retVar := "ageForPrice")
      (args := [.env .timestamp, .var "tic"])
      (argVals := [.int (Int.ofNat (clipperTimestampWord evm).toNat),
        .int (Int.ofNat tic.toNat)])
      (callee := subFunction)
      (locals := clipperUintBinaryLocals (clipperTimestampWord evm) tic)
      (calleeSolm :=
        { contract := contract v,
          locals := clipperUintBinaryLocalsZ (clipperTimestampWord evm) tic
            (UInt256.sub (clipperTimestampWord evm) tic) })
      (value := some [.int (Int.ofNat
        (UInt256.sub (clipperTimestampWord evm) tic).toNat)])
      (clipperEvalStatusAgeArgs v evm tic top)
      (clipperLookupSubFunction v)
      (clipperBindParamsSub (clipperTimestampWord evm) tic)
      (clipperSubFunctionReturns v evm (clipperTimestampWord evm) tic hle))

theorem clipperStatusAgeForPriceCallReverts (v : ClipperImmutables) (evm : EVM.State)
    (tic top : UInt256) (hlt : (clipperTimestampWord evm).toNat < tic.toNat) :
    ExecStmt (config v) { contract := contract v, locals := clipperStatusLocals tic top } evm
      (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperStatusLocals tic top })
      (evm := evm)
      (name := "sub") (retVar := "ageForPrice")
      (args := [.env .timestamp, .var "tic"])
      (argVals := [.int (Int.ofNat (clipperTimestampWord evm).toNat),
        .int (Int.ofNat tic.toNat)])
      (callee := subFunction)
      (locals := clipperUintBinaryLocals (clipperTimestampWord evm) tic)
      (clipperEvalStatusAgeArgs v evm tic top)
      (clipperLookupSubFunction v)
      (clipperBindParamsSub (clipperTimestampWord evm) tic)
      (clipperSubFunctionReverts v evm (clipperTimestampWord evm) tic hlt)

theorem clipperEvalStatusCalcTarget (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "calc" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage calcRef) = .ok (.address (clipperStatusCalcAddress evm)) := by
  let er : EvaledStorageRef := { base := "calc", steps := [] }
  have her : evalStorageRef (config v) { contract := contract v, locals := locals } evm
      calcRef = .ok er := by
    unfold evalStorageRef calcRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem .address) := by
    simp [er, storageTypeAt?, contract, storageDecls, addrSt]
  have hloc : (config v).storage.layout er = fun _ => some (addrLoc ⟨4⟩) := by
    funext evm'
    rfl
  have hload := evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_address evm ⟨4⟩)
  simpa [clipperStatusCalcAddress, clipperStatusCalcWord,
    accountAddress_ofUInt256_eq_ofNat_toNat] using hload

theorem clipperEvalStatusCalcCodeGuard_false (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "calc" = none)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage calcRef)) (.intLit 0)) =
        .ok (.bool false) := by
  have hnoCode' :
      (EVM.Word.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
    simpa using hnoCode
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalStatusCalcTarget v evm locals hbase,
    evalBinaryOp?, hnoCode']

theorem clipperEvalStatusCalcCodeGuard_true (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "calc" = none)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage calcRef)) (.intLit 0)) =
        .ok (.bool true) := by
  have hcode' :
      0 < (EVM.Word.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat := by
    simpa using hcode
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalStatusCalcTarget v evm locals hbase,
    evalBinaryOp?, hcode']

theorem clipperStatusAgeForPriceLocals_get_calc (tic top age : UInt256) :
    (clipperStatusAgeForPriceLocals tic top age).get? "calc" = none := by
  simp only [clipperStatusAgeForPriceLocals, clipperStatusLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem clipperEvalStatusVarTopAfterAge (v : ClipperImmutables) (evm : EVM.State)
    (tic top age : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top age } evm
      (.var "top") = .ok (.int (Int.ofNat top.toNat)) := by
  simp only [evalExpr?, clipperStatusAgeForPriceLocals, clipperStatusLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusVarAgeForPrice (v : ClipperImmutables) (evm : EVM.State)
    (tic top age : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top age } evm
      (.var "ageForPrice") = .ok (.int (Int.ofNat age.toNat)) := by
  simp only [evalExpr?, clipperStatusAgeForPriceLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalStatusPriceArgs (v : ClipperImmutables) (evm : EVM.State)
    (tic top age : UInt256) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top age } evm
      [.var "top", .var "ageForPrice"] =
      .ok [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)] := by
  simp only [evalExprs?, clipperEvalStatusVarTopAfterAge,
    clipperEvalStatusVarAgeForPrice, bind, EvalResult.bind, pure]

theorem clipperStatusPriceCallNoCode (v : ClipperImmutables) (evm : EVM.State)
    (tic top age : UInt256)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperStatusAgeForPriceLocals tic top age } : Frame)
      evm
      (checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
        [.var "top", .var "ageForPrice"] "price" (perm := false)) .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config v) (C := contract v) (evm := evm)
      (locals := clipperStatusAgeForPriceLocals tic top age)
      (receiver := .storage calcRef) (retVar := "price") (name := "price")
      (sendVal := 0) (args := [.var "top", .var "ageForPrice"]) (perm := false)
      (clipperEvalStatusCalcCodeGuard_false v evm
        (clipperStatusAgeForPriceLocals tic top age)
        (clipperStatusAgeForPriceLocals_get_calc tic top age) hnoCode)

theorem clipperStatusPriceCallFailure (v : ClipperImmutables) {evm evm' : EVM.State}
    (tic top age : UInt256) {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0 [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)]
        (false, evm', out) false) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperStatusAgeForPriceLocals tic top age } : Frame)
      evm
      (checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
        [.var "top", .var "ageForPrice"] "price" (perm := false)) .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evm')
      (locals := clipperStatusAgeForPriceLocals tic top age)
      (receiver := .storage calcRef) (retVar := "price") (name := "price")
      (target := clipperStatusCalcAddress evm) (sendVal := 0)
      (args := [.var "top", .var "ageForPrice"])
      (argVals := [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)])
      (out := out) (perm := false)
      (clipperEvalStatusCalcCodeGuard_true v evm
        (clipperStatusAgeForPriceLocals tic top age)
        (clipperStatusAgeForPriceLocals_get_calc tic top age) hcode)
      (clipperEvalStatusCalcTarget v evm
        (clipperStatusAgeForPriceLocals tic top age)
        (clipperStatusAgeForPriceLocals_get_calc tic top age))
      (clipperEvalStatusPriceArgs v evm tic top age)
      hcall

theorem clipperStatusPriceCallReturns (v : ClipperImmutables) {evm evm' : EVM.State}
    (tic top age price : UInt256) {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0 [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)]
        (true, evm', out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)]) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperStatusAgeForPriceLocals tic top age } : Frame)
      evm
      (checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
        [.var "top", .var "ageForPrice"] "price" (perm := false))
      (.ok ({ contract := contract v, locals := clipperStatusPriceLocals tic top age price } : Frame)
        evm') := by
  simpa [checkedExternalCallStmts, clipperStatusPriceLocals] using
    checkedExternalCallSuccess
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evm')
      (locals := clipperStatusAgeForPriceLocals tic top age)
      (receiver := .storage calcRef) (retVar := "price") (name := "price")
      (target := clipperStatusCalcAddress evm) (sendVal := 0)
      (args := [.var "top", .var "ageForPrice"])
      (argVals := [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)])
      (out := out) (perm := false) (value := [.int (Int.ofNat price.toNat)])
      (clipperEvalStatusCalcCodeGuard_true v evm
        (clipperStatusAgeForPriceLocals tic top age)
        (clipperStatusAgeForPriceLocals_get_calc tic top age) hcode)
      (clipperEvalStatusCalcTarget v evm
        (clipperStatusAgeForPriceLocals tic top age)
        (clipperStatusAgeForPriceLocals_get_calc tic top age))
      (clipperEvalStatusPriceArgs v evm tic top age)
      hcall
      hdec

theorem clipperStatusPriceCallDecodeReverts (v : ClipperImmutables) {evm evm' : EVM.State}
    (tic top age : UInt256) {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0 [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)]
        (true, evm', out) false)
    (hdec : (config v).externalABI.decode? "price" out = none) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperStatusAgeForPriceLocals tic top age } : Frame)
      evm
      (checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
        [.var "top", .var "ageForPrice"] "price" (perm := false)) .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evm')
      (locals := clipperStatusAgeForPriceLocals tic top age)
      (receiver := .storage calcRef) (retVar := "price") (name := "price")
      (target := clipperStatusCalcAddress evm) (sendVal := 0)
      (args := [.var "top", .var "ageForPrice"])
      (argVals := [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)])
      (out := out) (perm := false)
      (clipperEvalStatusCalcCodeGuard_true v evm
        (clipperStatusAgeForPriceLocals tic top age)
        (clipperStatusAgeForPriceLocals_get_calc tic top age) hcode)
      (clipperEvalStatusCalcTarget v evm
        (clipperStatusAgeForPriceLocals tic top age)
        (clipperStatusAgeForPriceLocals_get_calc tic top age))
      (clipperEvalStatusPriceArgs v evm tic top age)
      hcall
      hdec

theorem clipperEvalStatusVarTicAfterPrice (v : ClipperImmutables) (evm : EVM.State)
    (tic top age price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperStatusPriceLocals tic top age price } evm
      (.var "tic") = .ok (.int (Int.ofNat tic.toNat)) := by
  simp only [evalExpr?, clipperStatusPriceLocals, clipperStatusAgeForPriceLocals,
    clipperStatusLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusAgeForDoneArgs (v : ClipperImmutables) (evm : EVM.State)
    (tic top age price : UInt256) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperStatusPriceLocals tic top age price } evm
      [.env .timestamp, .var "tic"] =
      .ok [.int (Int.ofNat (clipperTimestampWord evm).toNat),
        .int (Int.ofNat tic.toNat)] := by
  simp only [evalExprs?, clipperEvalTimestamp, clipperEvalStatusVarTicAfterPrice, bind,
    EvalResult.bind, pure]

theorem clipperStatusAgeForDoneCallReturns (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price : UInt256)
    (hle : tic.toNat ≤ (clipperTimestampWord evm).toNat) :
    ExecStmt (config v)
      { contract := contract v,
        locals := clipperStatusPriceLocals tic top ageForPrice price } evm
      (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone")
      (.ok
        { contract := contract v,
          locals :=
            clipperStatusAgeForDoneLocals tic top ageForPrice price
              (UInt256.sub (clipperTimestampWord evm) tic) }
        evm) := by
  simpa [resumeAfterInternalCall, clipperStatusAgeForDoneLocals] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller :=
        { contract := contract v,
          locals := clipperStatusPriceLocals tic top ageForPrice price })
      (evm := evm) (calleeEvm := evm)
      (name := "sub") (retVar := "ageForDone")
      (args := [.env .timestamp, .var "tic"])
      (argVals := [.int (Int.ofNat (clipperTimestampWord evm).toNat),
        .int (Int.ofNat tic.toNat)])
      (callee := subFunction)
      (locals := clipperUintBinaryLocals (clipperTimestampWord evm) tic)
      (calleeSolm :=
        { contract := contract v,
          locals := clipperUintBinaryLocalsZ (clipperTimestampWord evm) tic
            (UInt256.sub (clipperTimestampWord evm) tic) })
      (value := some [.int (Int.ofNat
        (UInt256.sub (clipperTimestampWord evm) tic).toNat)])
      (clipperEvalStatusAgeForDoneArgs v evm tic top ageForPrice price)
      (clipperLookupSubFunction v)
      (clipperBindParamsSub (clipperTimestampWord evm) tic)
      (clipperSubFunctionReturns v evm (clipperTimestampWord evm) tic hle))

theorem clipperStatusAgeForDoneCallReverts (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price : UInt256)
    (hlt : (clipperTimestampWord evm).toNat < tic.toNat) :
    ExecStmt (config v)
      { contract := contract v,
        locals := clipperStatusPriceLocals tic top ageForPrice price } evm
      (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller :=
        { contract := contract v,
          locals := clipperStatusPriceLocals tic top ageForPrice price })
      (evm := evm)
      (name := "sub") (retVar := "ageForDone")
      (args := [.env .timestamp, .var "tic"])
      (argVals := [.int (Int.ofNat (clipperTimestampWord evm).toNat),
        .int (Int.ofNat tic.toNat)])
      (callee := subFunction)
      (locals := clipperUintBinaryLocals (clipperTimestampWord evm) tic)
      (clipperEvalStatusAgeForDoneArgs v evm tic top ageForPrice price)
      (clipperLookupSubFunction v)
      (clipperBindParamsSub (clipperTimestampWord evm) tic)
      (clipperSubFunctionReverts v evm (clipperTimestampWord evm) tic hlt)

theorem clipperStatusAgeForDoneLocals_get_tail (tic top ageForPrice price ageForDone :
    UInt256) :
    (clipperStatusAgeForDoneLocals tic top ageForPrice price ageForDone).get? "tail" =
      none := by
  simp only [clipperStatusAgeForDoneLocals, clipperStatusPriceLocals,
    clipperStatusAgeForPriceLocals, clipperStatusLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem clipperStatusDoneLocals_get_tail (tic top ageForPrice price ageForDone : UInt256) :
    (clipperStatusDoneLocals tic top ageForPrice price ageForDone).get? "tail" = none := by
  simp only [clipperStatusDoneLocals]
  rw [store_get_ne _ _ (by decide)]
  exact clipperStatusAgeForDoneLocals_get_tail tic top ageForPrice price ageForDone

theorem clipperEvalStatusTail (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "tail" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage tailRef) =
      .ok (.int (Int.ofNat (clipperStatusTailWord evm).toNat)) := by
  let er : EvaledStorageRef := { base := "tail", steps := [] }
  have her : evalStorageRef (config v) { contract := contract v, locals := locals } evm
      tailRef = .ok er := by
    unfold evalStorageRef tailRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, uint256St]
  have hloc : (config v).storage.layout er = fun _ => some (wordLoc ⟨6⟩) := by
    funext evm'
    rfl
  simpa [clipperStatusTailWord] using
    evalExpr_storage_scalar_value hbase her hty hloc
      (clipperStorageLocLoad_uint256 evm ⟨6⟩)

theorem clipperEvalStatusVarAgeForDoneAfterDone (v : ClipperImmutables)
    (evm : EVM.State) (tic top ageForPrice price ageForDone : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
      (.var "ageForDone") = .ok (.int (Int.ofNat ageForDone.toNat)) := by
  simp only [evalExpr?, clipperStatusDoneLocals, clipperStatusAgeForDoneLocals,
    clipperStatusPriceLocals, clipperStatusAgeForPriceLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusDoneTailCond_true (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256)
    (hlt : (clipperStatusTailWord evm).toNat < ageForDone.toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
      (.binary .gt (.var "ageForDone") (.storage tailRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    clipperEvalStatusVarAgeForDoneAfterDone v evm tic top ageForPrice price ageForDone,
    clipperEvalStatusTail v evm (clipperStatusDoneLocals tic top ageForPrice price ageForDone)
      (clipperStatusDoneLocals_get_tail tic top ageForPrice price ageForDone), hlt]

theorem clipperEvalStatusDoneTailCond_false (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256)
    (hle : ageForDone.toNat ≤ (clipperStatusTailWord evm).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
      (.binary .gt (.var "ageForDone") (.storage tailRef)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    clipperEvalStatusVarAgeForDoneAfterDone v evm tic top ageForPrice price ageForDone,
    clipperEvalStatusTail v evm (clipperStatusDoneLocals tic top ageForPrice price ageForDone)
      (clipperStatusDoneLocals_get_tail tic top ageForPrice price ageForDone), hle]

theorem clipperStatusLetDoneFalse (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    ExecStmt (config v)
      ({ contract := contract v, locals := clipperStatusAgeForDoneLocals tic top ageForPrice price ageForDone } : Frame) evm
      (.letDecl "done" (some boolTy) (.boolLit false))
      (.ok
        ({ contract := contract v, locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame)
        evm) := by
  simpa [clipperStatusDoneLocals, evalExpr?, pure] using
    (ExecStmt.letDecl
      (cfg := config v)
      (solm :=
        { contract := contract v,
          locals := clipperStatusAgeForDoneLocals tic top ageForPrice price ageForDone })
      (evm := evm) (name := "done") (ty := some boolTy) (expr := .boolLit false)
      (value := .bool false) (by simp [evalExpr?, pure]))

theorem clipperStatusAssignDoneTrue (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    ExecStmt (config v)
      ({ contract := contract v, locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame) evm
      (.assign .localVar (varRef "done") (.boolLit true))
      (.ok
        ({ contract := contract v, locals := clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone } : Frame)
        evm) := by
  have hrhs :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
        (.boolLit true) = .ok (.bool true) := by
    simp [evalExpr?, pure]
  let doneTrueFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone }
  have hassign :
      assignStorageRef? (config v)
        { contract := contract v,
          locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
        .localVar (varRef "done") (.bool true) =
        .ok (doneTrueFrame, evm) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, clipperStatusDoneLocals,
      clipperStatusDoneTrueLocals, doneTrueFrame, pure, bind, EvalResult.bind]
  simpa [doneTrueFrame] using ExecStmt.assign hrhs hassign

theorem clipperEvalStatusVarDoneTrue (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone } evm
      (.var "done") = .ok (.bool true) := by
  simp only [evalExpr?, clipperStatusDoneTrueLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalStatusVarPriceAfterDoneTrue (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone } evm
      (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?, clipperStatusDoneTrueLocals, clipperStatusAgeForDoneLocals,
    clipperStatusDoneLocals, clipperStatusPriceLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusReturnDoneTrue (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    evalExprs? (config v)
      { contract := contract v,
        locals := clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone } evm
      [.var "done", .var "price"] =
      .ok [.bool true, .int (Int.ofNat price.toNat)] := by
  simp only [evalExprs?, clipperEvalStatusVarDoneTrue, clipperEvalStatusVarPriceAfterDoneTrue,
    bind, EvalResult.bind, pure]

theorem clipperStatusDoneTailTrueBranch (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256)
    (hlt : (clipperStatusTailWord evm).toNat < ageForDone.toNat) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame) evm
      [ .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
          [ .assign .localVar (varRef "done") (.boolLit true) ]
          ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
             .assign .localVar (varRef "done")
               (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
        .return [.var "done", .var "price"] ]
      (.returned
        ({ contract := contract v, locals := clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone } : Frame)
        evm (some [.bool true, .int (Int.ofNat price.toNat)])) := by
  let doneFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone }
  let doneTrueFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone }
  have hthen :
      ExecBlock (config v) doneFrame evm
        [ .assign .localVar (varRef "done") (.boolLit true) ]
        (.ok doneTrueFrame evm) := by
    exact ExecBlock.consNormal
      (solm' := doneTrueFrame) (evm' := evm)
      (by simpa [doneFrame, doneTrueFrame] using
        clipperStatusAssignDoneTrue v evm tic top ageForPrice price ageForDone)
      ExecBlock.nil
  have hite :
      ExecStmt (config v) doneFrame evm
        (.ite (.binary .gt (.var "ageForDone") (.storage tailRef))
          [ .assign .localVar (varRef "done") (.boolLit true) ]
          ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
             .assign .localVar (varRef "done")
               (.binary .lt (.var "ratio") (.storage cuspRef)) ]))
        (.ok doneTrueFrame evm) := by
    exact ExecStmt.iteTrue
      (by simpa [doneFrame] using
        clipperEvalStatusDoneTailCond_true v evm tic top ageForPrice price ageForDone hlt)
      hthen
  have hret :
      ExecBlock (config v) doneTrueFrame evm [.return [.var "done", .var "price"]]
        (.returned doneTrueFrame evm (some [.bool true, .int (Int.ofNat price.toNat)])) := by
    exact ExecBlock.consReturn
      (ExecStmt.return
        (by simpa [doneTrueFrame] using
          clipperEvalStatusReturnDoneTrue v evm tic top ageForPrice price ageForDone))
  simpa [doneFrame, doneTrueFrame] using
    ExecBlock.consNormal (solm' := doneTrueFrame) (evm' := evm) hite hret

theorem clipperEvalStatusVarPriceAfterDone (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
      (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?, clipperStatusDoneLocals, clipperStatusAgeForDoneLocals,
    clipperStatusPriceLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusVarTopAfterDone (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
      (.var "top") = .ok (.int (Int.ofNat top.toNat)) := by
  simp only [evalExpr?, clipperStatusDoneLocals, clipperStatusAgeForDoneLocals,
    clipperStatusPriceLocals, clipperStatusAgeForPriceLocals, clipperStatusLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusRdivArgs (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256) :
    evalExprs? (config v)
      { contract := contract v,
        locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone } evm
      [.var "price", .var "top"] =
      .ok [.int (Int.ofNat price.toNat), .int (Int.ofNat top.toNat)] := by
  simp only [evalExprs?, clipperEvalStatusVarPriceAfterDone,
    clipperEvalStatusVarTopAfterDone, bind, EvalResult.bind, pure]

theorem clipperStatusRdivCallReturns (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size) (htop : top ≠ ⟨0⟩) :
    ExecStmt (config v)
      ({ contract := contract v, locals :=
        clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame) evm
      (.internalCall "rdiv" [.var "price", .var "top"] "ratio")
      (.ok
        ({ contract := contract v, locals :=
          clipperStatusRatioLocals tic top ageForPrice price ageForDone
            (UInt256.div (UInt256.mul price clipperRayWord) top) } : Frame)
        evm) := by
  simpa [resumeAfterInternalCall, clipperStatusRatioLocals] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller :=
        { contract := contract v,
          locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone })
      (evm := evm) (calleeEvm := evm)
      (name := "rdiv") (retVar := "ratio")
      (args := [.var "price", .var "top"])
      (argVals := [.int (Int.ofNat price.toNat), .int (Int.ofNat top.toNat)])
      (callee := rdivFunction)
      (locals := clipperUintBinaryLocals price top)
      (calleeSolm :=
        { contract := contract v,
          locals := clipperRdivReturnLocals price top (UInt256.mul price clipperRayWord) })
      (value := some [.int (Int.ofNat
        (UInt256.div (UInt256.mul price clipperRayWord) top).toNat)])
      (clipperEvalStatusRdivArgs v evm tic top ageForPrice price ageForDone)
      (clipperLookupRdivFunction v)
      (clipperBindParamsRdiv price top)
      (clipperRdivFunctionReturns v evm price top hmul htop))

theorem clipperStatusRdivCallRevertsMul (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256)
    (hover : UInt256.size ≤ price.toNat * clipperRayWord.toNat) :
    ExecStmt (config v)
      ({ contract := contract v, locals :=
        clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame) evm
      (.internalCall "rdiv" [.var "price", .var "top"] "ratio") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller :=
        { contract := contract v,
          locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone })
      (evm := evm)
      (name := "rdiv") (retVar := "ratio")
      (args := [.var "price", .var "top"])
      (argVals := [.int (Int.ofNat price.toNat), .int (Int.ofNat top.toNat)])
      (callee := rdivFunction)
      (locals := clipperUintBinaryLocals price top)
      (clipperEvalStatusRdivArgs v evm tic top ageForPrice price ageForDone)
      (clipperLookupRdivFunction v)
      (clipperBindParamsRdiv price top)
      (clipperRdivFunctionRevertsMul v evm price top hover)

theorem clipperStatusRatioLocals_get_cusp
    (tic top ageForPrice price ageForDone ratio : UInt256) :
    (clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio).get? "cusp" =
      none := by
  simp only [clipperStatusRatioLocals, clipperStatusDoneLocals,
    clipperStatusAgeForDoneLocals, clipperStatusPriceLocals,
    clipperStatusAgeForPriceLocals, clipperStatusLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem clipperEvalStatusCusp (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "cusp" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage cuspRef) =
      .ok (.int (Int.ofNat (clipperStatusCuspWord evm).toNat)) := by
  let er : EvaledStorageRef := { base := "cusp", steps := [] }
  have her : evalStorageRef (config v) { contract := contract v, locals := locals } evm
      cuspRef = .ok er := by
    unfold evalStorageRef cuspRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, uint256St]
  have hloc : (config v).storage.layout er = fun _ => some (wordLoc ⟨7⟩) := by
    funext evm'
    rfl
  simpa [clipperStatusCuspWord] using
    evalExpr_storage_scalar_value hbase her hty hloc
      (clipperStorageLocLoad_uint256 evm ⟨7⟩)

theorem clipperEvalStatusVarRatio (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone ratio : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio } evm
      (.var "ratio") = .ok (.int (Int.ofNat ratio.toNat)) := by
  simp only [evalExpr?, clipperStatusRatioLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalStatusRatioCuspCond_true (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone ratio : UInt256)
    (hlt : ratio.toNat < (clipperStatusCuspWord evm).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio } evm
      (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    clipperEvalStatusVarRatio v evm tic top ageForPrice price ageForDone ratio,
    clipperEvalStatusCusp v evm
      (clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio)
      (clipperStatusRatioLocals_get_cusp tic top ageForPrice price ageForDone ratio), hlt]

theorem clipperEvalStatusRatioCuspCond_false (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone ratio : UInt256)
    (hle : (clipperStatusCuspWord evm).toNat ≤ ratio.toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio } evm
      (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    clipperEvalStatusVarRatio v evm tic top ageForPrice price ageForDone ratio,
    clipperEvalStatusCusp v evm
      (clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio)
      (clipperStatusRatioLocals_get_cusp tic top ageForPrice price ageForDone ratio), hle]

theorem clipperStatusAssignDoneFromRatio (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone ratio : UInt256) (done : Bool)
    (hdone :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio } evm
        (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool done)) :
    ExecStmt (config v)
      ({ contract := contract v, locals :=
        clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio } : Frame) evm
      (.assign .localVar (varRef "done")
        (.binary .lt (.var "ratio") (.storage cuspRef)))
      (.ok
        ({ contract := contract v, locals :=
          clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone ratio done } :
          Frame)
        evm) := by
  let doneFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone ratio done }
  have hassign :
      assignStorageRef? (config v)
        { contract := contract v,
          locals := clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio } evm
        .localVar (varRef "done") (.bool done) = .ok (doneFrame, evm) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, clipperStatusDoneFromRatioLocals,
      clipperStatusRatioLocals, doneFrame, pure, bind, EvalResult.bind]
  simpa [doneFrame] using ExecStmt.assign hdone hassign

theorem clipperEvalStatusVarDoneFromRatio (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone ratio : UInt256) (done : Bool) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone ratio done }
      evm (.var "done") = .ok (.bool done) := by
  simp only [evalExpr?, clipperStatusDoneFromRatioLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalStatusVarPriceAfterDoneFromRatio (v : ClipperImmutables)
    (evm : EVM.State) (tic top ageForPrice price ageForDone ratio : UInt256) (done : Bool) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone ratio done }
      evm (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?, clipperStatusDoneFromRatioLocals, clipperStatusRatioLocals,
    clipperStatusDoneLocals, clipperStatusAgeForDoneLocals, clipperStatusPriceLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalStatusReturnDoneFromRatio (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone ratio : UInt256) (done : Bool) :
    evalExprs? (config v)
      { contract := contract v,
        locals := clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone ratio done }
      evm [.var "done", .var "price"] =
      .ok [.bool done, .int (Int.ofNat price.toNat)] := by
  simp only [evalExprs?, clipperEvalStatusVarDoneFromRatio,
    clipperEvalStatusVarPriceAfterDoneFromRatio, bind, EvalResult.bind, pure]

set_option maxHeartbeats 1000000 in
theorem clipperStatusDoneTailFalseBranchReturns (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256)
    (hleTail : ageForDone.toNat ≤ (clipperStatusTailWord evm).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size) (htop : top ≠ ⟨0⟩)
    (done : Bool)
    (hdone :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperStatusRatioLocals tic top ageForPrice price ageForDone
            (UInt256.div (UInt256.mul price clipperRayWord) top) } evm
        (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool done)) :
    ExecBlock (config v)
      ({ contract := contract v, locals :=
        clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame) evm
      [ .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
          [ .assign .localVar (varRef "done") (.boolLit true) ]
          ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
             .assign .localVar (varRef "done")
               (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
        .return [.var "done", .var "price"] ]
      (.returned
        ({ contract := contract v, locals :=
          clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone
            (UInt256.div (UInt256.mul price clipperRayWord) top) done } : Frame)
        evm (some [.bool done, .int (Int.ofNat price.toNat)])) := by
  let ratio : UInt256 := UInt256.div (UInt256.mul price clipperRayWord) top
  let doneFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone }
  let ratioFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusRatioLocals tic top ageForPrice price ageForDone ratio }
  let doneRatioFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone ratio done }
  have hrdiv :
      ExecStmt (config v) doneFrame evm
        (.internalCall "rdiv" [.var "price", .var "top"] "ratio")
        (.ok ratioFrame evm) := by
    simpa [doneFrame, ratioFrame, ratio] using
      clipperStatusRdivCallReturns v evm tic top ageForPrice price ageForDone hmul htop
  have hassign :
      ExecStmt (config v) ratioFrame evm
        (.assign .localVar (varRef "done")
          (.binary .lt (.var "ratio") (.storage cuspRef)))
        (.ok doneRatioFrame evm) := by
    exact clipperStatusAssignDoneFromRatio v evm tic top ageForPrice price ageForDone ratio done
      (by simpa [ratioFrame, ratio] using hdone)
  have helse :
      ExecBlock (config v) doneFrame evm
        [ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
          .assign .localVar (varRef "done")
            (.binary .lt (.var "ratio") (.storage cuspRef)) ]
        (.ok doneRatioFrame evm) := by
    exact ExecBlock.consNormal (solm' := ratioFrame) (evm' := evm) hrdiv
      (ExecBlock.consNormal (solm' := doneRatioFrame) (evm' := evm) hassign ExecBlock.nil)
  have hite :
      ExecStmt (config v) doneFrame evm
        (.ite (.binary .gt (.var "ageForDone") (.storage tailRef))
          [ .assign .localVar (varRef "done") (.boolLit true) ]
          ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
             .assign .localVar (varRef "done")
               (.binary .lt (.var "ratio") (.storage cuspRef)) ]))
        (.ok doneRatioFrame evm) := by
    exact ExecStmt.iteFalse
      (by simpa [doneFrame] using
        clipperEvalStatusDoneTailCond_false v evm tic top ageForPrice price ageForDone hleTail)
      helse
  have hret :
      ExecBlock (config v) doneRatioFrame evm [.return [.var "done", .var "price"]]
        (.returned doneRatioFrame evm (some [.bool done, .int (Int.ofNat price.toNat)])) := by
    exact ExecBlock.consReturn
      (ExecStmt.return
        (by
          cases done
          · simpa [doneRatioFrame, ratio] using
              (clipperEvalStatusReturnDoneFromRatio v evm tic top ageForPrice price ageForDone
                ratio false)
          · simpa [doneRatioFrame, ratio] using
              (clipperEvalStatusReturnDoneFromRatio v evm tic top ageForPrice price ageForDone
                ratio true)))
  simpa [doneFrame, ratioFrame, doneRatioFrame, ratio] using
    ExecBlock.consNormal (solm' := doneRatioFrame) (evm' := evm) hite hret

set_option maxHeartbeats 1000000 in
theorem clipperStatusFunctionReturnsDoneTailTrue (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top price : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : tic.toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (clipperStatusTailWord evmPrice).toNat <
        (UInt256.sub (clipperTimestampWord evmPrice) tic).toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body
      (.returned
        ({ contract := contract v, locals :=
          clipperStatusDoneTrueLocals tic top (UInt256.sub (clipperTimestampWord evm) tic)
            price (UInt256.sub (clipperTimestampWord evmPrice) tic) } : Frame)
        evmPrice (some [.bool true, .int (Int.ofNat price.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [statusFunction, checkedExternalCallStmts, List.cons_append, List.nil_append]
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let ageForDone : UInt256 := UInt256.sub (clipperTimestampWord evmPrice) tic
  let startFrame : Frame := { contract := contract v, locals := clipperStatusLocals tic top }
  let ageFrame : Frame :=
    { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top ageForPrice }
  let priceFrame : Frame :=
    { contract := contract v, locals := clipperStatusPriceLocals tic top ageForPrice price }
  let ageDoneFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusAgeForDoneLocals tic top ageForPrice price ageForDone }
  let doneFrame : Frame :=
    { contract := contract v, locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone }
  have hsubPrice :
      ExecStmt (config v) startFrame evm
        (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice")
        (.ok ageFrame evm) := by
    simpa [startFrame, ageFrame, ageForPrice] using
      clipperStatusAgeForPriceCallReturns v evm tic top hlePrice
  have hguard :
      evalExpr? (config v) ageFrame evm
        (.binary .gt (.extCodeSize (.storage calcRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [ageFrame] using
      clipperEvalStatusCalcCodeGuard_true v evm (clipperStatusAgeForPriceLocals tic top ageForPrice)
        (clipperStatusAgeForPriceLocals_get_calc tic top ageForPrice) hcode
  have hreceiver :
      evalExpr? (config v) ageFrame evm (.storage calcRef) =
        .ok (.address (clipperStatusCalcAddress evm)) := by
    simpa [ageFrame] using
      clipperEvalStatusCalcTarget v evm (clipperStatusAgeForPriceLocals tic top ageForPrice)
        (clipperStatusAgeForPriceLocals_get_calc tic top ageForPrice)
  have heth :
      evalExpr? (config v) ageFrame evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hargs :
      evalExprs? (config v) ageFrame evm [.var "top", .var "ageForPrice"] =
        .ok [.int (Int.ofNat top.toNat), .int (Int.ofNat ageForPrice.toNat)] := by
    simpa [ageFrame, ageForPrice] using
      clipperEvalStatusPriceArgs v evm tic top ageForPrice
  have hcallStmt :
      ExecStmt (config v) ageFrame evm
        (.externalCall (.storage calcRef) "price" (.intLit 0)
          [.var "top", .var "ageForPrice"] "price" (perm := false))
        (.ok priceFrame evmPrice) := by
    simpa [priceFrame] using
      (ExecStmt.externalCallSuccess
        (cfg := config v) (solm := ageFrame) (evm := evm) (evm' := evmPrice)
        (receiver := .storage calcRef) (name := "price") (eth := .intLit 0)
        (args := [.var "top", .var "ageForPrice"]) (retVar := "price")
        (perm := false) (target := clipperStatusCalcAddress evm) (sendVal := 0)
        (argVals := [.int (Int.ofNat top.toNat), .int (Int.ofNat ageForPrice.toNat)])
        (out := out) (value := [.int (Int.ofNat price.toNat)])
        hreceiver heth hargs
        (by simpa [ageForPrice] using hcall)
        hdec)
  have hsubDone :
      ExecStmt (config v) priceFrame evmPrice
        (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone")
        (.ok ageDoneFrame evmPrice) := by
    simpa [priceFrame, ageDoneFrame, ageForDone] using
      clipperStatusAgeForDoneCallReturns v evmPrice tic top ageForPrice price hleDone
  have hletDone :
      ExecStmt (config v) ageDoneFrame evmPrice (.letDecl "done" (some boolTy) (.boolLit false))
        (.ok doneFrame evmPrice) := by
    simpa [ageDoneFrame, doneFrame] using
      clipperStatusLetDoneFalse v evmPrice tic top ageForPrice price ageForDone
  have hbranch :
      ExecBlock (config v) doneFrame evmPrice
        [ .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
            [ .assign .localVar (varRef "done") (.boolLit true) ]
            ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
               .assign .localVar (varRef "done")
                 (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
          .return [.var "done", .var "price"] ]
        (.returned
          ({ contract := contract v, locals :=
            clipperStatusDoneTrueLocals tic top ageForPrice price ageForDone } : Frame)
          evmPrice (some [.bool true, .int (Int.ofNat price.toNat)])) := by
    simpa [doneFrame, ageForDone] using
      clipperStatusDoneTailTrueBranch v evmPrice tic top ageForPrice price ageForDone htail
  exact
    ExecBlock.consNormal (solm' := ageFrame) (evm' := evm) hsubPrice <|
      ExecBlock.consNormal (solm' := ageFrame) (evm' := evm) (ExecStmt.requireTrue hguard) <|
        ExecBlock.consNormal (solm' := priceFrame) (evm' := evmPrice) hcallStmt <|
            ExecBlock.consNormal (solm' := ageDoneFrame) (evm' := evmPrice) hsubDone <|
            ExecBlock.consNormal (solm' := doneFrame) (evm' := evmPrice) hletDone hbranch

set_option maxHeartbeats 1000000 in
theorem clipperStatusFunctionReturnsRdivBranch (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top price : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : tic.toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) tic).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size) (htop : top ≠ ⟨0⟩)
    (done : Bool)
    (hdone :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperStatusRatioLocals tic top
            (UInt256.sub (clipperTimestampWord evm) tic) price
            (UInt256.sub (clipperTimestampWord evmPrice) tic)
            (UInt256.div (UInt256.mul price clipperRayWord) top) } evmPrice
        (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool done)) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body
      (.returned
        ({ contract := contract v, locals :=
          clipperStatusDoneFromRatioLocals tic top
            (UInt256.sub (clipperTimestampWord evm) tic) price
            (UInt256.sub (clipperTimestampWord evmPrice) tic)
            (UInt256.div (UInt256.mul price clipperRayWord) top) done } : Frame)
        evmPrice (some [.bool done, .int (Int.ofNat price.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [statusFunction, checkedExternalCallStmts, List.cons_append, List.nil_append]
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let ageForDone : UInt256 := UInt256.sub (clipperTimestampWord evmPrice) tic
  let ratio : UInt256 := UInt256.div (UInt256.mul price clipperRayWord) top
  let startFrame : Frame := { contract := contract v, locals := clipperStatusLocals tic top }
  let ageFrame : Frame :=
    { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top ageForPrice }
  let priceFrame : Frame :=
    { contract := contract v, locals := clipperStatusPriceLocals tic top ageForPrice price }
  let ageDoneFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusAgeForDoneLocals tic top ageForPrice price ageForDone }
  let doneFrame : Frame :=
    { contract := contract v, locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone }
  have hsubPrice :
      ExecStmt (config v) startFrame evm
        (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice")
        (.ok ageFrame evm) := by
    simpa [startFrame, ageFrame, ageForPrice] using
      clipperStatusAgeForPriceCallReturns v evm tic top hlePrice
  have hguard :
      evalExpr? (config v) ageFrame evm
        (.binary .gt (.extCodeSize (.storage calcRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [ageFrame] using
      clipperEvalStatusCalcCodeGuard_true v evm (clipperStatusAgeForPriceLocals tic top ageForPrice)
        (clipperStatusAgeForPriceLocals_get_calc tic top ageForPrice) hcode
  have hreceiver :
      evalExpr? (config v) ageFrame evm (.storage calcRef) =
        .ok (.address (clipperStatusCalcAddress evm)) := by
    simpa [ageFrame] using
      clipperEvalStatusCalcTarget v evm (clipperStatusAgeForPriceLocals tic top ageForPrice)
        (clipperStatusAgeForPriceLocals_get_calc tic top ageForPrice)
  have heth :
      evalExpr? (config v) ageFrame evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hargs :
      evalExprs? (config v) ageFrame evm [.var "top", .var "ageForPrice"] =
        .ok [.int (Int.ofNat top.toNat), .int (Int.ofNat ageForPrice.toNat)] := by
    simpa [ageFrame, ageForPrice] using
      clipperEvalStatusPriceArgs v evm tic top ageForPrice
  have hcallStmt :
      ExecStmt (config v) ageFrame evm
        (.externalCall (.storage calcRef) "price" (.intLit 0)
          [.var "top", .var "ageForPrice"] "price" (perm := false))
        (.ok priceFrame evmPrice) := by
    simpa [priceFrame] using
      (ExecStmt.externalCallSuccess
        (cfg := config v) (solm := ageFrame) (evm := evm) (evm' := evmPrice)
        (receiver := .storage calcRef) (name := "price") (eth := .intLit 0)
        (args := [.var "top", .var "ageForPrice"]) (retVar := "price")
        (perm := false) (target := clipperStatusCalcAddress evm) (sendVal := 0)
        (argVals := [.int (Int.ofNat top.toNat), .int (Int.ofNat ageForPrice.toNat)])
        (out := out) (value := [.int (Int.ofNat price.toNat)])
        hreceiver heth hargs
        (by simpa [ageForPrice] using hcall)
        hdec)
  have hsubDone :
      ExecStmt (config v) priceFrame evmPrice
        (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone")
        (.ok ageDoneFrame evmPrice) := by
    simpa [priceFrame, ageDoneFrame, ageForDone] using
      clipperStatusAgeForDoneCallReturns v evmPrice tic top ageForPrice price hleDone
  have hletDone :
      ExecStmt (config v) ageDoneFrame evmPrice (.letDecl "done" (some boolTy) (.boolLit false))
        (.ok doneFrame evmPrice) := by
    simpa [ageDoneFrame, doneFrame] using
      clipperStatusLetDoneFalse v evmPrice tic top ageForPrice price ageForDone
  have hbranch :
      ExecBlock (config v) doneFrame evmPrice
        [ .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
            [ .assign .localVar (varRef "done") (.boolLit true) ]
            ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
               .assign .localVar (varRef "done")
                 (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
          .return [.var "done", .var "price"] ]
        (.returned
          ({ contract := contract v, locals :=
            clipperStatusDoneFromRatioLocals tic top ageForPrice price ageForDone ratio done } :
            Frame)
          evmPrice (some [.bool done, .int (Int.ofNat price.toNat)])) := by
    simpa [doneFrame, ageForDone, ageForPrice, ratio] using
      clipperStatusDoneTailFalseBranchReturns v evmPrice tic top ageForPrice price ageForDone
        htail hmul htop done (by simpa [ageForDone, ageForPrice, ratio] using hdone)
  exact
    ExecBlock.consNormal (solm' := ageFrame) (evm' := evm) hsubPrice <|
      ExecBlock.consNormal (solm' := ageFrame) (evm' := evm) (ExecStmt.requireTrue hguard) <|
        ExecBlock.consNormal (solm' := priceFrame) (evm' := evmPrice) hcallStmt <|
          ExecBlock.consNormal (solm' := ageDoneFrame) (evm' := evmPrice) hsubDone <|
            ExecBlock.consNormal (solm' := doneFrame) (evm' := evmPrice) hletDone hbranch

theorem clipperEvalGetStatusVarIdAfterTic (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.var "id") = .ok (clipperGetStatusArgValue I) := by
  simp [evalExpr?, EvalResult.ofOption]
  have hget :
      (clipperGetStatusLocalsTic evm I)["id"]? = some (clipperGetStatusArgValue I) := by
    simpa [Std.HashMap.get?_eq_getElem?] using clipperGetStatusLocalsTic_get_id evm I
  rcases Std.HashMap.getElem?_eq_some_iff.mp hget with ⟨_, hvalue⟩
  exact hvalue

theorem clipperLookupStatusFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "status" = some statusFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction, addFunction, subFunction, mulFunction, wmulFunction, rmulFunction,
    rdivFunction, getFeedPriceFunction, statusFunction]

theorem clipperBindParamsStatus (tic top : UInt256) :
    bindParams? statusFunction.params
      [.int (Int.ofNat tic.toNat), .int (Int.ofNat top.toNat)] =
      some (clipperStatusLocals tic top) := by
  simp [statusFunction, bindParams?, clipperStatusLocals]

theorem clipperEvalGetStatusSalesUsr (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusStore I } evm
      (.storage (salesF (.var "id") "usr")) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperGetStatusSalesPackedSlot I)) solcAddrMask).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "usr") (er := clipperGetStatusSalesUsrRef I)
    (t := .address) (loc := addrLoc (clipperGetStatusSalesPackedSlot I))
    (value := .address (AccountAddress.ofNat (UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperGetStatusSalesPackedSlot I)) solcAddrMask).toNat))
    (by simp [frame, salesF, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesUsrRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, clipperGetStatusStore, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, addrSt])
    (by rfl)
    (by simpa [clipperGetStatusSalesPackedSlot, clipperGetStatusSalesBaseSlot] using
      clipperStorageLocLoad_address evm (clipperGetStatusSalesPackedSlot I))

theorem clipperEvalGetStatusSalesTic (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusStore I } evm
      (.storage (salesF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (clipperSalesPackedTicWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperGetStatusSalesPackedSlot I))).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "tic") (er := clipperGetStatusSalesTicRef I)
    (t := .int uint96Int)
    (loc := uint96Loc (clipperGetStatusSalesPackedSlot I) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (clipperSalesPackedTicWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperGetStatusSalesPackedSlot I))).toNat))
    (by simp [frame, salesF, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesTicRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, clipperGetStatusStore, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint96St])
    (by rfl)
    (by simpa [clipperSalesPackedTicWord, clipperGetStatusSalesPackedSlot,
      clipperGetStatusSalesBaseSlot] using
      clipperStorageLocLoad_uint96 evm (clipperGetStatusSalesPackedSlot I))

theorem clipperEvalGetStatusSalesTop (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusStore I } evm
      (.storage (salesF (.var "id") "top")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperGetStatusSalesTopSlot I)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "top") (er := clipperGetStatusSalesTopRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperGetStatusSalesTopSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperGetStatusSalesTopSlot I)).toNat))
    (by simp [frame, salesF, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesTopRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, clipperGetStatusStore, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperGetStatusSalesTopSlot, clipperGetStatusSalesBaseSlot, wordLoc,
      uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperGetStatusSalesTopSlot I))

theorem clipperEvalGetStatusSalesLot (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusStore I } evm
      (.storage (salesF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperGetStatusSalesLotSlot I)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "lot") (er := clipperGetStatusSalesLotRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperGetStatusSalesLotSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperGetStatusSalesLotSlot I)).toNat))
    (by simp [frame, salesF, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesLotRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, clipperGetStatusStore, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperGetStatusSalesLotSlot, clipperGetStatusSalesBaseSlot, wordLoc,
      uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperGetStatusSalesLotSlot I))

theorem clipperEvalGetStatusSalesTab (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusStore I } evm
      (.storage (salesF (.var "id") "tab")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperGetStatusSalesTabSlot I)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "tab") (er := clipperGetStatusSalesTabRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperGetStatusSalesTabSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperGetStatusSalesTabSlot I)).toNat))
    (by simp [frame, salesF, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesTabRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, clipperGetStatusStore, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperGetStatusSalesTabSlot, clipperGetStatusSalesBaseSlot, wordLoc,
      uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperGetStatusSalesTabSlot I))

theorem clipperEvalGetStatusVarTicAfterTic (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.var "tic") = .ok (.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat)) := by
  simp only [evalExpr?, clipperGetStatusLocalsTic]
  rw [store_get_self]
  rfl

theorem clipperEvalGetStatusSalesTopAfterTic (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.storage (salesF (.var "id") "top")) =
      .ok (.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperGetStatusLocalsTic evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "top") (er := clipperGetStatusSalesTopRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperGetStatusSalesTopSlot I))
    (value := .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat))
    (by simp [frame, salesF, clipperGetStatusLocalsTic, clipperGetStatusLocalsUsr,
      clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesTopRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, clipperEvalGetStatusVarIdAfterTic v evm I, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperGetStatusTopWord, clipperGetStatusSalesTopSlot,
      clipperGetStatusSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperGetStatusSalesTopSlot I))

theorem clipperEvalGetStatusStatusArgs (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      [.var "tic", .storage (salesF (.var "id") "top")] =
      .ok [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
        .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)] := by
  simp only [evalExprs?, clipperEvalGetStatusVarTicAfterTic,
    clipperEvalGetStatusSalesTopAfterTic, bind, EvalResult.bind, pure]

theorem clipperEvalGetStatusDoneFromStatus (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsSt evm I done price }
      evm (tuple0 (.var "st")) = .ok (.bool done) := by
  simp only [tuple0, evalExpr?]
  rw [clipperGetStatusLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 0) = EvalResult.ok (Value.bool done)
  rfl

theorem clipperEvalGetStatusPriceFromStatus (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsDone evm I done price }
      evm (tuple1 (.var "st")) = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [tuple1, evalExpr?]
  rw [clipperGetStatusLocalsDone, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 1) = EvalResult.ok (Value.int ↑price.toNat)
  rfl

theorem clipperEvalGetStatusVarUsrAfterPrice (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsPrice evm I done price }
      evm (.var "usr") =
      .ok (.address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperGetStatusLocalsPrice, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsDone, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsSt, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsTic, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsUsr, store_get_self]
  rfl

theorem clipperEvalGetStatusVarDoneAfterPrice (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsPrice evm I done price }
      evm (.var "done") = .ok (.bool done) := by
  simp only [evalExpr?]
  rw [clipperGetStatusLocalsPrice, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsDone, store_get_self]
  rfl

theorem clipperEvalGetStatusZeroAddr (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    pure, bind]

theorem clipperEvalGetStatusNeedsRedo (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsPrice evm I done price }
      evm (.binary .and (.binary .ne (.var "usr") zeroAddr) (.var "done")) =
      .ok (.bool (clipperGetStatusNeedsRedo evm I done)) := by
  simp only [evalExpr?, clipperEvalGetStatusVarUsrAfterPrice,
    clipperEvalGetStatusZeroAddr, clipperEvalGetStatusVarDoneAfterPrice, EvalResult.bind,
    bind, evalBinaryOp?, clipperGetStatusNeedsRedo]
  generalize hb :
      (!(Value.address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat) ==
        Value.address (AccountAddress.ofNat 0))) = b
  cases b <;> simp [pure]

theorem clipperGetStatusStatusCallReturnsDoneTailTrue (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (clipperStatusTailWord evmPrice).toNat <
        (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      (.ok { contract := contract v, locals := clipperGetStatusLocalsSt evm I true price }
        evmPrice) := by
  simpa [resumeAfterInternalCall, clipperGetStatusLocalsSt] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
      (evm := evm) (calleeEvm := evmPrice)
      (name := "status") (retVar := "st")
      (args := [.var "tic", .storage (salesF (.var "id") "top")])
      (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
        .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
      (callee := statusFunction)
      (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
        (clipperGetStatusTopWord evm I))
      (calleeSolm :=
        { contract := contract v,
          locals := clipperStatusDoneTrueLocals (clipperGetStatusTicWord evm I)
            (clipperGetStatusTopWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I))
            price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)) })
      (value := some [.bool true, .int (Int.ofNat price.toNat)])
      (clipperEvalGetStatusStatusArgs v evm I)
      (clipperLookupStatusFunction v)
      (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
        (clipperGetStatusTopWord evm I))
      (clipperStatusFunctionReturnsDoneTailTrue v (clipperGetStatusTicWord evm I)
        (clipperGetStatusTopWord evm I) price hlePrice hcode hcall hdec hleDone htail))

theorem clipperGetStatusStatusCallReturnsRdivBranch (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperGetStatusTopWord evm I ≠ ⟨0⟩) (done : Bool)
    (hdone :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperStatusRatioLocals (clipperGetStatusTicWord evm I)
            (clipperGetStatusTopWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)) price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I))
            (UInt256.div (UInt256.mul price clipperRayWord) (clipperGetStatusTopWord evm I)) }
        evmPrice (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool done)) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      (.ok { contract := contract v, locals := clipperGetStatusLocalsSt evm I done price }
        evmPrice) := by
  simpa [resumeAfterInternalCall, clipperGetStatusLocalsSt] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
      (evm := evm) (calleeEvm := evmPrice)
      (name := "status") (retVar := "st")
      (args := [.var "tic", .storage (salesF (.var "id") "top")])
      (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
        .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
      (callee := statusFunction)
      (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
        (clipperGetStatusTopWord evm I))
      (calleeSolm :=
        { contract := contract v,
          locals := clipperStatusDoneFromRatioLocals (clipperGetStatusTicWord evm I)
            (clipperGetStatusTopWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I))
            price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I))
            (UInt256.div (UInt256.mul price clipperRayWord) (clipperGetStatusTopWord evm I))
            done })
      (value := some [.bool done, .int (Int.ofNat price.toNat)])
      (clipperEvalGetStatusStatusArgs v evm I)
      (clipperLookupStatusFunction v)
      (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
        (clipperGetStatusTopWord evm I))
      (clipperStatusFunctionReturnsRdivBranch v (clipperGetStatusTicWord evm I)
        (clipperGetStatusTopWord evm I) price hlePrice hcode hcall hdec hleDone htail
        hmul htop done hdone))

theorem clipperEvalGetStatusVarIdAfterUsr (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsUsr evmLoc I }
      evmRead (.var "id") = .ok (clipperGetStatusArgValue I) := by
  simp only [evalExpr?]
  rw [clipperGetStatusLocalsUsr, store_get_ne _ _ (by decide),
    clipperGetStatusStore, store_get_self]
  rfl

theorem clipperEvalGetStatusSalesTicAfterUsr (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsUsr evm I } evm
      (.storage (salesF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperGetStatusLocalsUsr evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "tic") (er := clipperGetStatusSalesTicRef I)
    (t := .int uint96Int)
    (loc := uint96Loc (clipperGetStatusSalesPackedSlot I) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (clipperGetStatusTicWord evm I).toNat))
    (by simp [frame, salesF, clipperGetStatusLocalsUsr, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesTicRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, clipperEvalGetStatusVarIdAfterUsr v evm evm I,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint96St])
    (by rfl)
    (by simpa [clipperGetStatusTicWord, clipperSalesPackedTicWord,
      clipperGetStatusSalesPackedSlot, clipperGetStatusSalesBaseSlot] using
      clipperStorageLocLoad_uint96 evm (clipperGetStatusSalesPackedSlot I))

theorem clipperEvalGetStatusDoneFromStatusAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsSt evmLoc I done price }
      evmRead (tuple0 (.var "st")) = .ok (.bool done) := by
  simp only [tuple0, evalExpr?]
  rw [clipperGetStatusLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 0) = EvalResult.ok (Value.bool done)
  rfl

theorem clipperEvalGetStatusPriceFromStatusAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsDone evmLoc I done price }
      evmRead (tuple1 (.var "st")) = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [tuple1, evalExpr?]
  rw [clipperGetStatusLocalsDone, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 1) = EvalResult.ok (Value.int ↑price.toNat)
  rfl

theorem clipperEvalGetStatusVarUsrAfterPriceAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsPrice evmLoc I done price }
      evmRead (.var "usr") =
      .ok (.address (AccountAddress.ofNat (clipperGetStatusUsrWord evmLoc I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperGetStatusLocalsPrice, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsDone, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsSt, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsTic, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsUsr, store_get_self]
  rfl

theorem clipperEvalGetStatusVarDoneAfterPriceAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsPrice evmLoc I done price }
      evmRead (.var "done") = .ok (.bool done) := by
  simp only [evalExpr?]
  rw [clipperGetStatusLocalsPrice, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsDone, store_get_self]
  rfl

theorem clipperEvalGetStatusNeedsRedoAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsPrice evmLoc I done price }
      evmRead (.binary .and (.binary .ne (.var "usr") zeroAddr) (.var "done")) =
      .ok (.bool (clipperGetStatusNeedsRedo evmLoc I done)) := by
  simp only [evalExpr?, clipperEvalGetStatusVarUsrAfterPriceAt,
    clipperEvalGetStatusZeroAddr, clipperEvalGetStatusVarDoneAfterPriceAt,
    EvalResult.bind, bind, evalBinaryOp?, clipperGetStatusNeedsRedo]
  generalize hb :
      (!(Value.address (AccountAddress.ofNat (clipperGetStatusUsrWord evmLoc I).toNat) ==
        Value.address (AccountAddress.ofNat 0))) = b
  cases b <;> simp [pure]

theorem clipperEvalGetStatusVarNeedsRedo (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
      evmRead (.var "needsRedo") =
      .ok (.bool (clipperGetStatusNeedsRedo evmLoc I done)) := by
  simp only [evalExpr?, clipperGetStatusLocalsNeedsRedo]
  rw [store_get_self]
  rfl

theorem clipperEvalGetStatusVarPriceAfterNeedsRedo (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
      evmRead (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?]
  rw [clipperGetStatusLocalsNeedsRedo, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsPrice, store_get_self]
  rfl

theorem clipperEvalGetStatusVarIdAfterNeedsRedo (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
      evmRead (.var "id") = .ok (clipperGetStatusArgValue I) := by
  simp only [evalExpr?]
  rw [clipperGetStatusLocalsNeedsRedo, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsPrice, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsDone, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsSt, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsTic, store_get_ne _ _ (by decide),
    clipperGetStatusLocalsUsr, store_get_ne _ _ (by decide),
    clipperGetStatusStore, store_get_self]
  rfl

theorem clipperEvalGetStatusSalesLotAfterNeedsRedo (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
      evmRead (.storage (salesF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (clipperGetStatusLotWord evmRead I).toNat)) := by
  let frame : Frame :=
    { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evmRead)
    (slot := salesF (.var "id") "lot") (er := clipperGetStatusSalesLotRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperGetStatusSalesLotSlot I))
    (value := .int (Int.ofNat (clipperGetStatusLotWord evmRead I).toNat))
    (by simp [frame, salesF, clipperGetStatusLocalsNeedsRedo,
      clipperGetStatusLocalsPrice, clipperGetStatusLocalsDone,
      clipperGetStatusLocalsSt, clipperGetStatusLocalsTic,
      clipperGetStatusLocalsUsr, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesLotRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep,
        clipperEvalGetStatusVarIdAfterNeedsRedo v evmLoc evmRead I done price,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperGetStatusLotWord, clipperGetStatusSalesLotSlot,
      clipperGetStatusSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evmRead (clipperGetStatusSalesLotSlot I))

theorem clipperEvalGetStatusSalesTabAfterNeedsRedo (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
      evmRead (.storage (salesF (.var "id") "tab")) =
      .ok (.int (Int.ofNat (clipperGetStatusTabWord evmRead I).toNat)) := by
  let frame : Frame :=
    { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evmRead)
    (slot := salesF (.var "id") "tab") (er := clipperGetStatusSalesTabRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperGetStatusSalesTabSlot I))
    (value := .int (Int.ofNat (clipperGetStatusTabWord evmRead I).toNat))
    (by simp [frame, salesF, clipperGetStatusLocalsNeedsRedo,
      clipperGetStatusLocalsPrice, clipperGetStatusLocalsDone,
      clipperGetStatusLocalsSt, clipperGetStatusLocalsTic,
      clipperGetStatusLocalsUsr, clipperGetStatusStore])
    (by
      simp [frame, clipperGetStatusSalesTabRef, clipperGetStatusArgValue,
        clipperGetStatusArgKey, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep,
        clipperEvalGetStatusVarIdAfterNeedsRedo v evmLoc evmRead I done price,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperGetStatusArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperGetStatusTabWord, clipperGetStatusSalesTabSlot,
      clipperGetStatusSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evmRead (clipperGetStatusSalesTabSlot I))

theorem clipperEvalGetStatusReturnValues (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evmLoc I done price }
      evmRead
      [ .var "needsRedo", .var "price",
        .storage (salesF (.var "id") "lot"), .storage (salesF (.var "id") "tab") ] =
      .ok [ .bool (clipperGetStatusNeedsRedo evmLoc I done),
        .int (Int.ofNat price.toNat),
        .int (Int.ofNat (clipperGetStatusLotWord evmRead I).toNat),
        .int (Int.ofNat (clipperGetStatusTabWord evmRead I).toNat)] := by
  simp only [evalExprs?, clipperEvalGetStatusVarNeedsRedo,
    clipperEvalGetStatusVarPriceAfterNeedsRedo, clipperEvalGetStatusSalesLotAfterNeedsRedo,
    clipperEvalGetStatusSalesTabAfterNeedsRedo, bind, EvalResult.bind, pure]

theorem clipperGetStatusBodyReturnsDoneTailTrue (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (clipperStatusTailWord evmPrice).toNat <
        (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body
      (.returned
        { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evm I true price }
        evmPrice
        (some [ .bool (clipperGetStatusNeedsRedo evm I true),
          .int (Int.ofNat price.toNat),
          .int (Int.ofNat (clipperGetStatusLotWord evmPrice I).toNat),
          .int (Int.ofNat (clipperGetStatusTabWord evmPrice I).toNat)])) := by
  let startFrame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  let usrFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsUsr evm I }
  let ticFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsTic evm I }
  let stFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsSt evm I true price }
  let doneFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsDone evm I true price }
  let priceFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsPrice evm I true price }
  let needsFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsNeedsRedo evm I true price }
  have hletUsr :
      ExecStmt (config v) startFrame evm
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evm) := by
    simpa [startFrame, usrFrame, clipperGetStatusLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evm) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat))
        (by simpa [startFrame, clipperGetStatusUsrWord] using
          clipperEvalGetStatusSalesUsr v evm I))
  have hletTic :
      ExecStmt (config v) usrFrame evm
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evm) := by
    simpa [usrFrame, ticFrame, clipperGetStatusLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evm) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperGetStatusTicWord evm I).toNat))
        (by simpa [usrFrame] using clipperEvalGetStatusSalesTicAfterUsr v evm I))
  have hstatus :
      ExecStmt (config v) ticFrame evm
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame] using
      clipperGetStatusStatusCallReturnsDoneTailTrue v I price hlePrice hcode hcall hdec
        hleDone htail
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperGetStatusLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool true)
        (by simpa [stFrame] using
          clipperEvalGetStatusDoneFromStatusAt v evm evmPrice I true price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperGetStatusLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalGetStatusPriceFromStatusAt v evm evmPrice I true price))
  have hletNeeds :
      ExecStmt (config v) priceFrame evmPrice
        (.letDecl "needsRedo" (some boolTy)
          (.binary .and (.binary .ne (.var "usr") zeroAddr) (.var "done")))
        (.ok needsFrame evmPrice) := by
    simpa [priceFrame, needsFrame, clipperGetStatusLocalsNeedsRedo] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := priceFrame) (evm := evmPrice) (name := "needsRedo")
        (ty := some boolTy)
        (expr := .binary .and (.binary .ne (.var "usr") zeroAddr) (.var "done"))
        (value := .bool (clipperGetStatusNeedsRedo evm I true))
        (by simpa [priceFrame] using
          clipperEvalGetStatusNeedsRedoAt v evm evmPrice I true price))
  have hret :
      ExecBlock (config v) needsFrame evmPrice
        [ .return [ .var "needsRedo", .var "price",
            .storage (salesF (.var "id") "lot"),
            .storage (salesF (.var "id") "tab") ] ]
        (.returned needsFrame evmPrice
          (some [ .bool (clipperGetStatusNeedsRedo evm I true),
            .int (Int.ofNat price.toNat),
            .int (Int.ofNat (clipperGetStatusLotWord evmPrice I).toNat),
            .int (Int.ofNat (clipperGetStatusTabWord evmPrice I).toNat)])) := by
    exact ExecBlock.consReturn
      (ExecStmt.return
        (by simpa [needsFrame] using
          clipperEvalGetStatusReturnValues v evm evmPrice I true price))
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
