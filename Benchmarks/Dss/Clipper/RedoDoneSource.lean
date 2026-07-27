import Benchmarks.Dss.Clipper.Redo
import Benchmarks.Dss.Clipper.GetFeedPrice
import Benchmarks.Dss.Clipper.StatusPriceCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

abbrev clipperRedoLocalsSt (evm : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) : Store :=
  (clipperRedoLocalsTop evm I).insert "st"
    (.tuple [.bool done, .int (Int.ofNat price.toNat)])

theorem clipperRedoStatusCallReturnsDoneTailTrue (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (clipperStatusTailWord evmPrice).toNat <
        (UInt256.sub (clipperTimestampWord evmPrice) (clipperRedoSalesTicEVMWord evm I)).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      (.ok { contract := contract v, locals := clipperRedoLocalsSt evm I true price }
        evmPrice) := by
  simpa [resumeAfterInternalCall, clipperRedoLocalsSt] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
      (evm := evm) (calleeEvm := evmPrice)
      (name := "status") (retVar := "st")
      (args := [.var "tic", .var "top"])
      (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
        .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
      (callee := statusFunction)
      (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
        (clipperRedoSalesTopEVMWord evm I))
      (calleeSolm :=
        { contract := contract v,
          locals := clipperStatusDoneTrueLocals (clipperRedoSalesTicEVMWord evm I)
            (clipperRedoSalesTopEVMWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I))
            price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperRedoSalesTicEVMWord evm I)) })
      (value := some [.bool true, .int (Int.ofNat price.toNat)])
      (clipperEvalRedoStatusArgs v evm I)
      (clipperLookupStatusFunction v)
      (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
        (clipperRedoSalesTopEVMWord evm I))
      (clipperStatusFunctionReturnsDoneTailTrue v (clipperRedoSalesTicEVMWord evm I)
        (clipperRedoSalesTopEVMWord evm I) price hlePrice hcode hcall hdec hleDone htail))

theorem clipperRedoStatusCallReturnsRdivBranch (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperRedoSalesTicEVMWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperRedoSalesTopEVMWord evm I ≠ ⟨0⟩) (done : Bool)
    (hdone :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperStatusRatioLocals (clipperRedoSalesTicEVMWord evm I)
            (clipperRedoSalesTopEVMWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)) price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperRedoSalesTicEVMWord evm I))
            (UInt256.div (UInt256.mul price clipperRayWord) (clipperRedoSalesTopEVMWord evm I)) }
        evmPrice (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool done)) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      (.ok { contract := contract v, locals := clipperRedoLocalsSt evm I done price }
        evmPrice) := by
  simpa [resumeAfterInternalCall, clipperRedoLocalsSt] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
      (evm := evm) (calleeEvm := evmPrice)
      (name := "status") (retVar := "st")
      (args := [.var "tic", .var "top"])
      (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
        .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
      (callee := statusFunction)
      (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
        (clipperRedoSalesTopEVMWord evm I))
      (calleeSolm :=
        { contract := contract v,
          locals := clipperStatusDoneFromRatioLocals (clipperRedoSalesTicEVMWord evm I)
            (clipperRedoSalesTopEVMWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I))
            price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperRedoSalesTicEVMWord evm I))
            (UInt256.div (UInt256.mul price clipperRayWord) (clipperRedoSalesTopEVMWord evm I))
            done })
      (value := some [.bool done, .int (Int.ofNat price.toNat)])
      (clipperEvalRedoStatusArgs v evm I)
      (clipperLookupStatusFunction v)
      (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
        (clipperRedoSalesTopEVMWord evm I))
      (clipperStatusFunctionReturnsRdivBranch v (clipperRedoSalesTicEVMWord evm I)
        (clipperRedoSalesTopEVMWord evm I) price hlePrice hcode hcall hdec hleDone htail
        hmul htop done hdone))

theorem clipperRedoStatusCallRevertsPriceNoCode (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .var "top"])
    (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperEvalRedoStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsPriceNoCode v evm
      (clipperRedoSalesTicEVMWord evm I) (clipperRedoSalesTopEVMWord evm I)
      hlePrice hnoCode)

theorem clipperRedoStatusCallRevertsPriceCallFailure (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)).toNat)]
        (false, evmPrice, out) false) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .var "top"])
    (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperEvalRedoStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsPriceCallFailure v
      (clipperRedoSalesTicEVMWord evm I) (clipperRedoSalesTopEVMWord evm I)
      hlePrice hcode hcall)

theorem clipperRedoStatusCallRevertsPriceDecode (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out = none) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .var "top"])
    (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperEvalRedoStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsPriceDecode v
      (clipperRedoSalesTicEVMWord evm I) (clipperRedoSalesTopEVMWord evm I)
      hlePrice hcode hcall hdec)

theorem clipperEvalRedoDoneFromStatus (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsSt evm I done price }
      evm (tuple0 (.var "st")) = .ok (.bool done) := by
  simp only [tuple0, evalExpr?]
  rw [clipperRedoLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 0) = EvalResult.ok (Value.bool done)
  rfl

theorem clipperEvalRedoDoneFromStatusAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsSt evmLoc I done price }
      evmRead (tuple0 (.var "st")) = .ok (.bool done) := by
  simp only [tuple0, evalExpr?]
  rw [clipperRedoLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 0) = EvalResult.ok (Value.bool done)
  rfl

abbrev clipperRedoSalesTabSlot (I : ExecutionEnv) : UInt256 :=
  clipperRedoSalesBaseSlot I + ⟨1⟩

abbrev clipperRedoSalesLotSlot (I : ExecutionEnv) : UInt256 :=
  clipperRedoSalesBaseSlot I + ⟨2⟩

abbrev clipperRedoSalesTabRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperRedoIdKey I), .field "tab"] }

abbrev clipperRedoSalesLotRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperRedoIdKey I), .field "lot"] }

abbrev clipperRedoSalesTabEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperRedoSalesTabSlot I)

abbrev clipperRedoSalesLotEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperRedoSalesLotSlot I)

abbrev clipperRedoLocalsTab (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price : UInt256) : Store :=
  (clipperRedoLocalsSt evmLoc I true price).insert "tab"
    (.int (Int.ofNat (clipperRedoSalesTabEVMWord evmRead I).toNat))

abbrev clipperRedoLocalsLot (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price : UInt256) : Store :=
  (clipperRedoLocalsTab evmLoc evmRead I price).insert "lot"
    (.int (Int.ofNat (clipperRedoSalesLotEVMWord evmRead I).toNat))

theorem clipperEvalRedoVarIdAfterStatusTrue (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsSt evmLoc I true price }
      evmRead (.var "id") = .ok (clipperRedoIdValue I) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsSt, store_get_ne _ _ (by decide), clipperRedoLocalsTop,
    store_get_ne _ _ (by decide), clipperRedoLocalsTic, store_get_ne _ _ (by decide),
    clipperRedoLocalsUsr, store_get_ne _ _ (by decide), clipperRedoStore,
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoVarIdAfterTab (v : ClipperImmutables)
    (evmLoc evmRead evmRead' : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTab evmLoc evmRead I price }
      evmRead' (.var "id") = .ok (clipperRedoIdValue I) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsTab, store_get_ne _ _ (by decide), clipperRedoLocalsSt,
    store_get_ne _ _ (by decide), clipperRedoLocalsTop, store_get_ne _ _ (by decide),
    clipperRedoLocalsTic, store_get_ne _ _ (by decide), clipperRedoLocalsUsr,
    store_get_ne _ _ (by decide), clipperRedoStore, store_get_ne _ _ (by decide),
    store_get_self]
  rfl

theorem clipperEvalRedoVarIdAfterLot (v : ClipperImmutables)
    (evmLoc evmRead evmRead' : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
      evmRead' (.var "id") = .ok (clipperRedoIdValue I) := by
  simp only [evalExpr?]
  rw [clipperRedoLocalsLot, store_get_ne _ _ (by decide), clipperRedoLocalsTab,
    store_get_ne _ _ (by decide), clipperRedoLocalsSt, store_get_ne _ _ (by decide),
    clipperRedoLocalsTop, store_get_ne _ _ (by decide), clipperRedoLocalsTic,
    store_get_ne _ _ (by decide), clipperRedoLocalsUsr, store_get_ne _ _ (by decide),
    clipperRedoStore, store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoSalesTabAfterStatusTrue (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsSt evmLoc I true price }
      evmRead (.storage (salesF (.var "id") "tab")) =
      .ok (.int (Int.ofNat (clipperRedoSalesTabEVMWord evmRead I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperRedoLocalsSt evmLoc I true price }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evmRead)
    (slot := salesF (.var "id") "tab") (er := clipperRedoSalesTabRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperRedoSalesTabSlot I))
    (value := .int (Int.ofNat (clipperRedoSalesTabEVMWord evmRead I).toNat))
    (by simp [frame, salesF, clipperRedoLocalsSt, clipperRedoLocalsTop,
      clipperRedoLocalsTic, clipperRedoLocalsUsr, clipperRedoStore])
    (by
      simp [frame, clipperRedoSalesTabRef, clipperRedoIdValue, clipperRedoIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalRedoVarIdAfterStatusTrue v evmLoc evmRead I price, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure])
    (by simp [frame, clipperRedoIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperRedoSalesTabEVMWord, clipperRedoSalesTabSlot, wordLoc, uint256Loc]
      using clipperStorageLocLoad_uint256 evmRead (clipperRedoSalesTabSlot I))

theorem clipperEvalRedoSalesLotAfterTab (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRedoLocalsTab evmLoc evmRead I price }
      evmRead (.storage (salesF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (clipperRedoSalesLotEVMWord evmRead I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperRedoLocalsTab evmLoc evmRead I price }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evmRead)
    (slot := salesF (.var "id") "lot") (er := clipperRedoSalesLotRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperRedoSalesLotSlot I))
    (value := .int (Int.ofNat (clipperRedoSalesLotEVMWord evmRead I).toNat))
    (by simp [frame, salesF, clipperRedoLocalsTab, clipperRedoLocalsSt,
      clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr, clipperRedoStore])
    (by
      simp [frame, clipperRedoSalesLotRef, clipperRedoIdValue, clipperRedoIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalRedoVarIdAfterTab v evmLoc evmRead evmRead I price, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure])
    (by simp [frame, clipperRedoIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperRedoSalesLotEVMWord, clipperRedoSalesLotSlot, wordLoc, uint256Loc]
      using clipperStorageLocLoad_uint256 evmRead (clipperRedoSalesLotSlot I))

theorem clipperEvalRedoTimestamp96 (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (wrap96 (.env .timestamp)) =
      .ok (.int (Int.ofNat ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
        (2 ^ 96)))) := by
  simp [wrap96, evalExpr?, evalBinaryOp?, envValue, uint96Modulus, bind, EvalResult.bind, pure]

private theorem clipperNatLandLowMaskMod (n k : Nat) :
    Nat.land n (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ k - 1)).testBit i = (n % 2 ^ k).testBit i
  rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  cases decide (i < k) <;> simp

private theorem clipperUInt256LandSalesUint96Mask_toNat (w : UInt256) :
    (UInt256.land w clipperSalesUint96Mask).toNat = w.toNat % 2 ^ 96 := by
  rw [u256_land_toNat]
  have hmask : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by native_decide
  rw [hmask, clipperNatLandLowMaskMod]
  have hlt : w.toNat % 2 ^ 96 < UInt256.size := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hlt]

private theorem clipperSalesUint96Mask_idempotent (w : UInt256) :
    UInt256.land (UInt256.land w clipperSalesUint96Mask) clipperSalesUint96Mask =
      UInt256.land w clipperSalesUint96Mask := by
  apply u256_inj
  rw [clipperUInt256LandSalesUint96Mask_toNat, clipperUInt256LandSalesUint96Mask_toNat]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]

theorem clipperStorageLocStore_uint96_offset20
    (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint96Loc slot ⟨20, by decide⟩ (by decide))
        (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.mul (UInt256.land val clipperSalesUint96Mask)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask))) := by
  unfold storageLocStore storageLocWriteWord uint96Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (12 : Fin 33).val _
        ++ List.drop ((20 : Fin 32).val + (12 : Fin 33).val) _) =
      (UInt256.lor
        ((val.land clipperSalesUint96Mask).mul ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩))
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).land solcAddrMask)).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (12 : Fin 33).val = 12 from rfl]
  rw [show 20 + 12 = 32 by norm_num, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask, fromBytes'_take_wordLE]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20).length = 20 := by
    rw [List.length_take, hslen]
    norm_num
  rw [hlen20]
  have hlowOld :
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).land solcAddrMask).toNat <
        2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using
      solcAddrMask_result_canonical (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
  have hvalMask : (val.land clipperSalesUint96Mask).toNat = val.toNat % 2 ^ 96 :=
    clipperUInt256LandSalesUint96Mask_toNat val
  have hshift : (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).toNat) = 2 ^ 160 := by
    native_decide
  have hmulLt :
      (val.land clipperSalesUint96Mask).toNat *
          ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).toNat <
        UInt256.size := by
    rw [hvalMask, hshift]
    have hmod : val.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by norm_num)
    have hmodLe : val.toNat % 2 ^ 96 ≤ 2 ^ 96 - 1 := Nat.le_pred_of_lt hmod
    calc
      val.toNat % 2 ^ 96 * 2 ^ 160 ≤ (2 ^ 96 - 1) * 2 ^ 160 :=
        Nat.mul_le_mul_right _ hmodLe
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  rw [u256_lor_toNat]
  rw [show
      ((val.land clipperSalesUint96Mask).mul ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩)).toNat =
        (val.land clipperSalesUint96Mask).toNat *
          ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).toNat by
    exact umul_toNat _ _ hmulLt]
  rw [hshift, hvalMask]
  rw [nat_lor_comm]
  rw [nat_lor_shift_add _ _ 160 hlowOld]
  have hsumLt :
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).land solcAddrMask).toNat +
          val.toNat % 2 ^ 96 * 2 ^ 160 <
        UInt256.size := by
    have hmod : val.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by norm_num)
    have hlowLe :
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).land solcAddrMask).toNat ≤
          2 ^ 160 - 1 := Nat.le_pred_of_lt hlowOld
    have hmodLe : val.toNat % 2 ^ 96 ≤ 2 ^ 96 - 1 := Nat.le_pred_of_lt hmod
    calc
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).land solcAddrMask).toNat +
          val.toNat % 2 ^ 96 * 2 ^ 160 ≤
        (2 ^ 160 - 1) + (2 ^ 96 - 1) * 2 ^ 160 := by
          exact Nat.add_le_add hlowLe (Nat.mul_le_mul_right _ hmodLe)
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  rw [Nat.mod_eq_of_lt hsumLt]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num, show 256 ^ 12 = 2 ^ 96 by norm_num]
  ring

abbrev clipperRedoPostTicPackedWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.land clipperSalesUint96Mask (UInt256.ofNat evm.executionEnv.header.timestamp))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
    (UInt256.land solcAddrMask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperRedoSalesPackedSlot I)))

abbrev clipperRedoPostTicState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperRedoSalesPackedSlot I)
    (clipperRedoPostTicPackedWord evm I)

theorem clipperStorageStore_σ₀
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem clipperStorageStore_createdAccounts
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).createdAccounts = evm.createdAccounts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem clipperStorageStore_genesisBlockHeader
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem clipperStorageStore_blocks
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem clipperStorageStore_executionEnv
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem clipperRedoPostTicAccountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv} (evm : EVM.State)
    (hevmAcct : evm.accountMap = τ)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ τ) :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ (clipperRedoSalesPackedSlot I)
          (UInt256.lor
            (UInt256.mul
              (UInt256.land clipperSalesUint96Mask (UInt256.ofNat I.header.timestamp))
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
            (UInt256.land solcAddrMask (solcSlotWord σ I (clipperRedoSalesPackedSlot I)))))
        (clipperRedoPostTicState evm I).accountMap := by
  subst τ
  subst I
  let slot := clipperRedoSalesPackedSlot evm.executionEnv
  let updated : UInt256 :=
    UInt256.lor
      (UInt256.mul
        (UInt256.land clipperSalesUint96Mask (UInt256.ofNat evm.executionEnv.header.timestamp))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
      (UInt256.land solcAddrMask (solcSlotWord σ evm.executionEnv slot))
  have hslotWord :
      solcSlotWord σ evm.executionEnv slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    simpa [solcSlotWord, State.lookupAccount, Account.lookupStorage] using
      accountMapEquiv_storage_findD hAccounts evm.executionEnv.codeOwner slot (⟨0⟩ : UInt256)
  have hupdated : updated = clipperRedoPostTicPackedWord evm evm.executionEnv := by
    simp [updated, slot, clipperRedoPostTicPackedWord, hslotWord]
  have hPostMap :
      (clipperRedoPostTicState evm evm.executionEnv).accountMap =
        sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap slot
          (clipperRedoPostTicPackedWord evm evm.executionEnv) := by
    simp [clipperRedoPostTicState, storageStore_accountMap, slot]
  rw [hPostMap]
  simpa [slot, updated, hupdated] using
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner slot updated hAccounts

theorem clipperRedoPostTicSpotterAddress_eq_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv} (evm : EVM.State)
    (hevmAcct : evm.accountMap = τ)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ τ) :
      clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evm I) =
        AccountAddress.ofUInt256
          (clipperSpotterTarget
            (sstoreAccountMap I.codeOwner σ (clipperRedoSalesPackedSlot I)
              (UInt256.lor
                (UInt256.mul
                  (UInt256.land clipperSalesUint96Mask (UInt256.ofNat I.header.timestamp))
                  (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
                (UInt256.land solcAddrMask (solcSlotWord σ I (clipperRedoSalesPackedSlot I)))))
            I) := by
  subst τ
  subst I
  let slot := clipperRedoSalesPackedSlot evm.executionEnv
  let updated : UInt256 :=
    UInt256.lor
      (UInt256.mul
        (UInt256.land clipperSalesUint96Mask (UInt256.ofNat evm.executionEnv.header.timestamp))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
      (UInt256.land solcAddrMask (solcSlotWord σ evm.executionEnv slot))
  have hPostMap :
      (clipperRedoPostTicState evm evm.executionEnv).accountMap =
        sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap slot
          (clipperRedoPostTicPackedWord evm evm.executionEnv) := by
    simp [clipperRedoPostTicState, storageStore_accountMap, slot]
  have hPostEnv :
      (clipperRedoPostTicState evm evm.executionEnv).executionEnv = evm.executionEnv := by
    simp [clipperRedoPostTicState, storageStore_executionEnv]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap evm.executionEnv.codeOwner σ slot updated)
        (clipperRedoPostTicState evm evm.executionEnv).accountMap := by
    simpa [slot, updated] using
      clipperRedoPostTicAccountMapEquiv
        (σ := σ) (τ := evm.accountMap) (I := evm.executionEnv) evm rfl rfl hAccounts
  have hslot3 := accountMapEquiv_storage_findD hAccountsPost
    evm.executionEnv.codeOwner (⟨3⟩ : UInt256) (⟨0⟩ : UInt256)
  rw [hPostMap] at hslot3
  simp [clipperGetFeedPriceSpotterAddress, clipperSpotterTarget, solcSlotWord,
    hPostMap, hPostEnv, slot] at hslot3 ⊢
  rw [← hslot3]

theorem clipperRedoPostTicNoCode_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv} (evm : EVM.State)
    (hevmAcct : evm.accountMap = τ)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (sstoreAccountMap I.codeOwner σ (clipperRedoSalesPackedSlot I)
          (UInt256.lor
            (UInt256.mul
              (UInt256.land clipperSalesUint96Mask (UInt256.ofNat I.header.timestamp))
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
            (UInt256.land solcAddrMask (solcSlotWord σ I (clipperRedoSalesPackedSlot I)))))
        (clipperSpotterTarget
          (sstoreAccountMap I.codeOwner σ (clipperRedoSalesPackedSlot I)
            (UInt256.lor
              (UInt256.mul
                (UInt256.land clipperSalesUint96Mask (UInt256.ofNat I.header.timestamp))
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
              (UInt256.land solcAddrMask (solcSlotWord σ I (clipperRedoSalesPackedSlot I)))))
          I) = ⟨0⟩) :
      (UInt256.ofNat
        (((clipperRedoPostTicState evm I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evm I))).option 0
            (fun acc => acc.code.size))).toNat = 0 := by
  subst τ
  subst I
  let slot := clipperRedoSalesPackedSlot evm.executionEnv
  let updated : UInt256 :=
    UInt256.lor
      (UInt256.mul
        (UInt256.land clipperSalesUint96Mask (UInt256.ofNat evm.executionEnv.header.timestamp))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
      (UInt256.land solcAddrMask (solcSlotWord σ evm.executionEnv slot))
  have hslotWord :
      solcSlotWord σ evm.executionEnv slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    simpa [solcSlotWord, State.lookupAccount, Account.lookupStorage] using
      accountMapEquiv_storage_findD hAccounts evm.executionEnv.codeOwner slot (⟨0⟩ : UInt256)
  have hupdated : updated = clipperRedoPostTicPackedWord evm evm.executionEnv := by
    simp [updated, slot, clipperRedoPostTicPackedWord, hslotWord]
  have hPostMap :
      (clipperRedoPostTicState evm evm.executionEnv).accountMap =
        sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap slot
          (clipperRedoPostTicPackedWord evm evm.executionEnv) := by
    simp [clipperRedoPostTicState, storageStore_accountMap, slot]
  have hPostEnv :
      (clipperRedoPostTicState evm evm.executionEnv).executionEnv = evm.executionEnv := by
    simp [clipperRedoPostTicState, storageStore_executionEnv]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap evm.executionEnv.codeOwner σ slot updated)
        (clipperRedoPostTicState evm evm.executionEnv).accountMap := by
    rw [hPostMap]
    simpa [slot, hupdated] using
      accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner slot updated hAccounts
  have htarget :
      clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evm evm.executionEnv) =
        AccountAddress.ofUInt256
          (clipperSpotterTarget
            (sstoreAccountMap evm.executionEnv.codeOwner σ slot updated)
            evm.executionEnv) := by
    have hslot3 := accountMapEquiv_storage_findD hAccountsPost
      evm.executionEnv.codeOwner (⟨3⟩ : UInt256) (⟨0⟩ : UInt256)
    rw [hPostMap] at hslot3
    simp [clipperGetFeedPriceSpotterAddress, clipperSpotterTarget, solcSlotWord,
      hPostMap, hPostEnv, slot] at hslot3 ⊢
    rw [← hslot3]
  simpa [hPostMap, hPostEnv, State.lookupAccount, slot, updated] using
    clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
      (σ := sstoreAccountMap evm.executionEnv.codeOwner σ slot updated)
      (τ := (clipperRedoPostTicState evm evm.executionEnv).accountMap)
      (target := clipperSpotterTarget
        (sstoreAccountMap evm.executionEnv.codeOwner σ slot updated) evm.executionEnv)
      (addr := clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evm evm.executionEnv))
      hAccountsPost htarget (by simpa [slot, updated] using hzero)

theorem clipperRedoPostTicCode_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv} (evm : EVM.State)
    (hevmAcct : evm.accountMap = τ)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ τ)
    (hcode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (sstoreAccountMap I.codeOwner σ (clipperRedoSalesPackedSlot I)
          (UInt256.lor
            (UInt256.mul
              (UInt256.land clipperSalesUint96Mask (UInt256.ofNat I.header.timestamp))
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
            (UInt256.land solcAddrMask (solcSlotWord σ I (clipperRedoSalesPackedSlot I)))))
        (clipperSpotterTarget
          (sstoreAccountMap I.codeOwner σ (clipperRedoSalesPackedSlot I)
            (UInt256.lor
              (UInt256.mul
                (UInt256.land clipperSalesUint96Mask (UInt256.ofNat I.header.timestamp))
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
              (UInt256.land solcAddrMask (solcSlotWord σ I (clipperRedoSalesPackedSlot I)))))
          I) ≠ ⟨0⟩) :
      0 < (UInt256.ofNat
        (((clipperRedoPostTicState evm I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evm I))).option 0
            (fun acc => acc.code.size))).toNat := by
  subst τ
  subst I
  let slot := clipperRedoSalesPackedSlot evm.executionEnv
  let updated : UInt256 :=
    UInt256.lor
      (UInt256.mul
        (UInt256.land clipperSalesUint96Mask (UInt256.ofNat evm.executionEnv.header.timestamp))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
      (UInt256.land solcAddrMask (solcSlotWord σ evm.executionEnv slot))
  have hslotWord :
      solcSlotWord σ evm.executionEnv slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    simpa [solcSlotWord, State.lookupAccount, Account.lookupStorage] using
      accountMapEquiv_storage_findD hAccounts evm.executionEnv.codeOwner slot (⟨0⟩ : UInt256)
  have hupdated : updated = clipperRedoPostTicPackedWord evm evm.executionEnv := by
    simp [updated, slot, clipperRedoPostTicPackedWord, hslotWord]
  have hPostMap :
      (clipperRedoPostTicState evm evm.executionEnv).accountMap =
        sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap slot
          (clipperRedoPostTicPackedWord evm evm.executionEnv) := by
    simp [clipperRedoPostTicState, storageStore_accountMap, slot]
  have hPostEnv :
      (clipperRedoPostTicState evm evm.executionEnv).executionEnv = evm.executionEnv := by
    simp [clipperRedoPostTicState, storageStore_executionEnv]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap evm.executionEnv.codeOwner σ slot updated)
        (clipperRedoPostTicState evm evm.executionEnv).accountMap := by
    rw [hPostMap]
    simpa [slot, hupdated] using
      accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner slot updated hAccounts
  have htarget :
      clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evm evm.executionEnv) =
        AccountAddress.ofUInt256
          (clipperSpotterTarget
            (sstoreAccountMap evm.executionEnv.codeOwner σ slot updated)
            evm.executionEnv) := by
    have hslot3 := accountMapEquiv_storage_findD hAccountsPost
      evm.executionEnv.codeOwner (⟨3⟩ : UInt256) (⟨0⟩ : UInt256)
    rw [hPostMap] at hslot3
    simp [clipperGetFeedPriceSpotterAddress, clipperSpotterTarget, solcSlotWord,
      hPostMap, hPostEnv, slot] at hslot3 ⊢
    rw [← hslot3]
  simpa [hPostMap, hPostEnv, State.lookupAccount, slot, updated] using
    clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
      (σ := sstoreAccountMap evm.executionEnv.codeOwner σ slot updated)
      (τ := (clipperRedoPostTicState evm evm.executionEnv).accountMap)
      (target := clipperSpotterTarget
        (sstoreAccountMap evm.executionEnv.codeOwner σ slot updated) evm.executionEnv)
      (addr := clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evm evm.executionEnv))
      hAccountsPost htarget (by simpa [slot, updated] using hcode)

theorem clipperRedoAssignSalesTicTimestampExact (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
      evmRead
      (.assign .storage (salesF (.var "id") "tic") (wrap96 (.env .timestamp)))
      (.ok { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
        (Solm.EVM.storageStore evmRead evmRead.executionEnv.codeOwner
          (clipperRedoSalesPackedSlot I)
          (UInt256.lor
            (UInt256.mul
              (UInt256.land clipperSalesUint96Mask
                (UInt256.ofNat evmRead.executionEnv.header.timestamp))
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
            (UInt256.land solcAddrMask
              (Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner
                (clipperRedoSalesPackedSlot I)))))) := by
  let ticWord : UInt256 :=
    UInt256.land (UInt256.ofNat evmRead.executionEnv.header.timestamp) clipperSalesUint96Mask
  let loc : StorageLoc := uint96Loc (clipperRedoSalesPackedSlot I) ⟨20, by decide⟩ (by decide)
  have hstore :
      storageLocStore evmRead loc (.int (Int.ofNat ticWord.toNat)) =
        some (Solm.EVM.storageStore evmRead evmRead.executionEnv.codeOwner
          (clipperRedoSalesPackedSlot I)
          (UInt256.lor
            (UInt256.mul
              (UInt256.land clipperSalesUint96Mask
                (UInt256.ofNat evmRead.executionEnv.header.timestamp))
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
            (UInt256.land solcAddrMask
              (Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner
                (clipperRedoSalesPackedSlot I))))) := by
    have hbase :=
      clipperStorageLocStore_uint96_offset20 evmRead (clipperRedoSalesPackedSlot I) ticWord
    rw [clipperSalesUint96Mask_idempotent] at hbase
    rw [u256_land_comm (UInt256.ofNat evmRead.executionEnv.header.timestamp)
      clipperSalesUint96Mask] at hbase
    rw [u256_land_comm
      (Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner
        (clipperRedoSalesPackedSlot I)) solcAddrMask] at hbase
    simpa [loc, ticWord] using hbase
  have hticWord :
      ticWord.toNat = (UInt256.ofNat evmRead.executionEnv.header.timestamp).toNat % 2 ^ 96 := by
    simpa [ticWord] using
      clipperUInt256LandSalesUint96Mask_toNat (UInt256.ofNat evmRead.executionEnv.header.timestamp)
  have hrhs :
      evalExpr? (config v)
        { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
        evmRead (wrap96 (.env .timestamp)) = .ok (.int (Int.ofNat ticWord.toNat)) := by
    rw [hticWord]
    simpa using
      clipperEvalRedoTimestamp96 v evmRead (clipperRedoLocalsLot evmLoc evmRead I price)
  have hassign :
      assignStorageRef? (config v)
        { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
        evmRead .storage (salesF (.var "id") "tic") (.int (Int.ofNat ticWord.toNat)) =
      .ok ({ contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price },
        Solm.EVM.storageStore evmRead evmRead.executionEnv.codeOwner
          (clipperRedoSalesPackedSlot I)
          (UInt256.lor
            (UInt256.mul
              (UInt256.land clipperSalesUint96Mask
                (UInt256.ofNat evmRead.executionEnv.header.timestamp))
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
            (UInt256.land solcAddrMask
              (Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner
                (clipperRedoSalesPackedSlot I))))) := by
    apply assignStorageRef_storage_scalar
      (er := clipperRedoSalesTicRef I)
      (ty := uint96St) (loc := loc)
    · simp [salesF, clipperRedoLocalsLot, clipperRedoLocalsTab, clipperRedoLocalsSt,
        clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr, clipperRedoStore]
    · simp [salesF, clipperRedoSalesTicRef, clipperRedoIdValue, clipperRedoIdKey,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalRedoVarIdAfterLot v evmLoc evmRead evmRead I price, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure]
    · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, SaleStructTy, uint96St]
    · rfl
    · exact hstore
  exact ExecStmt.assign hrhs hassign

theorem clipperRedoAssignSalesTicTimestampPost (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
      evmRead
      (.assign .storage (salesF (.var "id") "tic") (wrap96 (.env .timestamp)))
      (.ok { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
        (clipperRedoPostTicState evmRead I)) := by
  simpa [clipperRedoPostTicState, clipperRedoPostTicPackedWord] using
    clipperRedoAssignSalesTicTimestampExact v evmLoc evmRead I price

theorem clipperRedoAssignSalesTicTimestamp (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    ∃ evmTic,
      ExecStmt (config v)
        { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
        evmRead
        (.assign .storage (salesF (.var "id") "tic") (wrap96 (.env .timestamp)))
        (.ok { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
          evmTic) := by
  exact ⟨_, clipperRedoAssignSalesTicTimestampExact v evmLoc evmRead I price⟩

theorem clipperRedoDoneTrueGetFeedPriceSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hgetFeedPrice :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v)
        { contract := contract v, locals := clipperRedoLocalsLot evmLock evmPrice I price }
        (clipperRedoPostTicState evmPrice I)
        (.internalCall "getFeedPrice" [] "feedPrice") .reverted) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  intro locals evm0
  let evmLock := clipperRedoLockedState evm0
  let evmTic := clipperRedoPostTicState evmPrice I
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperRedoLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTic evmLock I }
  let topFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
  let tabFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTab evmLock evmPrice I price }
  let lotFrame : Frame := { contract := contract v, locals := clipperRedoLocalsLot evmLock evmPrice I price }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock, clipperRedoLockedState] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool true) := by
    apply evalExpr_clipperRedoStopped_lt_two_true
    · simp [locals]
    · simpa [evmLock, clipperRedoLockedState, evm0, initState, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
        storageStore_executionEnv] using hstopped
  have husrLoad : clipperRedoSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperRedoSalesUsrEVMWord, clipperRedoSalesUsrWord, evmLock,
      clipperRedoLockedState, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperRedoLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalRedoSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperRedoLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperRedoSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalRedoSalesTicAfterUsr v evmLock I))
  have hletTop :
      ExecStmt (config v) ticFrame evmLock
        (.letDecl "top" (some uint256) (.storage (salesF (.var "id") "top")))
        (.ok topFrame evmLock) := by
    simpa [ticFrame, topFrame, clipperRedoLocalsTop] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := ticFrame) (evm := evmLock) (name := "top")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "top"))
        (value := .int (Int.ofNat (clipperRedoSalesTopEVMWord evmLock I).toNat))
        (by simpa [ticFrame] using clipperEvalRedoSalesTopAfterTic v evmLock I))
  have husrEval :
      evalExpr? (config v) topFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [topFrame] using clipperEvalRedoUsrNeZeroAfterTop_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) topFrame evmLock
        (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok stFrame evmPrice) := by
    simpa [topFrame, stFrame, evmLock, evm0] using hstatus
  have hdoneEval :
      evalExpr? (config v) stFrame evmPrice (tuple0 (.var "st")) = .ok (.bool true) := by
    simpa [stFrame] using clipperEvalRedoDoneFromStatusAt v evmLock evmPrice I true price
  have hletTab :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [stFrame, tabFrame, clipperRedoLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat (clipperRedoSalesTabEVMWord evmPrice I).toNat))
        (by simpa [stFrame] using
          clipperEvalRedoSalesTabAfterStatusTrue v evmLock evmPrice I price))
  have hletLot :
      ExecStmt (config v) tabFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [tabFrame, lotFrame, clipperRedoLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := tabFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat (clipperRedoSalesLotEVMWord evmPrice I).toNat))
        (by simpa [tabFrame] using
          clipperEvalRedoSalesLotAfterTab v evmLock evmPrice I price))
  have hassignTic :
      ExecStmt (config v) lotFrame evmPrice
        (.assign .storage (salesF (.var "id") "tic") (wrap96 (.env .timestamp)))
        (.ok lotFrame evmTic) := by
    simpa [lotFrame, evmTic] using
      clipperRedoAssignSalesTicTimestampPost v evmLock evmPrice I price
  have hgetFeedPrice' :
      ExecStmt (config v) lotFrame evmTic
        (.internalCall "getFeedPrice" [] "feedPrice") .reverted := by
    simpa [lotFrame, evmTic, evmLock, evm0] using hgetFeedPrice
  have hblock :
      ExecBlock (config v) startFrame evm0 (redoTransition v).body .reverted := by
    simpa [redoTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal hletTop ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
        refine ExecBlock.consNormal hletTab ?_
        refine ExecBlock.consNormal hletLot ?_
        refine ExecBlock.consNormal hassignTic ?_
        exact ExecBlock.consRevert hgetFeedPrice')
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperRedoDoneTrueGetFeedPriceNoCodeSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hnoCode :
      (UInt256.ofNat
        (((clipperRedoPostTicState evmPrice I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I))).option 0
            (fun acc => acc.code.size))).toNat = 0) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  apply clipperRedoDoneTrueGetFeedPriceSourceReverts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus
  · simpa using
      clipperGetFeedPriceCallRevertsSpotterIlksNoCode v (clipperRedoPostTicState evmPrice I)
        (clipperRedoLocalsLot
          (clipperRedoLockedState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
          evmPrice I price)
        "feedPrice" hnoCode

theorem clipperRedoDoneTrueGetFeedPriceCallFailureSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmIlks : EVM.State} {out : ByteArray} (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hcode :
      0 < (UInt256.ofNat
        (((clipperRedoPostTicState evmPrice I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (clipperRedoPostTicState evmPrice I)
        (EVM.address (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I)))
        "spotterIlks" 0 [v.ilk] (false, evmIlks, out) true) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  apply clipperRedoDoneTrueGetFeedPriceSourceReverts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus
  · simpa using
      clipperGetFeedPriceCallRevertsSpotterIlksCallFailure v
        (clipperRedoLocalsLot
        (clipperRedoLockedState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
        evmPrice I price)
      "feedPrice" hcode hcall

theorem clipperRedoDoneTrueGetFeedPriceDecodeSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmIlks : EVM.State} {out : ByteArray} (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hcode :
      0 < (UInt256.ofNat
        (((clipperRedoPostTicState evmPrice I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (clipperRedoPostTicState evmPrice I)
        (EVM.address (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I)))
        "spotterIlks" 0 [v.ilk] (true, evmIlks, out) true)
    (hdec : (config v).externalABI.decode? "spotterIlks" out = none) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  apply clipperRedoDoneTrueGetFeedPriceSourceReverts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus
  · simpa using
      clipperGetFeedPriceCallRevertsSpotterIlksDecode v
        (clipperRedoLocalsLot
          (clipperRedoLockedState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
          evmPrice I price)
        "feedPrice" hcode hcall hdec

theorem clipperRedoDoneTrueGetFeedPricePipNoCodeSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmIlks : EVM.State} {outIlks : ByteArray} (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hcodeIlks :
      0 < (UInt256.ofNat
        (((clipperRedoPostTicState evmPrice I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) (clipperRedoPostTicState evmPrice I)
        (EVM.address (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I)))
        "spotterIlks" 0 [v.ilk] (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hnoCodePip :
      (UInt256.ofNat
        ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  apply clipperRedoDoneTrueGetFeedPriceSourceReverts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus
  · simpa using
      clipperGetFeedPriceCallRevertsPipPeekNoCode v
        (clipperRedoLocalsLot
          (clipperRedoLockedState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
          evmPrice I price)
        "feedPrice" hcodeIlks hcallIlks hdecIlks hnoCodePip

theorem clipperRedoDoneTrueGetFeedPricePipCallFailureSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmIlks evmPeek : EVM.State} {outIlks outPeek : ByteArray}
    (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hcodeIlks :
      0 < (UInt256.ofNat
        (((clipperRedoPostTicState evmPrice I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) (clipperRedoPostTicState evmPrice I)
        (EVM.address (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I)))
        "spotterIlks" 0 [v.ilk] (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat
        ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (false, evmPeek, outPeek) true) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  apply clipperRedoDoneTrueGetFeedPriceSourceReverts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus
  · simpa using
      clipperGetFeedPriceCallRevertsPipPeekCallFailure v
        (clipperRedoLocalsLot
          (clipperRedoLockedState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
          evmPrice I price)
        "feedPrice" hcodeIlks hcallIlks hdecIlks hcodePip hcallPeek

theorem clipperRedoDoneTrueGetFeedPricePipDecodeSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmIlks evmPeek : EVM.State} {outIlks outPeek : ByteArray}
    (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hcodeIlks :
      0 < (UInt256.ofNat
        (((clipperRedoPostTicState evmPrice I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) (clipperRedoPostTicState evmPrice I)
        (EVM.address (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I)))
        "spotterIlks" 0 [v.ilk] (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat
        ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evmPeek, outPeek) true)
    (hdecPeek : (config v).externalABI.decode? "peek" outPeek = none) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  apply clipperRedoDoneTrueGetFeedPriceSourceReverts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus
  · simpa using
      clipperGetFeedPriceCallRevertsPipPeekDecode v
        (clipperRedoLocalsLot
          (clipperRedoLockedState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
          evmPrice I price)
        "feedPrice" hcodeIlks hcallIlks hdecIlks hcodePip hcallPeek hdecPeek

theorem clipperRedoDoneTrueGetFeedPricePipHasFalseSourceReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice evmIlks evmPeek : EVM.State} {outIlks outPeek : ByteArray}
    (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I true price }
          evmPrice))
    (hcodeIlks :
      0 < (UInt256.ofNat
        (((clipperRedoPostTicState evmPrice I).lookupAccount
          (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) (clipperRedoPostTicState evmPrice I)
        (EVM.address (clipperGetFeedPriceSpotterAddress (clipperRedoPostTicState evmPrice I)))
        "spotterIlks" 0 [v.ilk] (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat
        ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evmPeek, outPeek) true)
    (hdecPeek : (config v).externalABI.decode? "peek" outPeek =
      some (clipperPipPeekValues outPeek))
    (hhasFalse : clipperPipPeekHasWord outPeek = ⟨0⟩) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  apply clipperRedoDoneTrueGetFeedPriceSourceReverts
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus
  · simpa using
      clipperGetFeedPriceCallRevertsPipPeekHasFalse v
        (clipperRedoLocalsLot
          (clipperRedoLockedState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
          evmPrice I price)
        "feedPrice" hcodeIlks hcallIlks hdecIlks hcodePip hcallPeek hdecPeek
        hhasFalse

end Benchmarks.Dss.Clipper
