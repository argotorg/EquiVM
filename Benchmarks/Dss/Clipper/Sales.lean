import Benchmarks.Dss.Clipper.UintEntry
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## ABI decode and source-level body for `sales(uint256)` -/

abbrev clipperSalesArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperSalesArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperSalesArgWord I).toNat)

abbrev clipperSalesArgKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (clipperSalesArgWord I).toNat)

abbrev clipperSalesStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (clipperSalesArgValue I)

abbrev clipperSalesBaseSlot (I : ExecutionEnv) : UInt256 :=
  salesBase (clipperSalesArgKey I)

abbrev clipperSalesPosSlot (I : ExecutionEnv) : UInt256 :=
  clipperSalesBaseSlot I

abbrev clipperSalesTabSlot (I : ExecutionEnv) : UInt256 :=
  clipperSalesBaseSlot I + ⟨1⟩

abbrev clipperSalesLotSlot (I : ExecutionEnv) : UInt256 :=
  clipperSalesBaseSlot I + ⟨2⟩

abbrev clipperSalesPackedSlot (I : ExecutionEnv) : UInt256 :=
  clipperSalesBaseSlot I + ⟨3⟩

abbrev clipperSalesTopSlot (I : ExecutionEnv) : UInt256 :=
  clipperSalesBaseSlot I + ⟨4⟩

abbrev clipperSalesPosRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperSalesArgKey I), .field "pos"] }

abbrev clipperSalesTabRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperSalesArgKey I), .field "tab"] }

abbrev clipperSalesLotRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperSalesArgKey I), .field "lot"] }

abbrev clipperSalesUsrRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperSalesArgKey I), .field "usr"] }

abbrev clipperSalesTicRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperSalesArgKey I), .field "tic"] }

abbrev clipperSalesTopRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperSalesArgKey I), .field "top"] }

def clipperSalesPackedTicWord (w : UInt256) : UInt256 :=
  UInt256.land (UInt256.div w (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)

theorem clipperDecode_sales_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (salesTransition.params.map Param.name)
      (transitionSignature salesTransition).paramTypes I.calldata =
        some (clipperSalesStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["arg0"] [uint256] I.calldata = _
  simpa [config, clipperSalesStore, clipperSalesArgValue, clipperSalesArgWord] using
    decodeCalldataWithMode_legacyUint256_ok (cd := I.calldata) (x := "arg0") hsz36

theorem clipperDecode_sales_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (salesTransition.params.map Param.name)
      (transitionSignature salesTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["arg0"] [uint256] I.calldata = none
  simpa [config] using
    decodeCalldataWithMode_legacyUint256_none_short (cd := I.calldata) (x := "arg0")
      hsz4 hshort

theorem clipperStorageLocLoad_uint96 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint96Loc slot ⟨20, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)).toNat) := by
  have h := storageLocLoad_uint_offset (evm := evm) (slot := slot)
    (offset := ⟨20, by decide⟩) (size := ⟨12, by decide⟩)
    (width := ⟨96, by decide⟩) (hbound := by decide) (by decide) (by decide)
  simpa [uint96Loc, uint96Int, show (256 ^ 20 = 2 ^ 160) by native_decide,
    show (256 ^ 12 = 2 ^ 96) by native_decide, UInt256.ofNat] using h

theorem clipperSalesBaseSlot_eq (I : ExecutionEnv) :
    clipperSalesBaseSlot I = solcMappingSlot ⟨12⟩ (clipperSalesArgWord I) := by
  unfold clipperSalesBaseSlot salesBase mapSlot solcMappingSlot clipperSalesArgKey
  rw [keyValueToWord_uint256]

theorem clipperSalesSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 18)) :
    clipperSelWord I = clipperSelNat 18 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xb5 0xf5 0x22 0xf7 (clipperSelNat 18)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_sales (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 18)) :
    dispatchMsg (contract v) I.calldata = some salesTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition])
    (post :=
      [spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
        upchostTransition v, vatTransition v, vowTransition, wardsTransition, yankTransition v])
    (ti := salesTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, ilkSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, redoSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, relySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, salesSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperSalesBodyReturns (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm (clipperSalesStore I)
      salesTransition.body
      (.returned { contract := contract v, locals := clipperSalesStore I } evm
        (some [
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesPosSlot I)).toNat),
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesTabSlot I)).toNat),
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesLotSlot I)).toNat),
          .address (AccountAddress.ofNat
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperSalesPackedSlot I)) solcAddrMask).toNat),
          .int (Int.ofNat (clipperSalesPackedTicWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperSalesPackedSlot I))).toNat),
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesTopSlot I)).toNat)])) := by
  let frame : Frame := { contract := contract v, locals := clipperSalesStore I }
  have hpos : evalExpr? (config v) frame evm (.storage (salesF (.var "arg0") "pos")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesPosSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := salesF (.var "arg0") "pos") (er := clipperSalesPosRef I)
      (t := .int uint256Int) (loc := wordLoc (clipperSalesPosSlot I))
      (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesPosSlot I)).toNat))
      (by simp [frame, salesF, clipperSalesStore])
      (by
        simp [frame, clipperSalesPosRef, clipperSalesArgValue, clipperSalesArgKey,
          clipperSalesStore, salesF, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind])
      (by simp [frame, clipperSalesArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, SaleStructTy, uint256St])
      (by rfl)
      (by simpa [clipperSalesPosSlot, clipperSalesBaseSlot, wordLoc, uint256Loc] using
        clipperStorageLocLoad_uint256 evm (clipperSalesPosSlot I))
  have htab : evalExpr? (config v) frame evm (.storage (salesF (.var "arg0") "tab")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesTabSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := salesF (.var "arg0") "tab") (er := clipperSalesTabRef I)
      (t := .int uint256Int) (loc := wordLoc (clipperSalesTabSlot I))
      (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesTabSlot I)).toNat))
      (by simp [frame, salesF, clipperSalesStore])
      (by
        simp [frame, clipperSalesTabRef, clipperSalesArgValue, clipperSalesArgKey,
          clipperSalesStore, salesF, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind])
      (by simp [frame, clipperSalesArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, SaleStructTy, uint256St])
      (by rfl)
      (by simpa [clipperSalesTabSlot, clipperSalesBaseSlot, wordLoc, uint256Loc] using
        clipperStorageLocLoad_uint256 evm (clipperSalesTabSlot I))
  have hlot : evalExpr? (config v) frame evm (.storage (salesF (.var "arg0") "lot")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesLotSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := salesF (.var "arg0") "lot") (er := clipperSalesLotRef I)
      (t := .int uint256Int) (loc := wordLoc (clipperSalesLotSlot I))
      (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesLotSlot I)).toNat))
      (by simp [frame, salesF, clipperSalesStore])
      (by
        simp [frame, clipperSalesLotRef, clipperSalesArgValue, clipperSalesArgKey,
          clipperSalesStore, salesF, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind])
      (by simp [frame, clipperSalesArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, SaleStructTy, uint256St])
      (by rfl)
      (by simpa [clipperSalesLotSlot, clipperSalesBaseSlot, wordLoc, uint256Loc] using
        clipperStorageLocLoad_uint256 evm (clipperSalesLotSlot I))
  have husr : evalExpr? (config v) frame evm (.storage (salesF (.var "arg0") "usr")) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperSalesPackedSlot I))
        solcAddrMask).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := salesF (.var "arg0") "usr") (er := clipperSalesUsrRef I)
      (t := .address) (loc := addrLoc (clipperSalesPackedSlot I))
      (value := .address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperSalesPackedSlot I))
        solcAddrMask).toNat))
      (by simp [frame, salesF, clipperSalesStore])
      (by
        simp [frame, clipperSalesUsrRef, clipperSalesArgValue, clipperSalesArgKey,
          clipperSalesStore, salesF, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind])
      (by simp [frame, clipperSalesArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, SaleStructTy, addrSt])
      (by rfl)
      (by simpa [clipperSalesPackedSlot, clipperSalesBaseSlot] using
        clipperStorageLocLoad_address evm (clipperSalesPackedSlot I))
  have htic : evalExpr? (config v) frame evm (.storage (salesF (.var "arg0") "tic")) =
      .ok (.int (Int.ofNat (clipperSalesPackedTicWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperSalesPackedSlot I))).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := salesF (.var "arg0") "tic") (er := clipperSalesTicRef I)
      (t := .int uint96Int)
      (loc := uint96Loc (clipperSalesPackedSlot I) ⟨20, by decide⟩ (by decide))
      (value := .int (Int.ofNat (clipperSalesPackedTicWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperSalesPackedSlot I))).toNat))
      (by simp [frame, salesF, clipperSalesStore])
      (by
        simp [frame, clipperSalesTicRef, clipperSalesArgValue, clipperSalesArgKey,
          clipperSalesStore, salesF, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind])
      (by simp [frame, clipperSalesArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, SaleStructTy, uint96St])
      (by rfl)
      (by simpa [clipperSalesPackedTicWord, clipperSalesPackedSlot, clipperSalesBaseSlot] using
        clipperStorageLocLoad_uint96 evm (clipperSalesPackedSlot I))
  have htop : evalExpr? (config v) frame evm (.storage (salesF (.var "arg0") "top")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesTopSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := salesF (.var "arg0") "top") (er := clipperSalesTopRef I)
      (t := .int uint256Int) (loc := wordLoc (clipperSalesTopSlot I))
      (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperSalesTopSlot I)).toNat))
      (by simp [frame, salesF, clipperSalesStore])
      (by
        simp [frame, clipperSalesTopRef, clipperSalesArgValue, clipperSalesArgKey,
          clipperSalesStore, salesF, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind])
      (by simp [frame, clipperSalesArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, SaleStructTy, uint256St])
      (by rfl)
      (by simpa [clipperSalesTopSlot, clipperSalesBaseSlot, wordLoc, uint256Loc] using
        clipperStorageLocLoad_uint256 evm (clipperSalesTopSlot I))
  have hreturns : evalExprs? (config v) frame evm
      [ .storage (salesF (.var "arg0") "pos"), .storage (salesF (.var "arg0") "tab"),
        .storage (salesF (.var "arg0") "lot"), .storage (salesF (.var "arg0") "usr"),
        .storage (salesF (.var "arg0") "tic"), .storage (salesF (.var "arg0") "top") ] =
      .ok [
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesPosSlot I)).toNat),
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesTabSlot I)).toNat),
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesLotSlot I)).toNat),
          .address (AccountAddress.ofNat
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperSalesPackedSlot I)) solcAddrMask).toNat),
          .int (Int.ofNat (clipperSalesPackedTicWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperSalesPackedSlot I))).toNat),
          .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperSalesTopSlot I)).toNat)] := by
    simp [evalExprs?, hpos, htab, hlot, husr, htic, htop, EvalResult.bind, bind, pure]
  simpa [salesTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

abbrev clipperSalesReturnBytes (pos tab lot usr tic top : UInt256) : ByteArray :=
  UInt256.toByteArray pos ++ UInt256.toByteArray tab ++ UInt256.toByteArray lot ++
    UInt256.toByteArray (UInt256.land usr solcAddrMask) ++ UInt256.toByteArray tic ++
      UInt256.toByteArray top

theorem clipperEncodeABIValue_uint96 (v : UInt256) (hv : v.toNat < EVM.twoPow 96) :
    encodeABIValue? uint96 (.int (Int.ofNat v.toNat)) = some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  simp [uint96, uint96Int, encodeABIValue?, encodeABIWord?, hword, hv]

theorem clipperEncodeABIValue_addr_masked (w : UInt256) :
    encodeABIValue? addr (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (EVM.Word.toBytesBE (UInt256.land w solcAddrMask)) := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask := by
    exact u256_ofNat_toNat _
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

theorem clipperSalesReturnEncoding (pos tab lot usr tic top : UInt256)
    (htic : tic.toNat < EVM.twoPow 96) :
    encodeReturnValues? [uint256, uint256, uint256, addr, uint96, uint256]
      [ .int (Int.ofNat pos.toNat), .int (Int.ofNat tab.toNat),
        .int (Int.ofNat lot.toNat),
        .address (AccountAddress.ofNat (UInt256.land usr solcAddrMask).toNat),
        .int (Int.ofNat tic.toNat), .int (Int.ofNat top.toNat)] =
      some (clipperSalesReturnBytes pos tab lot usr tic top) := by
  have hencPos := clipperEncodeABIValue_uint256 pos
  have hencTab := clipperEncodeABIValue_uint256 tab
  have hencLot := clipperEncodeABIValue_uint256 lot
  have hencUsr := clipperEncodeABIValue_addr_masked usr
  have hencTic := clipperEncodeABIValue_uint96 tic htic
  have hencTop := clipperEncodeABIValue_uint256 top
  have hhead : abiTupleHeadSize? [uint256, uint256, uint256, addr, uint96, uint256] =
      some 192 := by
    native_decide
  have hdu : isDynamicABIType uint256 = false := by rfl
  have hda : isDynamicABIType addr = false := by rfl
  have hd96 : isDynamicABIType uint96 = false := by rfl
  unfold clipperSalesReturnBytes
  rw [toByteArray_eq_toBytesBE pos, toByteArray_eq_toBytesBE tab,
    toByteArray_eq_toBytesBE lot, toByteArray_eq_toBytesBE (UInt256.land usr solcAddrMask),
    toByteArray_eq_toBytesBE tic, toByteArray_eq_toBytesBE top]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, hhead,
    hencPos, hencTab, hencLot, hencUsr, hencTic, hencTop, hdu, hda, hd96, bind,
    Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  rfl

abbrev clipperSalesUint96Mask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩

def clipperSalesReturnWrites (pos tab lot usr tic top : UInt256) : List (Nat × UInt256) :=
  [(128, pos), (160, tab), (192, lot), (224, UInt256.land usr solcAddrMask),
    (256, tic), (288, top)]

noncomputable def clipperSalesReturnMem
    (scratch : ByteArray) (pos tab lot usr tic top : UInt256) : ByteArray :=
  writeCascade scratch (clipperSalesReturnWrites pos tab lot usr tic top)

theorem clipperSalesReturnMem_size {scratch : ByteArray} (pos tab lot usr tic top : UInt256)
    (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).size = 320 := by
  unfold clipperSalesReturnMem clipperSalesReturnWrites
  exact writeCascade_size_of_base scratch
    [(128, pos), (160, tab), (192, lot), (224, UInt256.land usr solcAddrMask),
      (256, tic), (288, top)]
    hscratch
    (by simpa [WriteGapsOk] using (lt_usize 32 (by norm_num)))
    (by rfl)

theorem clipperSalesReturnMem_read64 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSalesReturnMem
  rw [writeCascade_read_preserved_of_base scratch
    (clipperSalesReturnWrites pos tab lot usr tic top) hscratch]
  · exact hread64
  · simp [clipperSalesReturnWrites, WindowDisjointFromWrites]
    exact lt_usize 32 (by norm_num)

theorem clipperSalesReturnMem_mload64 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperSalesReturnMem scratch pos tab lot usr tic top).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [clipperSalesReturnMem_size pos tab lot usr tic top hscratch]; decide)
    (by decide)
    (clipperSalesReturnMem_read64 pos tab lot usr tic top hscratch hread64)

theorem clipperSalesReturnMem_readWord128 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 128 32 =
      UInt256.toByteArray pos := by
  unfold clipperSalesReturnMem clipperSalesReturnWrites
  exact writeCascade_read_word_of_head_of_base scratch pos
    [(160, tab), (192, lot), (224, UInt256.land usr solcAddrMask), (256, tic), (288, top)]
    hscratch (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem clipperSalesReturnMem_readWord160 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 160 32 =
      UInt256.toByteArray tab := by
  unfold clipperSalesReturnMem clipperSalesReturnWrites
  rw [writeCascade_cons]
  have hbase : (writeWord scratch 128 pos).size = 160 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  exact writeCascade_read_word_of_head_of_base (writeWord scratch 128 pos) tab
    [(192, lot), (224, UInt256.land usr solcAddrMask), (256, tic), (288, top)]
    hbase (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem clipperSalesReturnMem_readWord192 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 192 32 =
      UInt256.toByteArray lot := by
  unfold clipperSalesReturnMem clipperSalesReturnWrites
  rw [writeCascade_cons, writeCascade_cons]
  have hbase0 : (writeWord scratch 128 pos).size = 160 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  have hbase1 : (writeWord (writeWord scratch 128 pos) 160 tab).size = 192 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  exact writeCascade_read_word_of_head_of_base (writeWord (writeWord scratch 128 pos) 160 tab)
    lot [(224, UInt256.land usr solcAddrMask), (256, tic), (288, top)]
    hbase1 (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem clipperSalesReturnMem_readWord224 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 224 32 =
      UInt256.toByteArray (UInt256.land usr solcAddrMask) := by
  unfold clipperSalesReturnMem clipperSalesReturnWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  have hbase0 : (writeWord scratch 128 pos).size = 160 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  have hbase1 : (writeWord (writeWord scratch 128 pos) 160 tab).size = 192 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  have hbase2 :
      (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot).size = 224 := by
    rw [writeWord_size]
    · rw [hbase1]
      norm_num
    · rw [hbase1]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot)
    (UInt256.land usr solcAddrMask) [(256, tic), (288, top)]
    hbase2 (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem clipperSalesReturnMem_readWord256 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 256 32 =
      UInt256.toByteArray tic := by
  unfold clipperSalesReturnMem clipperSalesReturnWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  have hbase0 : (writeWord scratch 128 pos).size = 160 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  have hbase1 : (writeWord (writeWord scratch 128 pos) 160 tab).size = 192 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  have hbase2 :
      (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot).size = 224 := by
    rw [writeWord_size]
    · rw [hbase1]
      norm_num
    · rw [hbase1]
      native_decide
  have hbase3 :
      (writeWord (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot) 224
        (UInt256.land usr solcAddrMask)).size = 256 := by
    rw [writeWord_size]
    · rw [hbase2]
      norm_num
    · rw [hbase2]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot) 224
      (UInt256.land usr solcAddrMask))
    tic [(288, top)] hbase3 (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem clipperSalesReturnMem_readWord288 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 288 32 =
      UInt256.toByteArray top := by
  unfold clipperSalesReturnMem clipperSalesReturnWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  have hbase0 : (writeWord scratch 128 pos).size = 160 := by
    rw [writeWord_size]
    · rw [hscratch]
      norm_num
    · rw [hscratch]
      native_decide
  have hbase1 : (writeWord (writeWord scratch 128 pos) 160 tab).size = 192 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  have hbase2 :
      (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot).size = 224 := by
    rw [writeWord_size]
    · rw [hbase1]
      norm_num
    · rw [hbase1]
      native_decide
  have hbase3 :
      (writeWord (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot) 224
        (UInt256.land usr solcAddrMask)).size = 256 := by
    rw [writeWord_size]
    · rw [hbase2]
      norm_num
    · rw [hbase2]
      native_decide
  have hbase4 :
      (writeWord
        (writeWord (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot) 224
          (UInt256.land usr solcAddrMask))
        256 tic).size = 288 := by
    rw [writeWord_size]
    · rw [hbase3]
      norm_num
    · rw [hbase3]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (writeWord (writeWord (writeWord scratch 128 pos) 160 tab) 192 lot) 224
        (UInt256.land usr solcAddrMask))
      256 tic)
    top [] hbase4 (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem clipperSalesReturnMem_read128_192 {scratch : ByteArray}
    (pos tab lot usr tic top : UInt256) (hscratch : scratch.size = 96) :
    (clipperSalesReturnMem scratch pos tab lot usr tic top).readWithPadding 128 192 =
      clipperSalesReturnBytes pos tab lot usr tic top := by
  rw [byteArray_readWithPadding_split _ 128 32 160 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperSalesReturnMem_size pos tab lot usr tic top hscratch])]
  rw [byteArray_readWithPadding_split _ 160 32 128 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperSalesReturnMem_size pos tab lot usr tic top hscratch])]
  rw [byteArray_readWithPadding_split _ 192 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperSalesReturnMem_size pos tab lot usr tic top hscratch])]
  rw [byteArray_readWithPadding_split _ 224 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperSalesReturnMem_size pos tab lot usr tic top hscratch])]
  rw [byteArray_readWithPadding_split _ 256 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [clipperSalesReturnMem_size pos tab lot usr tic top hscratch])]
  rw [clipperSalesReturnMem_readWord128 (scratch := scratch) pos tab lot usr tic top hscratch,
    clipperSalesReturnMem_readWord160 (scratch := scratch) pos tab lot usr tic top hscratch,
    clipperSalesReturnMem_readWord192 (scratch := scratch) pos tab lot usr tic top hscratch,
    clipperSalesReturnMem_readWord224 (scratch := scratch) pos tab lot usr tic top hscratch,
    clipperSalesReturnMem_readWord256 (scratch := scratch) pos tab lot usr tic top hscratch,
    clipperSalesReturnMem_readWord288 (scratch := scratch) pos tab lot usr tic top hscratch]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [clipperSalesReturnBytes, ByteArray.data_append, Array.toList_append]

/-! ## EVM reachability -/

set_option maxHeartbeats 1000000 in
theorem clipperReachSalesBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 18)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1161⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperSalesSelectorWord hsz hsel
  have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 20, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨260⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h162 := clipperSplitTaken (pc := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 3)
    (tgt := (⟨162⟩ : UInt256)) h43
    (by change decode code (⟨43⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨43⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 3, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨43⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨43⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨162⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨43⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨162⟩ : UInt256) (by native_decide))
    (by simp)
  have h163 := h162.jumpdest
    (by
      change decode code (⟨162⟩ : UInt256) = some (.JUMPDEST, .none)
      clipper_decode)
    (by evm_ov)
  have h174 := clipperSplitNotTaken (pc := (⟨163⟩ : UInt256))
    (next := (⟨174⟩ : UInt256)) (pivot := clipperSelNat 13)
    (tgt := (⟨222⟩ : UInt256)) h163
    (by change decode code (⟨163⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨163⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 13, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨163⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨163⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨222⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨163⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h185 := clipperArmNotTaken (pc := (⟨174⟩ : UInt256))
    (next := (⟨185⟩ : UInt256)) (sel := clipperSelNat 13)
    (tgt := (⟨1057⟩ : UInt256)) h174
    (by change decode code (⟨174⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨174⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 13, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨174⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨174⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1057⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨174⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h196 := clipperArmNotTaken (pc := (⟨185⟩ : UInt256))
    (next := (⟨196⟩ : UInt256)) (sel := clipperSelNat 2)
    (tgt := (⟨1115⟩ : UInt256)) h185
    (by change decode code (⟨185⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨185⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 2, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨185⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨185⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1115⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨185⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h207 := clipperArmNotTaken (pc := (⟨196⟩ : UInt256))
    (next := (⟨207⟩ : UInt256)) (sel := clipperSelNat 7)
    (tgt := (⟨1123⟩ : UInt256)) h196
    (by change decode code (⟨196⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨196⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 7, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨196⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨196⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1123⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨196⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h1161 := clipperArmTaken (pc := (⟨207⟩ : UInt256)) (sel := clipperSelNat 18)
    (tgt := (⟨1161⟩ : UInt256)) h207
    (by change decode code (⟨207⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨207⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 18, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨207⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨207⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1161⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨207⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1161⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1161⟩

@[reducible] def clipperSalesStructGetterWf (code : ByteArray) : Prop :=
  decode code (⟨6668⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨6669⟩ : UInt256) = some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode code (⟨6671⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨6673⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨6674⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (⟨6676⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨6677⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨6678⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨6679⟩ : UInt256) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (⟨6681⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨6682⟩ : UInt256) = some (.KECCAK256, .none)
  ∧ decode code (⟨6683⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨6684⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨6685⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨6687⟩ : UInt256) = some (.DUP3, .none)
  ∧ decode code (⟨6688⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨6689⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨6690⟩ : UInt256) = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code (⟨6692⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨6693⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨6694⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨6695⟩ : UInt256) = some (.Push .PUSH1, some (⟨3⟩, 1))
  ∧ decode code (⟨6697⟩ : UInt256) = some (.DUP5, .none)
  ∧ decode code (⟨6698⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨6699⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨6700⟩ : UInt256) = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code (⟨6702⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨6703⟩ : UInt256) = some (.SWAP5, .none)
  ∧ decode code (⟨6704⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨6705⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨6706⟩ : UInt256) = some (.SWAP3, .none)
  ∧ decode code (⟨6707⟩ : UInt256) = some (.SWAP4, .none)
  ∧ decode code (⟨6708⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨6709⟩ : UInt256) = some (.SWAP3, .none)
  ∧ decode code (⟨6710⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨6711⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨6712⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨6714⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨6716⟩ : UInt256) = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code (⟨6718⟩ : UInt256) = some (.SHL, .none)
  ∧ decode code (⟨6719⟩ : UInt256) = some (.SUB, .none)
  ∧ decode code (⟨6720⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨6721⟩ : UInt256) = some (.AND, .none)
  ∧ decode code (⟨6722⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨6723⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨6725⟩ : UInt256) = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code (⟨6727⟩ : UInt256) = some (.SHL, .none)
  ∧ decode code (⟨6728⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨6729⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨6730⟩ : UInt256) = some (.DIV, .none)
  ∧ decode code (⟨6731⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨6733⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨6735⟩ : UInt256) = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code (⟨6737⟩ : UInt256) = some (.SHL, .none)
  ∧ decode code (⟨6738⟩ : UInt256) = some (.SUB, .none)
  ∧ decode code (⟨6739⟩ : UInt256) = some (.AND, .none)
  ∧ decode code (⟨6740⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨6741⟩ : UInt256) = some (.DUP7, .none)
  ∧ decode code (⟨6742⟩ : UInt256) = some (.JUMP, .none)

set_option maxHeartbeats 4000000 in
theorem RD.clipperSalesStructGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨6668⟩ : UInt256) (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperSalesStructGetterWf code)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ key) + ⟨4⟩) ::
        clipperSalesPackedTicWord (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ key) + ⟨3⟩)) ::
        UInt256.land (solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ key) + ⟨3⟩)) solcAddrMask ::
        solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ key) + ⟨2⟩) ::
        solcSlotWord σ ee ((solcMappingSlot ⟨12⟩ key) + ⟨1⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨12⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨12⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd6668, hd6669, hd6671, hd6673, hd6674, hd6676, hd6677, hd6678, hd6679,
      hd6681, hd6682, hd6683, hd6684, hd6685, hd6687, hd6688, hd6689, hd6690,
      hd6692, hd6693, hd6694, hd6695, hd6697, hd6698, hd6699, hd6700, hd6702,
      hd6703, hd6704, hd6705, hd6706, hd6707, hd6708, hd6709, hd6710, hd6711,
      hd6712, hd6714, hd6716, hd6718, hd6719, hd6720, hd6721, hd6722, hd6723,
      hd6725, hd6727, hd6728, hd6729, hd6730, hd6731, hd6733, hd6735, hd6737,
      hd6738, hd6739, hd6740, hd6741, hd6742⟩
  have rd6669 := h.jumpdest hd6668 (by simp only [List.length_cons]; omega)
  have rd6671 := rd6669.push1 ⟨12⟩ hd6669 (by evm_ov)
  have rd6673 := rd6671.push1 ⟨32⟩ hd6671 (by evm_ov)
  have rd6674 := rd6673.mstore 0 (solcMappingBaseSlotMem ⟨12⟩)
    (UInt256.ofNat 3) hd6673 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6676 := rd6674.push1 ⟨0⟩ hd6674 (by evm_ov)
  have rd6677 := rd6676.swap1 hd6676 (by evm_ov)
  have rd6678 := rd6677.dup2 hd6677 (by evm_ov)
  have rd6679 := rd6678.mstore 0 (solcMappingHashMem ⟨12⟩ key)
    (UInt256.ofNat 3) hd6678 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6681 := rd6679.push1 ⟨64⟩ hd6679 (by evm_ov)
  have rd6682 := rd6681.swap1 hd6681 (by evm_ov)
  have rd6683 := rd6682.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) hd6682 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      solcMappingKeccakSlot ⟨12⟩ key)
    (by native_decide) (by evm_ov)
  have rd6684 := rd6683.dup1 hd6683 (by evm_ov)
  obtain ⟨_, _, rd6685⟩ := rd6684.sload hd6684 (by evm_ov)
  have rd6687 := rd6685.push1 ⟨1⟩ hd6685 (by evm_ov)
  have rd6688 := rd6687.dup3 hd6687 (by evm_ov)
  have rd6689 := rd6688.add hd6688 (by evm_ov)
  obtain ⟨_, _, rd6690⟩ := rd6689.sload hd6689 (by evm_ov)
  have rd6692 := rd6690.push1 ⟨2⟩ hd6690 (by evm_ov)
  have rd6693 := rd6692.dup4 hd6692 (by evm_ov)
  have rd6694 := rd6693.add hd6693 (by evm_ov)
  obtain ⟨_, _, rd6695⟩ := rd6694.sload hd6694 (by evm_ov)
  have rd6697 := rd6695.push1 ⟨3⟩ hd6695 (by evm_ov)
  have rd6698 := rd6697.dup5 hd6697 (by evm_ov)
  have rd6699 := rd6698.add hd6698 (by evm_ov)
  obtain ⟨_, _, rd6700⟩ := rd6699.sload hd6699 (by evm_ov)
  have rd6702 := rd6700.push1 ⟨4⟩ hd6700 (by evm_ov)
  have rd6703 := rd6702.swap1 hd6702 (by evm_ov)
  have rd6704 := rd6703.swap5 hd6703 (by evm_ov)
  have rd6705 := rd6704.add hd6704 (by evm_ov)
  obtain ⟨_, _, rd6706⟩ := rd6705.sload hd6705 (by evm_ov)
  have rd6707 := rd6706.swap3 hd6706 (by evm_ov)
  have rd6708 := rd6707.swap4 hd6707 (by evm_ov)
  have rd6709 := rd6708.swap2 hd6708 (by evm_ov)
  have rd6710 := rd6709.swap3 hd6709 (by evm_ov)
  have rd6711 := rd6710.swap1 hd6710 (by evm_ov)
  have rd6712 := rd6711.swap2 hd6711 (by evm_ov)
  have rd6714 := rd6712.push1 ⟨1⟩ hd6712 (by evm_ov)
  have rd6716 := rd6714.push1 ⟨1⟩ hd6714 (by evm_ov)
  have rd6718 := rd6716.push1 ⟨160⟩ hd6716 (by evm_ov)
  have rd6719 := rd6718.shl hd6718 (by evm_ov)
  have rd6720 := rd6719.sub hd6719 (by evm_ov)
  have rd6721 := rd6720.dup2 hd6720 (by evm_ov)
  have rd6722 := rd6721.and hd6721 (by evm_ov)
  have rd6723 := rd6722.swap2 hd6722 (by evm_ov)
  have rd6725 := rd6723.push1 ⟨1⟩ hd6723 (by evm_ov)
  have rd6727 := rd6725.push1 ⟨160⟩ hd6725 (by evm_ov)
  have rd6728 := rd6727.shl hd6727 (by evm_ov)
  have rd6729 := rd6728.swap1 hd6728 (by evm_ov)
  have rd6730 := rd6729.swap2 hd6729 (by evm_ov)
  have rd6731 := rd6730.div hd6730 (by evm_ov)
  have rd6733 := rd6731.push1 ⟨1⟩ hd6731 (by evm_ov)
  have rd6735 := rd6733.push1 ⟨1⟩ hd6733 (by evm_ov)
  have rd6737 := rd6735.push1 ⟨96⟩ hd6735 (by evm_ov)
  have rd6738 := rd6737.shl hd6737 (by evm_ov)
  have rd6739 := rd6738.sub hd6738 (by evm_ov)
  have rd6740 := rd6739.and hd6739 (by evm_ov)
  have rd6741 := rd6740.swap1 hd6740 (by evm_ov)
  have rd6742 := rd6741.dup7 hd6741 (by evm_ov)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  exact ⟨_, _, by
    simpa [clipperSalesPackedTicWord, solcSlotWord, u256_add_comm, haddrMask,
      u256_land_comm] using rd6742.jump hd6742 hret (by evm_ov)⟩

theorem clipperSalesPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 6668 ≤ lo) (hhi : hi ≤ 6743) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
  | some bs =>
      simp [hIlk]
      omega

theorem clipperSalesStructGetterWfPatched (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperSalesStructGetterWf code := by
  unfold clipperSalesStructGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperSalesPatchesWindowDisjoint32 v <;> native_decide)
      (by apply clipperSalesPatchesWindowDisjoint32 v <;> native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperJumpDest6668 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6668⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperSalesX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1161⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨6668⟩ : UInt256)
      (clipperSalesArgWord I :: ⟨1190⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := (⟨1161⟩ : UInt256))
    (ret := (⟨1190⟩ : UInt256)) (decoded := (⟨1183⟩ : UInt256))
    (need := (⟨32⟩ : UInt256)) hreach
    (by change decode code (⟨1161⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code (⟨1162⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨1190⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨1165⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨1167⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (⟨1168⟩ : UInt256) = some (.CALLDATASIZE, .none)
      clipper_decode)
    (by change decode code (⟨1169⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨1170⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨32⟩, 1))
      clipper_decode)
    (by change decode code (⟨1172⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨1173⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨1174⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨1175⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨1183⟩, 2))
      clipper_decode)
    (by change decode code (⟨1178⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1183⟩ : UInt256) (by native_decide))
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd1184 := hdecoded.jumpdest
    (by
      change decode code (⟨1183⟩ : UInt256) = some (.JUMPDEST, .none)
      clipper_decode)
    (by evm_ov)
  have rd1185 := rd1184.pop
    (by
      change decode code (⟨1184⟩ : UInt256) = some (.POP, .none)
      clipper_decode)
    (by evm_ov)
  have rd1186 := rd1185.calldataload
    (by
      change decode code (⟨1185⟩ : UInt256) = some (.CALLDATALOAD, .none)
      clipper_decode)
    (by evm_ov)
  have rd1189 := rd1186.push2 ⟨6668⟩
    (by
      change decode code (⟨1186⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨6668⟩, 2))
      clipper_decode)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperSalesArgWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      rd1189.jump
        (by change decode code (⟨1189⟩ : UInt256) = some (.JUMP, .none); clipper_decode)
        (clipperJumpDest6668 v hpatch)
        (by evm_ov)⟩

@[reducible] def clipperSalesReturnFromMemWf (code : ByteArray) : Prop :=
  decode code (⟨1190⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨1191⟩ : UInt256) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (⟨1193⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨1194⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨1195⟩ : UInt256) = some (.SWAP7, .none)
  ∧ decode code (⟨1196⟩ : UInt256) = some (.DUP8, .none)
  ∧ decode code (⟨1197⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1198⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨1200⟩ : UInt256) = some (.DUP8, .none)
  ∧ decode code (⟨1201⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1202⟩ : UInt256) = some (.SWAP6, .none)
  ∧ decode code (⟨1203⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1204⟩ : UInt256) = some (.SWAP6, .none)
  ∧ decode code (⟨1205⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1206⟩ : UInt256) = some (.DUP6, .none)
  ∧ decode code (⟨1207⟩ : UInt256) = some (.DUP6, .none)
  ∧ decode code (⟨1208⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1209⟩ : UInt256) = some (.SWAP4, .none)
  ∧ decode code (⟨1210⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1211⟩ : UInt256) = some (.SWAP4, .none)
  ∧ decode code (⟨1212⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1213⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨1215⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨1217⟩ : UInt256) = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code (⟨1219⟩ : UInt256) = some (.SHL, .none)
  ∧ decode code (⟨1220⟩ : UInt256) = some (.SUB, .none)
  ∧ decode code (⟨1221⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1222⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨1223⟩ : UInt256) = some (.AND, .none)
  ∧ decode code (⟨1224⟩ : UInt256) = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code (⟨1226⟩ : UInt256) = some (.DUP6, .none)
  ∧ decode code (⟨1227⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1228⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1229⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨1231⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨1233⟩ : UInt256) = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code (⟨1235⟩ : UInt256) = some (.SHL, .none)
  ∧ decode code (⟨1236⟩ : UInt256) = some (.SUB, .none)
  ∧ decode code (⟨1237⟩ : UInt256) = some (.AND, .none)
  ∧ decode code (⟨1238⟩ : UInt256) = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code (⟨1240⟩ : UInt256) = some (.DUP5, .none)
  ∧ decode code (⟨1241⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1242⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1243⟩ : UInt256) = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code (⟨1245⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨1246⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1247⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1248⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨1249⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1250⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨1251⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1252⟩ : UInt256) = some (.SUB, .none)
  ∧ decode code (⟨1253⟩ : UInt256) = some (.Push .PUSH1, some (⟨192⟩, 1))
  ∧ decode code (⟨1255⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1256⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1257⟩ : UInt256) = some (.RETURN, .none)

set_option maxHeartbeats 2000000 in
theorem RD.clipperSalesReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {top tic usr lot tab pos ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 (⟨1190⟩ : UInt256)
        (top :: tic :: usr :: lot :: tab :: pos :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : clipperSalesReturnFromMemWf code)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hscratch : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 13 ≤ 1024) :
    RDret code g s0 acc
      (clipperSalesReturnBytes pos tab lot usr (UInt256.land clipperSalesUint96Mask tic) top) := by
  rcases hwf with
    ⟨hd1190, hd1191, hd1193, hd1194, hd1195, hd1196, hd1197, hd1198, hd1200,
      hd1201, hd1202, hd1203, hd1204, hd1205, hd1206, hd1207, hd1208, hd1209,
      hd1210, hd1211, hd1212, hd1213, hd1215, hd1217, hd1219, hd1220, hd1221,
      hd1222, hd1223, hd1224, hd1226, hd1227, hd1228, hd1229, hd1231, hd1233,
      hd1235, hd1236, hd1237, hd1238, hd1240, hd1241, hd1242, hd1243, hd1245,
      hd1246, hd1247, hd1248, hd1249, hd1250, hd1251, hd1252, hd1253, hd1255,
      hd1256, hd1257⟩
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  exact evm_run h with [
    raw jumpdest hd1190 (by evm_ov),
    raw push1 ⟨64⟩ hd1191 (by evm_ov),
    raw dup1 hd1193 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd1194 mem_cost hmload64 (by decide)
      (by evm_ov),
    raw swap7 hd1195 (by evm_ov),
    raw dup8 hd1196 (by evm_ov),
    raw mstore 6 (writeCascade mem [(128, pos)]) (UInt256.ofNat 5) hd1197 mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd1198 (by evm_ov),
    raw dup8 hd1200 (by evm_ov),
    raw add hd1201 (by evm_ov),
    raw swap6 hd1202 (by evm_ov),
    raw swap1 hd1203 (by evm_ov),
    raw swap6 hd1204 (by evm_ov),
    raw mstore 3 (writeCascade mem [(128, pos), (160, tab)]) (UInt256.ofNat 6)
      hd1205 mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup6 hd1206 (by evm_ov),
    raw dup6 hd1207 (by evm_ov),
    raw add hd1208 (by evm_ov),
    raw swap4 hd1209 (by evm_ov),
    raw swap1 hd1210 (by evm_ov),
    raw swap4 hd1211 (by evm_ov),
    raw mstore 3 (writeCascade mem [(128, pos), (160, tab), (192, lot)])
      (UInt256.ofNat 7) hd1212 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd1213 (by evm_ov),
    raw push1 ⟨1⟩ hd1215 (by evm_ov),
    raw push1 ⟨160⟩ hd1217 (by evm_ov),
    raw shl hd1219 (by evm_ov),
    raw sub hd1220 (by evm_ov),
    raw swap1 hd1221 (by evm_ov),
    raw swap2 hd1222 (by evm_ov),
    raw and hd1223 (by evm_ov),
    raw push1 ⟨96⟩ hd1224 (by evm_ov),
    raw dup6 hd1226 (by evm_ov),
    raw add hd1227 (by evm_ov),
    raw mstore 3
      (writeCascade mem [(128, pos), (160, tab), (192, lot),
        (224, UInt256.land usr solcAddrMask)])
      (UInt256.ofNat 8) hd1228 mem_cost
      (by rw [haddrMask]; rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd1229 (by evm_ov),
    raw push1 ⟨1⟩ hd1231 (by evm_ov),
    raw push1 ⟨96⟩ hd1233 (by evm_ov),
    raw shl hd1235 (by evm_ov),
    raw sub hd1236 (by evm_ov),
    raw and hd1237 (by evm_ov),
    raw push1 ⟨128⟩ hd1238 (by evm_ov),
    raw dup5 hd1240 (by evm_ov),
    raw add hd1241 (by evm_ov),
    raw mstore 3
      (writeCascade mem [(128, pos), (160, tab), (192, lot),
        (224, UInt256.land usr solcAddrMask), (256, UInt256.land clipperSalesUint96Mask tic)])
      (UInt256.ofNat 9) hd1242 mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 from by decide]
        simp [clipperSalesUint96Mask, Reasoning.Theory.writeCascade,
          Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw push1 ⟨160⟩ hd1243 (by evm_ov),
    raw dup4 hd1245 (by evm_ov),
    raw add hd1246 (by evm_ov),
    raw mstore 3
      (clipperSalesReturnMem mem pos tab lot usr (UInt256.land clipperSalesUint96Mask tic) top)
      (UInt256.ofNat 10) hd1247 mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨160⟩).toNat = 288 from by decide]
        simp [clipperSalesReturnMem, clipperSalesReturnWrites, Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) hd1248 mem_cost
      (clipperSalesReturnMem_mload64 pos tab lot usr
        (UInt256.land clipperSalesUint96Mask tic) top hscratch hread64)
      (by decide) (by evm_ov),
    raw swap1 hd1249 (by evm_ov),
    raw dup2 hd1250 (by evm_ov),
    raw swap1 hd1251 (by evm_ov),
    raw sub hd1252 (by evm_ov),
    raw push1 ⟨192⟩ hd1253 (by evm_ov),
    raw add hd1255 (by evm_ov),
    raw swap1 hd1256 (by evm_ov),
    raw ret 0
      (clipperSalesReturnBytes pos tab lot usr (UInt256.land clipperSalesUint96Mask tic) top)
      hd1257 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨192⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat =
            192 from by decide]
        exact clipperSalesReturnMem_read128_192 pos tab lot usr
          (UInt256.land clipperSalesUint96Mask tic) top hscratch)
      (by evm_ov)]

theorem clipperSalesReturnFromMemWfPatched (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperSalesReturnFromMemWf code := by
  unfold clipperSalesReturnFromMemWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperSalesX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1161⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := (⟨1161⟩ : UInt256))
    (ret := (⟨1190⟩ : UInt256)) (decoded := (⟨1183⟩ : UInt256))
    (need := (⟨32⟩ : UInt256)) hreach
    (by change decode code (⟨1161⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code (⟨1162⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨1190⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨1165⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨1167⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (⟨1168⟩ : UInt256) = some (.CALLDATASIZE, .none)
      clipper_decode)
    (by change decode code (⟨1169⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨1170⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨32⟩, 1))
      clipper_decode)
    (by change decode code (⟨1172⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨1173⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨1174⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨1175⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨1183⟩, 2))
      clipper_decode)
    (by change decode code (⟨1178⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (by
      change decode code (⟨1179⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨0⟩, 1))
      clipper_decode)
    (by change decode code (⟨1181⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨1182⟩ : UInt256) = some (.REVERT, .none); clipper_decode)
    hlt

theorem clipperSalesBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some salesTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨1161⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := clipperDecode_sales_none_short v (I := I) hsz4 hshort
  exact (clipperSalesX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4 hsize
    hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem clipperSalesBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 18))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 18) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some salesTransition :=
    clipperDispatch_sales v hsel
  have hreach := clipperReachSalesBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · let key : UInt256 := clipperSalesArgWord I
    let base : UInt256 := solcMappingSlot ⟨12⟩ key
    let posE : UInt256 := solcSlotWord σ_evm I base
    let tabE : UInt256 := solcSlotWord σ_evm I (base + ⟨1⟩)
    let lotE : UInt256 := solcSlotWord σ_evm I (base + ⟨2⟩)
    let packedE : UInt256 := solcSlotWord σ_evm I (base + ⟨3⟩)
    let usrE : UInt256 := UInt256.land packedE solcAddrMask
    let ticE : UInt256 := clipperSalesPackedTicWord packedE
    let topE : UInt256 := solcSlotWord σ_evm I (base + ⟨4⟩)
    obtain ⟨_, _, rd6668⟩ := clipperSalesX_decoded (v := v) (g := Sat256.ofUInt256 g)
      hpatch hsz36 hsize hreach
    obtain ⟨_, _, rd1190⟩ := RD.clipperSalesStructGetter
      (key := key) (ret := (⟨1190⟩ : UInt256)) (R := [clipperSelWord I])
      rd6668 (clipperSalesStructGetterWfPatched v hpatch)
      (clipperJumpDestBeforeFirstPatch v hpatch (⟨1190⟩ : UInt256) (by native_decide))
      (by simp)
    have hretRaw :
        RDret code (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
          (clipperSalesReturnBytes posE tabE lotE usrE
            (UInt256.land clipperSalesUint96Mask ticE) topE) := by
      simpa [key, base, posE, tabE, lotE, packedE, usrE, ticE, topE] using
        RD.clipperSalesReturnFromMem rd1190 (clipperSalesReturnFromMemWfPatched v hpatch)
          (solcMappingHashMem_mload64 ⟨12⟩ key)
          (solcMappingHashMem_size ⟨12⟩ key)
          (solcMappingHashMem_read64 ⟨12⟩ key)
          (by simp)
    have hmask160 : solcAddrMask.toNat = 2 ^ 160 - 1 := by
      native_decide
    have husrLt : usrE.toNat < EVM.twoPow 160 := by
      simpa [usrE] using u256LandMaskToNatLtOfToNat packedE solcAddrMask hmask160
    have husrClean : UInt256.land usrE solcAddrMask = usrE := by
      exact u256LandMaskCleanOfToNat usrE solcAddrMask hmask160 husrLt
    have hmask96 : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by
      native_decide
    have hticLt : ticE.toNat < EVM.twoPow 96 := by
      simpa [ticE, clipperSalesPackedTicWord, clipperSalesUint96Mask] using
        u256LandMaskToNatLtOfToNat
          (UInt256.div packedE (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
          clipperSalesUint96Mask hmask96
    have hticClean : UInt256.land clipperSalesUint96Mask ticE = ticE := by
      rw [u256_land_comm]
      exact u256LandMaskCleanOfToNat ticE clipperSalesUint96Mask hmask96 hticLt
    have hret :
        RDret code (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
          (clipperSalesReturnBytes posE tabE lotE packedE ticE topE) := by
      simpa [clipperSalesReturnBytes, usrE, husrClean, hticClean] using hretRaw
    have hdec := clipperDecode_sales_ok v (I := I) hsz36
    have hbody :
        ExecTransitionBody (config v) (contract v)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperSalesStore I) salesTransition.body
          (.returned { contract := contract v, locals := clipperSalesStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [
              .int (Int.ofNat (solcSlotWord σ_solm I base).toNat),
              .int (Int.ofNat (solcSlotWord σ_solm I (base + ⟨1⟩)).toNat),
              .int (Int.ofNat (solcSlotWord σ_solm I (base + ⟨2⟩)).toNat),
              .address (AccountAddress.ofNat
                (UInt256.land (solcSlotWord σ_solm I (base + ⟨3⟩)) solcAddrMask).toNat),
              .int (Int.ofNat
                (clipperSalesPackedTicWord (solcSlotWord σ_solm I (base + ⟨3⟩))).toNat),
              .int (Int.ofNat (solcSlotWord σ_solm I (base + ⟨4⟩)).toNat)])) := by
      simpa [key, base, clipperSalesPosSlot, clipperSalesTabSlot, clipperSalesLotSlot,
        clipperSalesPackedSlot, clipperSalesTopSlot, clipperSalesBaseSlot_eq I,
        solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        clipperSalesBodyReturns v
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hposWord : posE = solcSlotWord σ_solm I base := by
      simpa [posE] using accountMapEquiv_storage_findD hAccounts I.codeOwner base ⟨0⟩
    have htabWord : tabE = solcSlotWord σ_solm I (base + ⟨1⟩) := by
      simpa [tabE] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (base + ⟨1⟩) ⟨0⟩
    have hlotWord : lotE = solcSlotWord σ_solm I (base + ⟨2⟩) := by
      simpa [lotE] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (base + ⟨2⟩) ⟨0⟩
    have hpackedWord : packedE = solcSlotWord σ_solm I (base + ⟨3⟩) := by
      simpa [packedE] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (base + ⟨3⟩) ⟨0⟩
    have htopWord : topE = solcSlotWord σ_solm I (base + ⟨4⟩) := by
      simpa [topE] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (base + ⟨4⟩) ⟨0⟩
    have hval :
        some [
          Value.int (Int.ofNat (solcSlotWord σ_solm I base).toNat),
          Value.int (Int.ofNat (solcSlotWord σ_solm I (base + ⟨1⟩)).toNat),
          Value.int (Int.ofNat (solcSlotWord σ_solm I (base + ⟨2⟩)).toNat),
          Value.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ_solm I (base + ⟨3⟩)) solcAddrMask).toNat),
          Value.int (Int.ofNat
            (clipperSalesPackedTicWord (solcSlotWord σ_solm I (base + ⟨3⟩))).toNat),
          Value.int (Int.ofNat (solcSlotWord σ_solm I (base + ⟨4⟩)).toNat)] =
        some [
          Value.int (Int.ofNat posE.toNat), Value.int (Int.ofNat tabE.toNat),
          Value.int (Int.ofNat lotE.toNat),
          Value.address (AccountAddress.ofNat (UInt256.land packedE solcAddrMask).toNat),
          Value.int (Int.ofNat ticE.toNat), Value.int (Int.ofNat topE.toNat)] := by
      rw [← hposWord, ← htabWord, ← hlotWord, ← hpackedWord, ← htopWord]
    have henc :
        returnEquiv (clipperSalesReturnBytes posE tabE lotE packedE ticE topE)
          (some [
            Value.int (Int.ofNat posE.toNat), Value.int (Int.ofNat tabE.toNat),
            Value.int (Int.ofNat lotE.toNat),
            Value.address (AccountAddress.ofNat (UInt256.land packedE solcAddrMask).toNat),
            Value.int (Int.ofNat ticE.toNat), Value.int (Int.ofNat topE.toNat)])
          salesTransition.returnType := by
      rw [show salesTransition.returnType = [uint256, uint256, uint256, addr, uint96, uint256]
        from rfl]
      exact returnEquiv.returned rfl
        (clipperSalesReturnEncoding posE tabE lotE packedE ticE topE hticLt)
    exact hret.reEquivExecutionTransport hcode hdispatch hdec hbody hval hAccounts henc
  · exact clipperSalesBodyCoreDecodeFailed_short (v := v) hpatch hcode hsize hsz4
      (by omega) hdispatch hreach

end Benchmarks.Dss.Clipper
