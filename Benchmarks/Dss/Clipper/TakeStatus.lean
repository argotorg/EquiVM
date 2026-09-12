import Benchmarks.Dss.Clipper.Arithmetic
import Benchmarks.Dss.Clipper.GetStatusEVM
import Benchmarks.Dss.Clipper.GetStatusEVMReverts
import Benchmarks.Dss.Clipper.GetStatusReverts
import Benchmarks.Dss.Clipper.Sales
import Benchmarks.Dss.Clipper.Take

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeIdKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (clipperTakeIdWord I).toNat)

abbrev clipperTakeSalesBaseSlot (I : ExecutionEnv) : UInt256 :=
  salesBase (clipperTakeIdKey I)

theorem clipperTakeSalesBaseSlot_eq (I : ExecutionEnv) :
    clipperTakeSalesBaseSlot I = solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) := by
  unfold clipperTakeSalesBaseSlot salesBase mapSlot solcMappingSlot clipperTakeIdKey
  rw [keyValueToWord_uint256]

abbrev clipperTakeSalesPackedSlot (I : ExecutionEnv) : UInt256 :=
  clipperTakeSalesBaseSlot I + ⟨3⟩

abbrev clipperTakeSalesTabSlot (I : ExecutionEnv) : UInt256 :=
  clipperTakeSalesBaseSlot I + ⟨1⟩

abbrev clipperTakeSalesLotSlot (I : ExecutionEnv) : UInt256 :=
  clipperTakeSalesBaseSlot I + ⟨2⟩

abbrev clipperTakeSalesTopSlot (I : ExecutionEnv) : UInt256 :=
  clipperTakeSalesBaseSlot I + ⟨4⟩

abbrev clipperTakeSalesUsrWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I (clipperTakeSalesPackedSlot I)) solcAddrMask

abbrev clipperTakeSalesTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div (solcSlotWord σ I (clipperTakeSalesPackedSlot I))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)

abbrev clipperTakeSalesTicStackWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)
    (UInt256.div (solcSlotWord σ I (clipperTakeSalesPackedSlot I))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))

abbrev clipperTakeSalesTopWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperTakeSalesTopSlot I)

abbrev clipperTakeSalesTabWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperTakeSalesTabSlot I)

abbrev clipperTakeSalesLotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperTakeSalesLotSlot I)

abbrev clipperTakeSalesUsrRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperTakeIdKey I), .field "usr"] }

abbrev clipperTakeSalesTicRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperTakeIdKey I), .field "tic"] }

abbrev clipperTakeSalesTabRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperTakeIdKey I), .field "tab"] }

abbrev clipperTakeSalesLotRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperTakeIdKey I), .field "lot"] }

abbrev clipperTakeSalesTopRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperTakeIdKey I), .field "top"] }

abbrev clipperTakeSalesUsrEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperTakeSalesPackedSlot I))
    solcAddrMask

abbrev clipperTakeSalesTicEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperTakeSalesPackedSlot I))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)

abbrev clipperTakeSalesTopEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperTakeSalesTopSlot I)

abbrev clipperTakeSalesTabEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperTakeSalesTabSlot I)

abbrev clipperTakeSalesLotEVMWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperTakeSalesLotSlot I)

abbrev clipperTakeDogTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask

abbrev clipperTakeLocalsUsr (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperTakeStore I).insert "usr"
    (.address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evm I).toNat))

abbrev clipperTakeLocalsTic (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperTakeLocalsUsr evm I).insert "tic"
    (.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat))

abbrev clipperTakeLocalsSt (evm : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) : Store :=
  (clipperTakeLocalsTic evm I).insert "st"
    (.tuple [.bool done, .int (Int.ofNat price.toNat)])

abbrev clipperTakeLocalsDone (evm : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) : Store :=
  (clipperTakeLocalsSt evm I done price).insert "done" (.bool done)

abbrev clipperTakeLocalsPrice (evm : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) : Store :=
  (clipperTakeLocalsDone evm I done price).insert "price"
    (.int (Int.ofNat price.toNat))

abbrev clipperTakeLocalsLot (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) : Store :=
  (clipperTakeLocalsPrice evmLoc I done price).insert "lot"
    (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat))

abbrev clipperTakeLocalsTab (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) : Store :=
  (clipperTakeLocalsLot evmLoc evmRead I done price).insert "tab"
    (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat))

abbrev clipperTakeLocalsSlice (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice : UInt256) : Store :=
  (clipperTakeLocalsTab evmLoc evmRead I done price).insert "slice"
    (.int (Int.ofNat slice.toNat))

abbrev clipperTakeLocalsOwe0 (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 : UInt256) : Store :=
  (clipperTakeLocalsSlice evmLoc evmRead I done price slice).insert "owe0"
    (.int (Int.ofNat owe0.toNat))

abbrev clipperTakeLocalsOwe (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) : Store :=
  (clipperTakeLocalsOwe0 evmLoc evmRead I done price slice owe0).insert "owe"
    (.int (Int.ofNat owe.toNat))

abbrev clipperTakeLocalsOweTab (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) : Store :=
  (clipperTakeLocalsOwe evmLoc evmRead I done price slice owe0 owe).insert "owe"
    (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat))

abbrev clipperTakeLocalsOweTabSlice (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' : UInt256) : Store :=
  (clipperTakeLocalsOweTab evmLoc evmRead I done price slice owe0 owe).insert "slice"
    (.int (Int.ofNat slice'.toNat))

abbrev clipperTakeLocalsTabNew (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' tabNew : UInt256) : Store :=
  (clipperTakeLocalsOweTabSlice evmLoc evmRead I done price slice owe0 owe slice').insert
    "tabNew" (.int (Int.ofNat tabNew.toNat))

abbrev clipperTakeLocalsLotNew (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsTabNew evmLoc evmRead I done price slice owe0 owe slice' tabNew).insert
    "lotNew" (.int (Int.ofNat lotNew.toNat))

abbrev clipperTakeLocalsTabAssigned (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsLotNew evmLoc evmRead I done price slice owe0 owe slice' tabNew
    lotNew).insert "tab" (.int (Int.ofNat tabNew.toNat))

abbrev clipperTakeLocalsLotAssigned (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsTabAssigned evmLoc evmRead I done price slice owe0 owe slice' tabNew
    lotNew).insert "lot" (.int (Int.ofNat lotNew.toNat))

theorem clipperEvalTakeDoneFromStatusAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsSt evmLoc I done price }
      evmRead (tuple0 (.var "st")) = .ok (.bool done) := by
  simp only [tuple0, evalExpr?]
  rw [clipperTakeLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 0) = EvalResult.ok (Value.bool done)
  rfl

theorem clipperEvalTakePriceFromStatusAt (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsDone evmLoc I done price }
      evmRead (tuple1 (.var "st")) = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [tuple1, evalExpr?]
  rw [clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_self]
  change (EvalResult.ok (Value.tuple [Value.bool done, Value.int ↑price.toNat])).bind
    (fun v => tupleGetValue? v 1) = EvalResult.ok (Value.int ↑price.toNat)
  rfl

theorem clipperEvalTakeNotDone_false (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I true price }
      evmRead (.unary .not (.var "done")) = .ok (.bool false) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_self]
  rfl

theorem clipperEvalTakeNotDone_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I false price }
      evmRead (.unary .not (.var "done")) = .ok (.bool true) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_self]
  rfl

theorem clipperEvalTakeVarMaxAtPrice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I done price }
      evmRead (.var "max") = .ok (.int (Int.ofNat (clipperTakeMaxWord I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_ne _ _ (by decide),
    clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]
  rfl

theorem clipperEvalTakeVarPriceAtPrice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I done price }
      evmRead (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsPrice, store_get_self]
  rfl

theorem clipperEvalTakeVarIdAtPrice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I done price }
      evmRead (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_ne _ _ (by decide),
    clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeMaxGePrice_false (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256)
    (hmax : (clipperTakeMaxWord I).toNat < price.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I false price }
      evmRead (.binary .ge (.var "max") (.var "price")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarMaxAtPrice v evmLoc evmRead I false price,
    clipperEvalTakeVarPriceAtPrice v evmLoc evmRead I false price]
  simp [evalBinaryOp?]
  exact hmax

theorem clipperEvalTakeMaxGePrice_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price : UInt256)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I false price }
      evmRead (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarMaxAtPrice v evmLoc evmRead I false price,
    clipperEvalTakeVarPriceAtPrice v evmLoc evmRead I false price]
  simp [evalBinaryOp?]
  exact hmax

theorem clipperEvalTakeSalesLotAtPrice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I done price }
      evmRead (.storage (salesF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
  let frame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsPrice evmLoc I done price }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evmRead)
    (slot := salesF (.var "id") "lot") (er := clipperTakeSalesLotRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperTakeSalesLotSlot I))
    (value := .int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat))
    (by simp [frame, salesF, clipperTakeLocalsPrice, clipperTakeLocalsDone,
      clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
      clipperTakeStore])
    (by
      simp [frame, clipperTakeSalesLotRef, clipperTakeIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalTakeVarIdAtPrice v evmLoc evmRead I done price, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperTakeSalesLotEVMWord, clipperTakeSalesLotSlot,
      clipperTakeSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evmRead (clipperTakeSalesLotSlot I))

theorem clipperEvalTakeVarIdAtLot (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsLot evmLoc evmRead I done price }
      evmEval (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_ne _ _ (by decide),
    clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeSalesTabAfterLot (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsLot evmLoc evmRead I done price }
      evmRead (.storage (salesF (.var "id") "tab")) =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  let frame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsLot evmLoc evmRead I done price }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evmRead)
    (slot := salesF (.var "id") "tab") (er := clipperTakeSalesTabRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperTakeSalesTabSlot I))
    (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat))
    (by simp [frame, salesF, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore])
    (by
      simp [frame, clipperTakeSalesTabRef, clipperTakeIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalTakeVarIdAtLot v evmLoc evmRead evmRead I done price,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperTakeSalesTabEVMWord, clipperTakeSalesTabSlot,
      clipperTakeSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evmRead (clipperTakeSalesTabSlot I))

theorem clipperEvalTakeVarLotAtTab (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTab evmLoc evmRead I done price }
      evmEval (.var "lot") =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_self]
  rfl

theorem clipperEvalTakeVarAmtAtTab (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTab evmLoc evmRead I done price }
      evmEval (.var "amt") = .ok (clipperTakeAmtValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_ne _ _ (by decide),
    clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeMinArgsAtTab (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price : UInt256) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperTakeLocalsTab evmLoc evmRead I done price }
      evmRead [.var "lot", .var "amt"] =
      .ok [.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat),
        .int (Int.ofNat (clipperTakeAmtWord I).toNat)] := by
  exact clipperEvalExprsUintBinary v evmRead
    (clipperTakeLocalsTab evmLoc evmRead I done price)
    (clipperTakeSalesLotEVMWord evmRead I) (clipperTakeAmtWord I)
    (clipperEvalTakeVarLotAtTab v evmLoc evmRead evmRead I done price)
    (by simpa [clipperTakeAmtValue] using
      clipperEvalTakeVarAmtAtTab v evmLoc evmRead evmRead I done price)

theorem clipperEvalTakeVarSliceAtSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsSlice evmLoc evmRead I done price slice }
      evmEval (.var "slice") = .ok (.int (Int.ofNat slice.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsSlice, store_get_self]
  rfl

theorem clipperEvalTakeVarPriceAtSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsSlice evmLoc evmRead I done price slice }
      evmEval (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_self]
  rfl

theorem clipperEvalTakeOwe0Mul_revert (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hover : UInt256.size ≤ slice.toNat * price.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsSlice evmLoc evmRead I false price slice }
      evmRead (mul256 (.var "slice") (.var "price")) = .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarSliceAtSlice v evmLoc evmRead evmRead I false price slice,
    clipperEvalTakeVarPriceAtSlice v evmLoc evmRead evmRead I false price slice,
    evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem clipperEvalTakeOwe0Mul_ok (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsSlice evmLoc evmRead I false price slice }
      evmRead (mul256 (.var "slice") (.var "price")) =
        .ok (.int (Int.ofNat (UInt256.mul slice price).toNat)) := by
  have hlt : ¬Int.ofNat (slice.toNat * price.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hmul))
  have hword : (UInt256.mul slice price).toNat = slice.toNat * price.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt hmul]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarSliceAtSlice v evmLoc evmRead evmRead I false price slice,
    clipperEvalTakeVarPriceAtSlice v evmLoc evmRead evmRead I false price slice,
    evalBinaryOp?, uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem clipperEvalTakeVarPriceAtOwe0 (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe0 evmLoc evmRead I done price slice owe0 }
      evmEval (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_self]
  rfl

theorem clipperEvalTakeVarSliceAtOwe0 (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe0 evmLoc evmRead I done price slice owe0 }
      evmEval (.var "slice") = .ok (.int (Int.ofNat slice.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_self]
  rfl

theorem clipperEvalTakeVarOwe0AtOwe0 (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe0 evmLoc evmRead I done price slice owe0 }
      evmEval (.var "owe0") = .ok (.int (Int.ofNat owe0.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOwe0, store_get_self]
  rfl

theorem clipperEvalTakeVarOweAtOwe (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I done price slice owe0 owe }
      evmEval (.var "owe") = .ok (.int (Int.ofNat owe.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOwe, store_get_self]
  rfl

theorem clipperEvalTakeVarTabAtOwe (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I done price slice owe0 owe }
      evmEval (.var "tab") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_self]
  rfl

theorem clipperEvalTakeVarLotAtOwe (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I done price slice owe0 owe }
      evmEval (.var "lot") =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_self]
  rfl

theorem clipperEvalTakeVarSliceAtOwe (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I done price slice owe0 owe }
      evmEval (.var "slice") =
      .ok (.int (Int.ofNat slice.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_self]
  rfl

theorem clipperEvalTakeOweGtTab_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hgt : (clipperTakeSalesTabEVMWord evmRead I).toNat < owe.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead (.binary .gt (.var "owe") (.var "tab")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarOweAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
    clipperEvalTakeVarTabAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe]
  simp [evalBinaryOp?]
  exact hgt

theorem clipperEvalTakeOweGtTab_false (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hle : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead (.binary .gt (.var "owe") (.var "tab")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarOweAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
    clipperEvalTakeVarTabAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe]
  simp [evalBinaryOp?]
  omega

theorem clipperEvalTakeOweLtTab_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hlt : owe.toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead (.binary .lt (.var "owe") (.var "tab")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarOweAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
    clipperEvalTakeVarTabAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe]
  simp [evalBinaryOp?]
  exact hlt

theorem clipperEvalTakeOweLtTab_false (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hge : (clipperTakeSalesTabEVMWord evmRead I).toNat ≤ owe.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead (.binary .lt (.var "owe") (.var "tab")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarOweAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
    clipperEvalTakeVarTabAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe]
  simp [evalBinaryOp?]
  omega

theorem clipperEvalTakeSliceLtLot_false (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hsliceGe : (clipperTakeSalesLotEVMWord evmRead I).toNat ≤ slice.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead (.binary .lt (.var "slice") (.var "lot")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarSliceAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
    clipperEvalTakeVarLotAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe]
  simp [evalBinaryOp?]
  omega

theorem clipperEvalTakeNoChostCond_false_left (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hge : (clipperTakeSalesTabEVMWord evmRead I).toNat ≤ owe.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead
        (.binary .and (.binary .lt (.var "owe") (.var "tab"))
          (.binary .lt (.var "slice") (.var "lot"))) =
      .ok (.bool false) := by
  have hleft :=
    clipperEvalTakeOweLtTab_false v evmLoc evmRead I price slice owe0 owe hge
  simp [evalExpr?, hleft, EvalResult.bind, bind, pure]

theorem clipperEvalTakeNoChostCond_false_right (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hlt : owe.toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceGe : (clipperTakeSalesLotEVMWord evmRead I).toNat ≤ slice.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead
        (.binary .and (.binary .lt (.var "owe") (.var "tab"))
          (.binary .lt (.var "slice") (.var "lot"))) =
      .ok (.bool false) := by
  have hleft :=
    clipperEvalTakeOweLtTab_true v evmLoc evmRead I price slice owe0 owe hlt
  have hright :=
    clipperEvalTakeSliceLtLot_false v evmLoc evmRead I price slice owe0 owe hsliceGe
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem clipperTakeAssignOweToTab (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256) :
    ExecStmt (config v)
      (Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe))
      evmRead (.assign .localVar (varRef "owe") (.var "tab"))
      (.ok
        (Frame.mk (contract v) (clipperTakeLocalsOweTab evmLoc evmRead I false price slice owe0 owe))
        evmRead) := by
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe)
  let oweTabFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOweTab evmLoc evmRead I false price slice owe0 owe)
  have hrhs :
      evalExpr? (config v) oweFrame evmRead (.var "tab") =
        .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simpa [oweFrame] using
      clipperEvalTakeVarTabAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe
  have hassign :
      assignStorageRef? (config v) oweFrame evmRead .localVar (varRef "owe")
        (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) =
      .ok (oweTabFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, oweFrame, oweTabFrame,
      clipperTakeLocalsOweTab, clipperTakeLocalsOwe, pure, bind, EvalResult.bind]
  simpa [oweFrame, oweTabFrame] using ExecStmt.assign hrhs hassign

theorem clipperEvalTakeVarOweAtOweTab (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTab evmLoc evmRead I done price slice owe0 owe }
      evmEval (.var "owe") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOweTab, store_get_self]
  rfl

theorem clipperEvalTakeVarPriceAtOweTab (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTab evmLoc evmRead I done price slice owe0 owe }
      evmEval (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_self]
  rfl

theorem clipperEvalTakeOweDivPriceAtOweTab (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hprice : price ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTab evmLoc evmRead I false price slice owe0 owe }
      evmRead (.binary .div (.var "owe") (.var "price")) =
      .ok (.int (Int.ofNat (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)) := by
  have hpriceNat : ¬price.toNat = 0 := by
    intro hzero
    exact hprice (uint256_toNat_eq_zero hzero)
  have hdiv :
      Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat / Int.ofNat price.toNat =
        Int.ofNat (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat := by
    rw [udiv_toNat]
    exact Int.ofNat_ediv_ofNat
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    clipperEvalTakeVarOweAtOweTab v evmLoc evmRead evmRead I false price slice owe0 owe,
    clipperEvalTakeVarPriceAtOweTab v evmLoc evmRead evmRead I false price slice owe0 owe,
    hpriceNat]
  exact hdiv

theorem clipperTakeAssignSliceFromOweTab (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 : UInt256)
    (hprice : price ≠ ⟨0⟩) :
    ExecStmt (config v)
        (Frame.mk (contract v) (clipperTakeLocalsOweTab evmLoc evmRead I false price slice owe0
          (UInt256.mul slice price)))
      evmRead (.assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")))
      (.ok
        (Frame.mk (contract v) (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0
          (UInt256.mul slice price)
          (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price)))
        evmRead) := by
  let oweTabFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOweTab evmLoc evmRead I false price slice owe0
      (UInt256.mul slice price))
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0
      (UInt256.mul slice price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price))
  have hrhs :
      evalExpr? (config v) oweTabFrame evmRead
        (.binary .div (.var "owe") (.var "price")) =
      .ok (.int (Int.ofNat
        (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)) := by
    simpa [oweTabFrame] using
      clipperEvalTakeOweDivPriceAtOweTab v evmLoc evmRead I price slice owe0
        (UInt256.mul slice price) hprice
  have hassign :
      assignStorageRef? (config v) oweTabFrame evmRead .localVar (varRef "slice")
        (.int (Int.ofNat
          (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)) =
      .ok (sliceFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, oweTabFrame, sliceFrame,
      clipperTakeLocalsOweTabSlice, pure, bind, EvalResult.bind]
  simpa [oweTabFrame, sliceFrame] using ExecStmt.assign hrhs hassign

theorem clipperEvalTakeVarTabAtOweTabSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTabSlice evmLoc evmRead I done price slice owe0 owe
          slice' }
      evmEval (.var "tab") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_self]
  rfl

theorem clipperEvalTakeVarOweAtOweTabSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTabSlice evmLoc evmRead I done price slice owe0 owe
          slice' }
      evmEval (.var "owe") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTab, store_get_self]
  rfl

theorem clipperEvalTakeVarLotAtOweTabSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTabSlice evmLoc evmRead I done price slice owe0 owe
          slice' }
      evmEval (.var "lot") =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_self]
  rfl

theorem clipperEvalTakeVarSliceAtOweTabSlice (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (done : Bool) (price slice owe0 owe slice' : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTabSlice evmLoc evmRead I done price slice owe0 owe
          slice' }
      evmEval (.var "slice") = .ok (.int (Int.ofNat slice'.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOweTabSlice, store_get_self]
  rfl

theorem clipperEvalTakeTabSubOweAtOweTabSlice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe
          slice' }
      evmRead (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
        (clipperTakeSalesTabEVMWord evmRead I)).toNat)) := by
  have hsub :
      UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
          (clipperTakeSalesTabEVMWord evmRead I) = ⟨0⟩ := by
    exact u256_sub_self (clipperTakeSalesTabEVMWord evmRead I)
  have hzero :
      Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
          Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat = 0 := by
    omega
  have hmod : (0 : Int) % wordModulus = 0 := by
    norm_num [wordModulus]
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  simp [wrap256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarTabAtOweTabSlice v evmLoc evmRead evmRead I false price slice owe0
      owe slice',
    clipperEvalTakeVarOweAtOweTabSlice v evmLoc evmRead evmRead I false price slice owe0
      owe slice',
    evalBinaryOp?, hsub, hmod, hwordNonzero]

theorem clipperEvalTakeLotSubSliceAtOweTabSlice (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' : UInt256)
    (hsliceLot : slice'.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe
          slice' }
      evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesLotEVMWord evmRead I)
        slice').toNat)) := by
  let lot := clipperTakeSalesLotEVMWord evmRead I
  have hsubNat : (UInt256.sub lot slice').toNat = lot.toNat - slice'.toNat := by
    exact usub_toNat hsliceLot
  have hdiff :
      Int.ofNat lot.toNat - Int.ofNat slice'.toNat =
        Int.ofNat (lot.toNat - slice'.toNat) := by
    exact (Int.ofNat_sub hsliceLot).symm
  have hltNat : lot.toNat - slice'.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le lot.toNat slice'.toNat) lot.val.isLt
  have hlt : Int.ofNat (lot.toNat - slice'.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (lot.toNat - slice'.toNat) % wordModulus =
        Int.ofNat (lot.toNat - slice'.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
          Int.ofNat slice'.toNat) % wordModulus =
        Int.ofNat ((clipperTakeSalesLotEVMWord evmRead I).toNat - slice'.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
        Int.ofNat slice'.toNat = Int.ofNat (lot.toNat - slice'.toNat) by
      simpa [lot] using hdiff]
    simpa [lot] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarLotAtOweTabSlice v evmLoc evmRead evmRead I false price slice owe0
      owe slice',
    clipperEvalTakeVarSliceAtOweTabSlice v evmLoc evmRead evmRead I false price slice owe0
      owe slice',
    evalBinaryOp?, hsubNat, hwordNonzero, lot]
  exact hmodLoad

theorem clipperTakeLetTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' : UInt256) :
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
      (clipperTakeSalesTabEVMWord evmRead I)
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe slice'))
      evmRead
      (.letDecl "tabNew" (some uint256) (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe slice'
            tabNew))
        evmRead) := by
  intro tabNew
  let sliceFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe slice')
  let tabNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe slice' tabNew)
  have hrhs :
      evalExpr? (config v) sliceFrame evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [sliceFrame, tabNew] using
      clipperEvalTakeTabSubOweAtOweTabSlice v evmLoc evmRead I price slice owe0 owe
        slice'
  simpa [sliceFrame, tabNewFrame, clipperTakeLocalsTabNew] using
    (ExecStmt.letDecl
      (cfg := config v) (solm := sliceFrame) (evm := evmRead) (name := "tabNew")
      (ty := some uint256) (expr := wrap256 (.binary .sub (.var "tab") (.var "owe")))
      (value := .int (Int.ofNat tabNew.toNat)) hrhs)

theorem clipperEvalTakeLotSubSliceAtTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew : UInt256)
    (hsliceLot : slice'.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe slice'
          tabNew }
      evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesLotEVMWord evmRead I)
        slice').toNat)) := by
  have hlot :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe
            slice' tabNew }
        evmRead (.var "lot") =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_self]
    rfl
  have hslice :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe
            slice' tabNew }
        evmRead (.var "slice") = .ok (.int (Int.ofNat slice'.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_self]
    rfl
  let lot := clipperTakeSalesLotEVMWord evmRead I
  have hsubNat : (UInt256.sub lot slice').toNat = lot.toNat - slice'.toNat := by
    exact usub_toNat hsliceLot
  have hdiff :
      Int.ofNat lot.toNat - Int.ofNat slice'.toNat =
        Int.ofNat (lot.toNat - slice'.toNat) := by
    exact (Int.ofNat_sub hsliceLot).symm
  have hltNat : lot.toNat - slice'.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le lot.toNat slice'.toNat) lot.val.isLt
  have hlt : Int.ofNat (lot.toNat - slice'.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (lot.toNat - slice'.toNat) % wordModulus =
        Int.ofNat (lot.toNat - slice'.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
          Int.ofNat slice'.toNat) % wordModulus =
        Int.ofNat ((clipperTakeSalesLotEVMWord evmRead I).toNat - slice'.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
        Int.ofNat slice'.toNat = Int.ofNat (lot.toNat - slice'.toNat) by
      simpa [lot] using hdiff]
    simpa [lot] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind, hlot, hslice, evalBinaryOp?, hsubNat,
    hwordNonzero, lot]
  exact hmodLoad

theorem clipperTakeLetLotNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew : UInt256)
    (hsliceLot : slice'.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe slice'
          tabNew))
      evmRead
      (.letDecl "lotNew" (some uint256)
        (wrap256 (.binary .sub (.var "lot") (.var "slice"))))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsLotNew evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead) := by
  intro lotNew
  let tabNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe slice' tabNew)
  let lotNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsLotNew evmLoc evmRead I false price slice owe0 owe slice' tabNew
        lotNew)
  have hrhs :
      evalExpr? (config v) tabNewFrame evmRead
        (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [tabNewFrame, lotNew] using
      clipperEvalTakeLotSubSliceAtTabNew v evmLoc evmRead I price slice owe0 owe slice'
        tabNew hsliceLot
  simpa [tabNewFrame, lotNewFrame, clipperTakeLocalsLotNew] using
    (ExecStmt.letDecl
      (cfg := config v) (solm := tabNewFrame) (evm := evmRead) (name := "lotNew")
      (ty := some uint256)
      (expr := wrap256 (.binary .sub (.var "lot") (.var "slice")))
      (value := .int (Int.ofNat lotNew.toNat)) hrhs)

theorem clipperTakeAssignTabFromTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsLotNew evmLoc evmRead I false price slice owe0 owe slice' tabNew
          lotNew))
      evmRead (.assign .localVar (varRef "tab") (.var "tabNew"))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsTabAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead) := by
  let lotNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsLotNew evmLoc evmRead I false price slice owe0 owe slice' tabNew
        lotNew)
  let tabFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsTabAssigned evmLoc evmRead I false price slice owe0 owe slice'
        tabNew lotNew)
  have hrhs :
      evalExpr? (config v) lotNewFrame evmRead (.var "tabNew") =
      .ok (.int (Int.ofNat tabNew.toNat)) := by
    change evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsLotNew evmLoc evmRead I false price slice owe0 owe slice'
          tabNew lotNew }
      evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat))
    simp only [evalExpr?]
    rw [clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_self]
    rfl
  have hassign :
      assignStorageRef? (config v) lotNewFrame evmRead .localVar (varRef "tab")
        (.int (Int.ofNat tabNew.toNat)) = .ok (tabFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, lotNewFrame, tabFrame,
      clipperTakeLocalsTabAssigned, pure, bind, EvalResult.bind]
  simpa [lotNewFrame, tabFrame] using ExecStmt.assign hrhs hassign

theorem clipperTakeAssignLotFromLotNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsTabAssigned evmLoc evmRead I false price slice owe0 owe slice'
          tabNew lotNew))
      evmRead (.assign .localVar (varRef "lot") (.var "lotNew"))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead) := by
  let tabFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsTabAssigned evmLoc evmRead I false price slice owe0 owe slice'
        tabNew lotNew)
  let lotFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
        tabNew lotNew)
  have hrhs :
      evalExpr? (config v) tabFrame evmRead (.var "lotNew") =
      .ok (.int (Int.ofNat lotNew.toNat)) := by
    change evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsTabAssigned evmLoc evmRead I false price slice owe0 owe
          slice' tabNew lotNew }
      evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat))
    simp only [evalExpr?]
    rw [clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_self]
    rfl
  have hassign :
      assignStorageRef? (config v) tabFrame evmRead .localVar (varRef "lot")
        (.int (Int.ofNat lotNew.toNat)) = .ok (lotFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, tabFrame, lotFrame,
      clipperTakeLocalsLotAssigned, pure, bind, EvalResult.bind]
  simpa [tabFrame, lotFrame] using ExecStmt.assign hrhs hassign

theorem clipperEvalTakeCheckedOwe0Require_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOwe0 evmLoc evmRead I false price slice (UInt256.mul slice price) }
      evmRead
      (.binary .or
        (.binary .eq (.var "price") (.intLit 0))
        (.binary .eq (.binary .div (.var "owe0") (.var "price")) (.var "slice"))) =
      .ok (.bool true) := by
  by_cases hprice : price = ⟨0⟩
  · subst price
    simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
      clipperEvalTakeVarPriceAtOwe0 v evmLoc evmRead evmRead I false ⟨0⟩ slice
        (UInt256.mul slice ⟨0⟩)]
  · have hdiv :
        Int.ofNat (UInt256.mul slice price).toNat / Int.ofNat price.toNat =
          Int.ofNat slice.toNat := by
      have hcancel := Reasoning.Theory.clipperMulDiv_cancel (x := price) (y := slice)
        hprice (by simpa [Nat.mul_comm] using hmul)
      have hnat := congrArg UInt256.toNat hcancel
      rw [udiv_toNat, u256_mul_comm price slice] at hnat
      exact (Int.ofNat_ediv_ofNat (a := (UInt256.mul slice price).toNat)
        (b := price.toNat)).trans (congrArg Int.ofNat hnat)
    have hpriceNat : ¬price.toNat = 0 := by
      intro hzero
      exact hprice (uint256_toNat_eq_zero hzero)
    have hleft :
        evalExpr? (config v)
          { contract := contract v,
            locals := clipperTakeLocalsOwe0 evmLoc evmRead I false price slice
              (UInt256.mul slice price) }
          evmRead (.binary .eq (.var "price") (.intLit 0)) = .ok (.bool false) := by
      simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
        clipperEvalTakeVarPriceAtOwe0 v evmLoc evmRead evmRead I false price slice
          (UInt256.mul slice price), hpriceNat]
    have hright :
        evalExpr? (config v)
          { contract := contract v,
            locals := clipperTakeLocalsOwe0 evmLoc evmRead I false price slice
              (UInt256.mul slice price) }
          evmRead
          (.binary .eq (.binary .div (.var "owe0") (.var "price")) (.var "slice")) =
          .ok (.bool true) := by
      simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
        clipperEvalTakeVarOwe0AtOwe0 v evmLoc evmRead evmRead I false price slice
          (UInt256.mul slice price),
        clipperEvalTakeVarPriceAtOwe0 v evmLoc evmRead evmRead I false price slice
          (UInt256.mul slice price),
        clipperEvalTakeVarSliceAtOwe0 v evmLoc evmRead evmRead I false price slice
          (UInt256.mul slice price), hpriceNat]
      exact hdiv
    simp [evalExpr?, EvalResult.bind, bind, pure, hleft, hright]

theorem clipperTakePostLotWord_eq {σ τ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ)
    (hacc : evm.accountMap = τ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    solcSlotWord σ I (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩) =
      clipperTakeSalesLotEVMWord evm I := by
  have hslot :=
    accountMapEquiv_storage_findD (σ := σ) (τ := τ)
      hAccounts I.codeOwner (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩)
      (⟨0⟩ : UInt256)
  simpa [clipperTakeSalesLotEVMWord, clipperTakeSalesLotSlot,
    clipperTakeSalesBaseSlot_eq I, solcSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, hacc, howner] using hslot

theorem clipperTakePostTabWord_eq {σ τ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ)
    (hacc : evm.accountMap = τ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    solcSlotWord σ I (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨1⟩) =
      clipperTakeSalesTabEVMWord evm I := by
  have hslot :=
    accountMapEquiv_storage_findD (σ := σ) (τ := τ)
      hAccounts I.codeOwner (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨1⟩)
      (⟨0⟩ : UInt256)
  simpa [clipperTakeSalesTabEVMWord, clipperTakeSalesTabSlot,
    clipperTakeSalesBaseSlot_eq I, solcSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, hacc, howner] using hslot

noncomputable abbrev clipperTakeSalesHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperTakeIdWord I) ⟨12⟩ solcFreePtrMem

noncomputable abbrev clipperTakeSalesTopHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperTakeIdWord I) ⟨12⟩ (clipperTakeSalesHashMem I)

theorem clipperTakeSalesHashMem_size (I : ExecutionEnv) :
    (clipperTakeSalesHashMem I).size = 96 := by
  simpa [clipperTakeSalesHashMem] using
    twoWordHashMem_size_96 (clipperTakeIdWord I) ⟨12⟩ solcFreePtrMem_size

theorem clipperTakeSalesHashMem_read64 (I : ExecutionEnv) :
    (clipperTakeSalesHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [clipperTakeSalesHashMem, twoWordHashMem_read64 _ _ solcFreePtrMem_size]
  exact solcFreePtrMem_read64

theorem clipperTakeSalesTopHashMem_size (I : ExecutionEnv) :
    (clipperTakeSalesTopHashMem I).size = 96 := by
  simpa [clipperTakeSalesTopHashMem] using
    twoWordHashMem_size_96 (clipperTakeIdWord I) ⟨12⟩ (clipperTakeSalesHashMem_size I)

theorem clipperTakeSalesTopHashMem_read64 (I : ExecutionEnv) :
    (clipperTakeSalesTopHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [clipperTakeSalesTopHashMem, twoWordHashMem_read64 _ _ (clipperTakeSalesHashMem_size I)]
  exact clipperTakeSalesHashMem_read64 I

theorem clipperEvalTakeVarId (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := clipperTakeStore I } evm
      (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?, clipperTakeStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeSalesUsr (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeStore I } evm
      (.storage (salesF (.var "id") "usr")) =
      .ok (.address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperTakeStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "usr") (er := clipperTakeSalesUsrRef I)
    (t := .address) (loc := addrLoc (clipperTakeSalesPackedSlot I))
    (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evm I).toNat))
    (by simp [frame, salesF, clipperTakeStore])
    (by
      simp only [frame, clipperTakeSalesUsrRef, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, pure, bind]
      rw [clipperEvalTakeVarId v evm I]
      simp [clipperTakeIdKey, valueToKey?, EvalResult.ofOption, pure])
    (by simp [frame, clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, addrSt])
    (by rfl)
    (by simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesPackedSlot,
      clipperTakeSalesBaseSlot] using
      clipperStorageLocLoad_address evm (clipperTakeSalesPackedSlot I))

theorem clipperEvalTakeVarIdAfterUsr (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsUsr evmLoc I }
      evmRead (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeSalesTicAfterUsr (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsUsr evm I } evm
      (.storage (salesF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "tic") (er := clipperTakeSalesTicRef I)
    (t := .int uint96Int)
    (loc := uint96Loc (clipperTakeSalesPackedSlot I) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat))
    (by simp [frame, salesF, clipperTakeLocalsUsr, clipperTakeStore])
    (by
      simp [frame, clipperTakeSalesTicRef, clipperTakeIdValue, clipperTakeIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalTakeVarIdAfterUsr v evm evm I, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint96St])
    (by rfl)
    (by simpa [clipperTakeSalesTicEVMWord, clipperTakeSalesPackedSlot,
      clipperTakeSalesBaseSlot] using
      clipperStorageLocLoad_uint96 evm (clipperTakeSalesPackedSlot I))

theorem clipperEvalTakeZeroAddr (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    pure, bind]

theorem clipperEvalTakeVarUsrAfterTic (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.var "usr") =
      .ok (.address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evm I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_self]
  rfl

theorem clipperEvalTakeUsrNeZeroAfterTic_false (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (husr : clipperTakeSalesUsrEVMWord evm I = ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.binary .ne (.var "usr") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, clipperEvalTakeVarUsrAfterTic, clipperEvalTakeZeroAddr,
    EvalResult.bind, bind]
  rw [husr]
  native_decide

theorem clipperTakeMaskedAddress_ne_zero {w : UInt256}
    (h : UInt256.land w solcAddrMask ≠ ⟨0⟩) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  have hval : (UInt256.land w solcAddrMask).toNat = 0 := by
    have hlt : (UInt256.land w solcAddrMask).toNat < AccountAddress.size := by
      rw [u256_land_toNat]
      have hland : Nat.land w.toNat solcAddrMask.toNat ≤ solcAddrMask.toNat :=
        Nat.and_le_right
      have hmask : solcAddrMask.toNat < AccountAddress.size := by
        native_decide
      have hlandlt : Nat.land w.toNat solcAddrMask.toNat < UInt256.size := by
        have hsize : AccountAddress.size < UInt256.size := by decide
        omega
      rw [Nat.mod_eq_of_lt hlandlt]
      omega
    apply congrArg Fin.val at haddr
    simpa [AccountAddress.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hlt] using haddr
  exact h (u256_inj (by simpa using hval))

theorem clipperEvalTakeUsrNeZeroAfterTic_true (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (husr : clipperTakeSalesUsrEVMWord evm I ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.binary .ne (.var "usr") zeroAddr) = .ok (.bool true) := by
  simp only [evalExpr?, clipperEvalTakeVarUsrAfterTic, clipperEvalTakeZeroAddr,
    EvalResult.bind, bind]
  have haddr : AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evm I).toNat ≠
      AccountAddress.ofNat 0 := by
    simpa [clipperTakeSalesUsrEVMWord] using
      clipperTakeMaskedAddress_ne_zero
        (w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperTakeSalesPackedSlot I))
        (by simpa [clipperTakeSalesUsrEVMWord] using husr)
  simp [evalBinaryOp?, haddr]

theorem clipperEvalTakeVarIdAfterTic (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeVarTicAfterTic (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.var "tic") =
      .ok (.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsTic, store_get_self]
  rfl

theorem clipperEvalTakeSalesTopAfterTic (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.storage (salesF (.var "id") "top")) =
      .ok (.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "top") (er := clipperTakeSalesTopRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperTakeSalesTopSlot I))
    (value := .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat))
    (by simp [frame, salesF, clipperTakeLocalsTic, clipperTakeLocalsUsr,
      clipperTakeStore])
    (by
      simp [frame, clipperTakeSalesTopRef, clipperTakeIdKey, salesF,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        clipperEvalTakeVarIdAfterTic v evm I, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperTakeSalesTopEVMWord, clipperTakeSalesTopSlot,
      clipperTakeSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperTakeSalesTopSlot I))

theorem clipperEvalTakeStatusArgs (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      [.var "tic", .storage (salesF (.var "id") "top")] =
      .ok [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
        .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)] := by
  simp only [evalExprs?, clipperEvalTakeVarTicAfterTic,
    clipperEvalTakeSalesTopAfterTic, EvalResult.bind, bind, pure]

theorem clipperTakeStatusCallRevertsAgeForPrice (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (clipperTimestampWord evm).toNat < (clipperTakeSalesTicEVMWord evm I).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperEvalTakeStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsAgeForPrice v evm
      (clipperTakeSalesTicEVMWord evm I) (clipperTakeSalesTopEVMWord evm I) hlt)

theorem clipperTakeStatusCallReturnsDoneTailTrue (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (clipperStatusTailWord evmPrice).toNat <
        (UInt256.sub (clipperTimestampWord evmPrice) (clipperTakeSalesTicEVMWord evm I)).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      (.ok { contract := contract v, locals := clipperTakeLocalsSt evm I true price }
        evmPrice) := by
  simpa [resumeAfterInternalCall, clipperTakeLocalsSt] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
      (evm := evm) (calleeEvm := evmPrice)
      (name := "status") (retVar := "st")
      (args := [.var "tic", .storage (salesF (.var "id") "top")])
      (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
        .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
      (callee := statusFunction)
      (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
        (clipperTakeSalesTopEVMWord evm I))
      (calleeSolm :=
        { contract := contract v,
          locals := clipperStatusDoneTrueLocals (clipperTakeSalesTicEVMWord evm I)
            (clipperTakeSalesTopEVMWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I))
            price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperTakeSalesTicEVMWord evm I)) })
      (value := some [.bool true, .int (Int.ofNat price.toNat)])
      (clipperEvalTakeStatusArgs v evm I)
      (clipperLookupStatusFunction v)
      (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
        (clipperTakeSalesTopEVMWord evm I))
      (clipperStatusFunctionReturnsDoneTailTrue v (clipperTakeSalesTicEVMWord evm I)
        (clipperTakeSalesTopEVMWord evm I) price hlePrice hcode hcall hdec hleDone htail))

theorem clipperTakeStatusCallReturnsRdivBranch (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperTakeSalesTicEVMWord evm I).toNat ≤
      (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperTakeSalesTicEVMWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperTakeSalesTopEVMWord evm I ≠ ⟨0⟩) (done : Bool)
    (hdone :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperStatusRatioLocals (clipperTakeSalesTicEVMWord evm I)
            (clipperTakeSalesTopEVMWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)) price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperTakeSalesTicEVMWord evm I))
            (UInt256.div (UInt256.mul price clipperRayWord) (clipperTakeSalesTopEVMWord evm I)) }
        evmPrice (.binary .lt (.var "ratio") (.storage cuspRef)) = .ok (.bool done)) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      (.ok { contract := contract v, locals := clipperTakeLocalsSt evm I done price }
        evmPrice) := by
  simpa [resumeAfterInternalCall, clipperTakeLocalsSt] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
      (evm := evm) (calleeEvm := evmPrice)
      (name := "status") (retVar := "st")
      (args := [.var "tic", .storage (salesF (.var "id") "top")])
      (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
        .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
      (callee := statusFunction)
      (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
        (clipperTakeSalesTopEVMWord evm I))
      (calleeSolm :=
        { contract := contract v,
          locals := clipperStatusDoneFromRatioLocals (clipperTakeSalesTicEVMWord evm I)
            (clipperTakeSalesTopEVMWord evm I)
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I))
            price
            (UInt256.sub (clipperTimestampWord evmPrice) (clipperTakeSalesTicEVMWord evm I))
            (UInt256.div (UInt256.mul price clipperRayWord)
              (clipperTakeSalesTopEVMWord evm I))
            done })
      (value := some [.bool done, .int (Int.ofNat price.toNat)])
      (clipperEvalTakeStatusArgs v evm I)
      (clipperLookupStatusFunction v)
      (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
        (clipperTakeSalesTopEVMWord evm I))
      (clipperStatusFunctionReturnsRdivBranch v (clipperTakeSalesTicEVMWord evm I)
        (clipperTakeSalesTopEVMWord evm I) price hlePrice hcode hcall hdec hleDone htail
        hmul htop done hdone))

theorem clipperTakeStatusCallRevertsPriceNoCode (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperEvalTakeStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsPriceNoCode v evm
      (clipperTakeSalesTicEVMWord evm I) (clipperTakeSalesTopEVMWord evm I)
      hlePrice hnoCode)

theorem clipperTakeStatusCallRevertsPriceCallFailure (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)).toNat)]
        (false, evmPrice, out) false) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperEvalTakeStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsPriceCallFailure v
      (clipperTakeSalesTicEVMWord evm I) (clipperTakeSalesTopEVMWord evm I)
      hlePrice hcode hcall)

theorem clipperTakeStatusCallRevertsPriceDecode (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out = none) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperEvalTakeStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsPriceDecode v
      (clipperTakeSalesTicEVMWord evm I) (clipperTakeSalesTopEVMWord evm I)
      hlePrice hcode hcall hdec)

theorem clipperTakeStatusCallRevertsAgeForDone (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256)
    {out : ByteArray}
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hltDone : (clipperTimestampWord evmPrice).toNat <
      (clipperTakeSalesTicEVMWord evm I).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperEvalTakeStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsAgeForDone v
      (clipperTakeSalesTicEVMWord evm I) (clipperTakeSalesTopEVMWord evm I) price
      hlePrice hcode hcall hdec hltDone)

theorem clipperTakeStatusCallRevertsRdivMul (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256)
    {out : ByteArray}
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperTakeSalesTicEVMWord evm I).toNat ≤
      (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperTakeSalesTicEVMWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hover : UInt256.size ≤ price.toNat * clipperRayWord.toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperEvalTakeStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsRdivMul v
      (clipperTakeSalesTicEVMWord evm I) (clipperTakeSalesTopEVMWord evm I) price
      hlePrice hcode hcall hdec hleDone htail hover)

theorem clipperTakeStatusCallRevertsRdivDivZero (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256)
    {out : ByteArray}
    (hlePrice : (clipperTakeSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperTakeSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperTakeSalesTicEVMWord evm I).toNat ≤
      (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperTakeSalesTicEVMWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperTakeSalesTopEVMWord evm I = ⟨0⟩) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperTakeLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperTakeLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperTakeSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperTakeSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperEvalTakeStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperTakeSalesTicEVMWord evm I)
      (clipperTakeSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsRdivDivZero v
      (clipperTakeSalesTicEVMWord evm I) (clipperTakeSalesTopEVMWord evm I) price
      hlePrice hcode hcall hdec hleDone htail hmul htop)

end Benchmarks.Dss.Clipper
