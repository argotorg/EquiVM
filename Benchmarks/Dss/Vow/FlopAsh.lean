import Benchmarks.Dss.Vow.FlopDai

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flop()` ash update after the second `vat.dai(address(this))` call -/

abbrev flopLocalsVatSinFreeSinDebtDaiAshNew
    (vatSin freeSin flopDebt vatDai AshNew : UInt256) : Store :=
  (flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai).insert "AshNew"
    (.int (Int.ofNat AshNew.toNat))

theorem flopLocalsVatSinFreeSinDebtDaiAshNew_get_AshNew
    (vatSin freeSin flopDebt vatDai AshNew : UInt256) :
    (flopLocalsVatSinFreeSinDebtDaiAshNew vatSin freeSin flopDebt vatDai AshNew).get?
      "AshNew" = some (.int (Int.ofNat AshNew.toNat)) := by
  rw [flopLocalsVatSinFreeSinDebtDaiAshNew, store_get_self]

abbrev flopLocalsVatSinFreeSinDebtDaiAshNewId
    (vatSin freeSin flopDebt vatDai AshNew id : UInt256) : Store :=
  (flopLocalsVatSinFreeSinDebtDaiAshNew vatSin freeSin flopDebt vatDai AshNew).insert "id"
    (.int (Int.ofNat id.toNat))

theorem flopLocalsVatSinFreeSinDebtDaiAshNewId_get_id
    (vatSin freeSin flopDebt vatDai AshNew id : UInt256) :
    (flopLocalsVatSinFreeSinDebtDaiAshNewId vatSin freeSin flopDebt vatDai AshNew id).get?
      "id" = some (.int (Int.ofNat id.toNat)) := by
  rw [flopLocalsVatSinFreeSinDebtDaiAshNewId, store_get_self]

def flopFlopperAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      solcAddrMask).toNat

theorem evalExpr_flopFlopperStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "flopper" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage flopperRef) =
      .ok (.address (flopFlopperAddressOf evm)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "flopper", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨3⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_address_offset0 evm ⟨3⟩)
  · exact hbase
  · simp [flopperRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

abbrev flopDumpEvaledRef : EvaledStorageRef :=
  { base := "dump", steps := [] }

theorem evalExpr_flopDumpStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "dump" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage dumpRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := flopDumpEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨8⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨8⟩)
  · exact hbase
  · simp [flopDumpEvaledRef, dumpRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, flopDumpEvaledRef]

-- LIBRARY CANDIDATE: generic source-side checked external-call code guard.
theorem evalExpr_extCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

-- LIBRARY CANDIDATE: generic source-side checked external-call code guard.
theorem evalExpr_extCodeGuard_false {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

-- LIBRARY CANDIDATE: sequential composition for an `ExecBlock` prefix that falls through.
theorem execBlock_append_ok {cfg : Config} {solm evm solm' evm' result}
    {xs ys : List Stmt}
    (hxs : ExecBlock cfg solm evm xs (.ok solm' evm'))
    (hys : ExecBlock cfg solm' evm' ys result) :
    ExecBlock cfg solm evm (xs ++ ys) result := by
  induction xs generalizing solm evm with
  | nil =>
      cases hxs
      simpa using hys
  | cons stmt xs ih =>
      cases hxs with
      | consNormal hstmt hrest =>
          simpa using ExecBlock.consNormal hstmt (ih hrest)

def flopAshAssignStmts : List Stmt :=
  [ .internalCall "add" [.storage AshRef, .storage sumpRef] "AshNew",
    .assign .storage AshRef (.var "AshNew") ]

def flopKickAndReturnStmts : List Stmt :=
  checkedExternalCallStmts (.storage flopperRef) "kick" (.intLit 0)
    [thisAddr, .storage dumpRef, .storage sumpRef] "id" ++
  [ .return [.var "id"] ]

abbrev flopKickSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨771388233⟩ ⟨226⟩

abbrev flopKickSelectorWord : UInt256 :=
  ⟨3085552932⟩

abbrev flopKickOutPtr : UInt256 := ⟨128⟩

abbrev flopKickInSize : UInt256 := ⟨100⟩

abbrev flopKickOutSize : UInt256 := ⟨32⟩

abbrev flopKickEndPtr : UInt256 := ⟨228⟩

noncomputable def flopKickSelectorMem (mem : ByteArray) : ByteArray :=
  flopKickSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def flopKickAddressMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 (flopKickSelectorMem mem) 132 32

noncomputable def flopKickDumpMem (I : ExecutionEnv) (dump : UInt256)
    (mem : ByteArray) : ByteArray :=
  dump.toByteArray.write 0 (flopKickAddressMem I mem) 164 32

noncomputable def flopKickCalldataMem (I : ExecutionEnv) (dump sump : UInt256)
    (mem : ByteArray) : ByteArray :=
  sump.toByteArray.write 0 (flopKickDumpMem I dump mem) 196 32

theorem flopKickSelectorMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (flopKickSelectorMem mem).size = 164 := by
  unfold flopKickSelectorMem
  exact toByteArray_write32_size_of_le mem flopKickSelectorShifted 128 164 164 hmem
    (by rw [hmem]; omega) (by omega)

theorem flopKickAddressMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (flopKickAddressMem I mem).size = 164 := by
  unfold flopKickAddressMem
  exact toByteArray_write32_size_of_le (flopKickSelectorMem mem)
    (UInt256.ofNat I.codeOwner.val) 132 164 164
    (flopKickSelectorMem_size hmem)
    (by rw [flopKickSelectorMem_size hmem]; omega) (by omega)

theorem flopKickDumpMem_size (I : ExecutionEnv) (dump : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (flopKickDumpMem I dump mem).size = 196 := by
  unfold flopKickDumpMem
  exact toByteArray_write32_size_of_le (flopKickAddressMem I mem) dump 164 164 196
    (flopKickAddressMem_size I hmem)
    (by rw [flopKickAddressMem_size I hmem]) (by omega)

theorem flopKickCalldataMem_size (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flopKickCalldataMem I dump sump mem).size = 228 := by
  unfold flopKickCalldataMem
  exact toByteArray_write32_size_of_le (flopKickDumpMem I dump mem) sump 196 196 228
    (flopKickDumpMem_size I dump hmem)
    (by rw [flopKickDumpMem_size I dump hmem]) (by omega)

theorem flopKickSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flopKickSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flopKickSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega), hread64]

theorem flopKickAddressMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flopKickAddressMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flopKickAddressMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [flopKickSelectorMem_size hmem]; omega) (by omega),
    flopKickSelectorMem_read64 hmem hread64]

theorem flopKickDumpMem_read64 (I : ExecutionEnv) (dump : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flopKickDumpMem I dump mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flopKickDumpMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [flopKickAddressMem_size I hmem]) (by omega),
    flopKickAddressMem_read64 I hmem hread64]

theorem flopKickCalldataMem_read64 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flopKickCalldataMem I dump sump mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold flopKickCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [flopKickDumpMem_size I dump hmem]) (by omega),
    flopKickDumpMem_read64 I dump hmem hread64]

theorem flopKickCalldataMem_read128_4 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flopKickCalldataMem I dump sump mem).readWithPadding 128 4 =
      flopKickSelector := by
  have hDumpSize := flopKickDumpMem_size I dump hmem
  have hAddressSize := flopKickAddressMem_size I hmem
  have hSelectorSize := flopKickSelectorMem_size hmem
  unfold flopKickCalldataMem
  rw [toByteArray_write_read_below_len_of_gap sump (flopKickDumpMem I dump mem) 196 128 4
      (by
        rw [hDumpSize]
        omega)
      (by omega) (by omega) (by omega)
      (by
        rw [hDumpSize]
        native_decide)]
  unfold flopKickDumpMem
  rw [toByteArray_write_read_below_len_of_gap dump (flopKickAddressMem I mem) 164 128 4
      (by
        rw [hAddressSize]
        omega)
      (by omega) (by omega) (by omega)
      (by
        rw [hAddressSize]
        native_decide)]
  unfold flopKickAddressMem
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val)
      (flopKickSelectorMem mem) 132 128 4
      (by
        rw [hSelectorSize]
        omega)
      (by omega) (by omega) (by omega)
      (by
        rw [hSelectorSize]
        native_decide)]
  unfold flopKickSelectorMem
  rw [toByteArray_write_read_window_of_gap flopKickSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega)
      (by
        rw [hmem]
        native_decide)]
  native_decide

theorem flopKickCalldataMem_read132_32 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flopKickCalldataMem I dump sump mem).readWithPadding 132 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  have hDumpSize := flopKickDumpMem_size I dump hmem
  have hAddressSize := flopKickAddressMem_size I hmem
  have hSelectorSize := flopKickSelectorMem_size hmem
  unfold flopKickCalldataMem
  rw [toByteArray_write_read_below_len_of_gap sump (flopKickDumpMem I dump mem) 196 132 32
      (by
        rw [hDumpSize]
        omega)
      (by omega) (by omega) (by omega)
      (by
        rw [hDumpSize]
        native_decide)]
  unfold flopKickDumpMem
  rw [toByteArray_write_read_below_len_of_gap dump (flopKickAddressMem I mem) 164 132 32
      (by rw [hAddressSize])
      (by omega) (by omega) (by omega)
      (by
        rw [hAddressSize]
        native_decide)]
  unfold flopKickAddressMem
  rw [toByteArray_write_read_back_of_gap (UInt256.ofNat I.codeOwner.val)
      (flopKickSelectorMem mem) 132
      (by
        rw [hSelectorSize]
        native_decide)]

theorem flopKickCalldataMem_read164_32 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flopKickCalldataMem I dump sump mem).readWithPadding 164 32 =
      dump.toByteArray := by
  have hDumpSize := flopKickDumpMem_size I dump hmem
  have hAddressSize := flopKickAddressMem_size I hmem
  unfold flopKickCalldataMem
  rw [toByteArray_write_read_below_len_of_gap sump (flopKickDumpMem I dump mem) 196 164 32
      (by rw [hDumpSize])
      (by omega) (by omega) (by omega)
      (by
        rw [hDumpSize]
        native_decide)]
  unfold flopKickDumpMem
  rw [toByteArray_write_read_back_of_gap dump (flopKickAddressMem I mem) 164
      (by
        rw [hAddressSize]
        native_decide)]

theorem flopKickCalldataMem_read196_32 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flopKickCalldataMem I dump sump mem).readWithPadding 196 32 =
      sump.toByteArray := by
  have hDumpSize := flopKickDumpMem_size I dump hmem
  unfold flopKickCalldataMem
  rw [toByteArray_write_read_back_of_gap sump (flopKickDumpMem I dump mem) 196
      (by
        rw [hDumpSize]
        native_decide)]

theorem flopKickCalldataMem_read128_100 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flopKickCalldataMem I dump sump mem).readWithPadding 128 100 =
      flopKickSelector ++ (UInt256.ofNat I.codeOwner.val).toByteArray ++
        dump.toByteArray ++ sump.toByteArray := by
  have hsize : (flopKickCalldataMem I dump sump mem).size = 228 :=
    flopKickCalldataMem_size I dump sump hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (flopKickCalldataMem I dump sump mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (flopKickCalldataMem I dump sump mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (flopKickCalldataMem I dump sump mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize])]
  rw [flopKickCalldataMem_read128_4 I dump sump hmem,
    flopKickCalldataMem_read132_32 I dump sump hmem,
    flopKickCalldataMem_read164_32 I dump sump hmem,
    flopKickCalldataMem_read196_32 I dump sump hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem flopKickEncode_eq (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "kick"
        [.address I.codeOwner, .int (Int.ofNat dump.toNat), .int (Int.ofNat sump.toNat)] =
      some ((flopKickCalldataMem I dump sump mem).readWithPadding
        flopKickOutPtr.toNat flopKickInSize.toNat) := by
  change config.externalABI.encode? "kick"
      [.address I.codeOwner, .int (Int.ofNat dump.toNat), .int (Int.ofNat sump.toNat)] =
    some ((flopKickCalldataMem I dump sump mem).readWithPadding 128 100)
  rw [flopKickCalldataMem_read128_100 I dump sump hmem]
  have hdumpLt : dump.toNat < EVM.twoPow 256 := dump.val.isLt
  have hsumpLt : sump.toNat < EVM.twoPow 256 := sump.val.isLt
  have hdumpWord : EVM.word dump.toNat = dump := by
    show UInt256.ofNat dump.toNat = dump
    exact u256_ofNat_toNat _
  have hsumpWord : EVM.word sump.toNat = sump := by
    show UInt256.ofNat sump.toNat = sump
    exact u256_ofNat_toNat _
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, flopKickSelector, selectorBytes, hdumpLt, hsumpLt,
    hdumpWord, hsumpWord]
  rw [show EVM.word (↑I.codeOwner : ℕ) = UInt256.ofNat (↑I.codeOwner : ℕ) from rfl]
  apply ByteArray.ext
  simp [word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.data_append, Array.append_assoc]

theorem flopAshAddAssignSuccess
    {evmDai : EVM.State}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew : UInt256}
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ = AshValDai)
    (hSumpLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ = SumpValDai)
    (hAshNew : AshNew = AshValDai + SumpValDai)
    (hfit : AshValDai.toNat + SumpValDai.toNat < UInt256.size) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    let locals5 := flopLocalsVatSinFreeSinDebtDaiAshNew vatSin freeSin flopDebt vatDai AshNew
    let evmAsh := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew
    ExecBlock config { contract := contract, locals := locals4 } evmDai
      [ .internalCall "add" [.storage AshRef, .storage sumpRef] "AshNew",
        .assign .storage AshRef (.var "AshNew") ]
      (.ok { contract := contract, locals := locals5 } evmAsh) := by
  intro locals4 locals5 evmAsh
  have hAshDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.storage AshRef) =
        .ok (.int (Int.ofNat AshValDai.toNat)) := by
    simpa [locals4, hAshLoadDai] using
      evalExpr_kissAshStorage (evm := evmDai) (locals := locals4)
        (by simp [locals4, flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hSumpDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.storage sumpRef) =
        .ok (.int (Int.ofNat SumpValDai.toNat)) := by
    simpa [locals4, hSumpLoadDai] using
      evalExpr_flopSumpStorage (evm := evmDai) (locals := locals4)
        (by simp [locals4, flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hargsAdd :
      evalExprs? config { contract := contract, locals := locals4 } evmDai
        [.storage AshRef, .storage sumpRef] =
          .ok [.int (Int.ofNat AshValDai.toNat), .int (Int.ofNat SumpValDai.toNat)] := by
    simp [evalExprs?, hAshDai, hSumpDai, EvalResult.bind, bind, pure]
  have hbindAdd :
      bindParams? addFunction.params
          [.int (Int.ofNat AshValDai.toNat), .int (Int.ofNat SumpValDai.toNat)] =
        some (uintBinaryLocals AshValDai SumpValDai) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := locals4 } evmDai
        (.internalCall "add" [.storage AshRef, .storage sumpRef] "AshNew")
        (.ok { contract := contract, locals := locals5 } evmDai) := by
    have hbody := execAddFunctionReturn (evm := evmDai) (x := AshValDai)
      (y := SumpValDai) (sum := AshNew) hAshNew hfit
    simpa [locals4, locals5, flopLocalsVatSinFreeSinDebtDaiAshNew,
      resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals4 })
        (evm := evmDai) (calleeEvm := evmDai) (name := "add") (retVar := "AshNew")
        (args := [.storage AshRef, .storage sumpRef])
        (argVals := [.int (Int.ofNat AshValDai.toNat), .int (Int.ofNat SumpValDai.toNat)])
        (callee := addFunction) (locals := uintBinaryLocals AshValDai SumpValDai)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ AshValDai SumpValDai AshNew })
        (value := some [.int (Int.ofNat AshNew.toNat)]) hargsAdd (by rfl) hbindAdd hbody)
  have hAshNewVar :
      evalExpr? config { contract := contract, locals := locals5 } evmDai (.var "AshNew") =
        .ok (.int (Int.ofNat AshNew.toNat)) := by
    simpa [locals5] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flopLocalsVatSinFreeSinDebtDaiAshNew vatSin freeSin flopDebt vatDai AshNew)
        (name := "AshNew") (value := AshNew)
        (flopLocalsVatSinFreeSinDebtDaiAshNew_get_AshNew
          vatSin freeSin flopDebt vatDai AshNew)
  have hassignAsh :
      assignStorageRef? config { contract := contract, locals := locals5 } evmDai
        .storage AshRef (.int (Int.ofNat AshNew.toNat)) =
          .ok ({ contract := contract, locals := locals5 }, evmAsh) := by
    simpa [evmAsh, locals5] using
      assign_kissAshStorage evmDai (locals := locals5) AshNew
        (by simp [locals5, flopLocalsVatSinFreeSinDebtDaiAshNew,
          flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  refine ExecBlock.consNormal haddStmt ?_
  exact ExecBlock.consNormal (ExecStmt.assign hAshNewVar hassignAsh) ExecBlock.nil

theorem flopAshAssignThenKickSuccess
    {evmDai evmKick : EVM.State}
    {outKick : ByteArray}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew DumpVal SumpVal id : UInt256}
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ = AshValDai)
    (hSumpLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ = SumpValDai)
    (hAshNew : AshNew = AshValDai + SumpValDai)
    (hfit : AshValDai.toNat + SumpValDai.toNat < UInt256.size)
    (hDumpLoadAsh :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).executionEnv.codeOwner
        ⟨8⟩ = DumpVal)
    (hSumpLoadAsh :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).executionEnv.codeOwner
        ⟨9⟩ = SumpVal)
    (hflopperCode :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (flopFlopperAddressOf
            (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew))).option
          0 (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
        (EVM.address
          (flopFlopperAddressOf
            (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)))
        "kick" 0
        [.address
          (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).executionEnv.codeOwner,
          .int (Int.ofNat DumpVal.toNat), .int (Int.ofNat SumpVal.toNat)]
        (true, evmKick, outKick) true)
    (hdecKick :
      config.externalABI.decode? "kick" outKick =
        some [.int (Int.ofNat id.toNat)]) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    let locals6 := flopLocalsVatSinFreeSinDebtDaiAshNewId vatSin freeSin flopDebt vatDai AshNew id
    ExecBlock config { contract := contract, locals := locals4 } evmDai
      (flopAshAssignStmts ++ flopKickAndReturnStmts)
      (.returned { contract := contract, locals := locals6 } evmKick
        (some [.int (Int.ofNat id.toNat)])) := by
  intro locals4 locals6
  let locals5 := flopLocalsVatSinFreeSinDebtDaiAshNew vatSin freeSin flopDebt vatDai AshNew
  let evmAsh := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew
  have hDumpLoadAsh' :
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨8⟩ = DumpVal := by
    simpa [evmAsh] using hDumpLoadAsh
  have hSumpLoadAsh' :
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨9⟩ = SumpVal := by
    simpa [evmAsh] using hSumpLoadAsh
  have hflopperCode' :
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (flopFlopperAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [evmAsh] using hflopperCode
  have hcallKick' :
      typedCallViaEVM config evmAsh (EVM.address (flopFlopperAddressOf evmAsh))
        "kick" 0
        [.address evmAsh.executionEnv.codeOwner, .int (Int.ofNat DumpVal.toNat),
          .int (Int.ofNat SumpVal.toNat)]
        (true, evmKick, outKick) true := by
    simpa [evmAsh] using hcallKick
  have hassignBlock :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flopAshAssignStmts (.ok { contract := contract, locals := locals5 } evmAsh) := by
    simpa [flopAshAssignStmts, locals4, locals5, evmAsh] using
      flopAshAddAssignSuccess (evmDai := evmDai) (vatSin := vatSin)
        (freeSin := freeSin) (flopDebt := flopDebt) (vatDai := vatDai)
        (AshValDai := AshValDai) (SumpValDai := SumpValDai) (AshNew := AshNew)
        hAshLoadDai hSumpLoadDai hAshNew hfit
  have hflopper :
      evalExpr? config { contract := contract, locals := locals5 } evmAsh (.storage flopperRef) =
        .ok (.address (flopFlopperAddressOf evmAsh)) := by
    simpa [locals5, flopLocalsVatSinFreeSinDebtDaiAshNew,
      flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
      flopLocalsVatSinFreeSin, flopLocalsVatSin] using
      evalExpr_flopFlopperStorage (evm := evmAsh) (locals := locals5)
        (by simp [locals5, flopLocalsVatSinFreeSinDebtDaiAshNew,
          flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hguard :
      evalExpr? config { contract := contract, locals := locals5 } evmAsh
        (.binary .gt (.extCodeSize (.storage flopperRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_extCodeGuard_true hflopper hflopperCode'
  have hthis :
      evalExpr? config { contract := contract, locals := locals5 } evmAsh thisAddr =
        .ok (.address evmAsh.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hdump :
      evalExpr? config { contract := contract, locals := locals5 } evmAsh (.storage dumpRef) =
        .ok (.int (Int.ofNat DumpVal.toNat)) := by
    simpa [hDumpLoadAsh'] using
      evalExpr_flopDumpStorage (evm := evmAsh) (locals := locals5)
        (by simp [locals5, flopLocalsVatSinFreeSinDebtDaiAshNew,
          flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hsump :
      evalExpr? config { contract := contract, locals := locals5 } evmAsh (.storage sumpRef) =
        .ok (.int (Int.ofNat SumpVal.toNat)) := by
    simpa [hSumpLoadAsh'] using
      evalExpr_flopSumpStorage (evm := evmAsh) (locals := locals5)
        (by simp [locals5, flopLocalsVatSinFreeSinDebtDaiAshNew,
          flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hargsKick :
      evalExprs? config { contract := contract, locals := locals5 } evmAsh
        [thisAddr, .storage dumpRef, .storage sumpRef] =
          .ok [.address evmAsh.executionEnv.codeOwner,
            .int (Int.ofNat DumpVal.toNat), .int (Int.ofNat SumpVal.toNat)] := by
    simp [evalExprs?, hthis, hdump, hsump, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals5 } evmAsh
        (.externalCall (.storage flopperRef) "kick" (.intLit 0)
          [thisAddr, .storage dumpRef, .storage sumpRef] "id")
        (.ok { contract := contract, locals := locals6 } evmKick) := by
    simpa [locals6, flopLocalsVatSinFreeSinDebtDaiAshNewId, collapseReturns] using
      ExecStmt.externalCallSuccess hflopper (by simp [evalExpr?, pure])
        hargsKick hcallKick' hdecKick
  have hid :
      evalExpr? config { contract := contract, locals := locals6 } evmKick (.var "id") =
        .ok (.int (Int.ofNat id.toNat)) := by
    simpa [locals6] using
      evalExpr_varUInt256 (evm := evmKick)
        (locals := flopLocalsVatSinFreeSinDebtDaiAshNewId
          vatSin freeSin flopDebt vatDai AshNew id)
        (name := "id") (value := id)
        (flopLocalsVatSinFreeSinDebtDaiAshNewId_get_id
          vatSin freeSin flopDebt vatDai AshNew id)
  have hkickBlock :
      ExecBlock config { contract := contract, locals := locals5 } evmAsh
        flopKickAndReturnStmts
        (.returned { contract := contract, locals := locals6 } evmKick
          (some [.int (Int.ofNat id.toNat)])) := by
    simp only [flopKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hid))
  exact execBlock_append_ok hassignBlock hkickBlock

theorem vowFlopSourceAshAddOverflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal vatDai AshValDai SumpValDai : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : flopDebt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hSumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpVal)
    (henough : SumpVal.toNat ≤ flopDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ I)) "dai" 0
        [.address I.codeOwner] (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiZero : vatDai = ⟨0⟩)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ = AshValDai)
    (hSumpLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ = SumpValDai)
    (hover : UInt256.size ≤ AshValDai.toNat + SumpValDai.toNat) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  let locals1 := flopLocalsVatSin vatSin
  let locals2 := flopLocalsVatSinFreeSin vatSin freeSin
  let locals3 := flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt
  let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmSin) := by
    simpa [locals, locals1, flopLocalsVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsSin hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmSin) (locals := flopLocalsVatSin vatSin)
        (name := "vatSin") (value := vatSin) (flopLocalsVatSin_get_vatSin vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals1, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals1)
        (by simp [locals1, flopLocalsVatSin])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals1 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals1, locals2, flopLocalsVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals1 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flopLocalsVatSinFreeSin vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (flopLocalsVatSinFreeSin_get_freeSin vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals2, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "flopDebt")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := freeSin) (y := AshVal)
      (diff := flopDebt) hdebt hdebtOk
    simpa [locals2, locals3, flopLocalsVatSinFreeSinDebt, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "flopDebt")
        (args := [.var "freeSin", .storage AshRef])
        (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ freeSin AshVal flopDebt })
        (value := some [.int (Int.ofNat flopDebt.toNat)]) hargsDebt (by rfl) hbindDebt hbody)
  have hsump :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage sumpRef) =
        .ok (.int (Int.ofNat SumpVal.toNat)) := by
    simpa [locals3, hSumpLoad] using
      evalExpr_flopSumpStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, flopLocalsVatSinFreeSinDebt, flopLocalsVatSinFreeSin,
          flopLocalsVatSin])
  have hflopDebt :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.var "flopDebt") =
        .ok (.int (Int.ofNat flopDebt.toNat)) := by
    simpa [locals3] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt)
        (name := "flopDebt") (value := flopDebt)
        (flopLocalsVatSinFreeSinDebt_get_flopDebt vatSin freeSin flopDebt)
  have hreqDebt :
      evalExpr? config { contract := contract, locals := locals3 } evmSin
        (.binary .le (.storage sumpRef) (.var "flopDebt")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hsump hflopDebt henough
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals3, kissVatAddress, vowAddressReturnWord, hvatLoadSin] using
      evalExpr_kissVatStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, flopLocalsVatSinFreeSinDebt, flopLocalsVatSinFreeSin,
          flopLocalsVatSin])
  have hguardDai :
      evalExpr? config { contract := contract, locals := locals3 } evmSin
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatDai hvatCodeDai
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals3 } evmSin [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvSin : evmSin.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallSin
    simpa [locals3, henvSin, evm0, initState] using evalExprs_kissThis evmSin locals3
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals3 } evmSin
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals3, locals4, flopLocalsVatSinFreeSinDebtDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvatDai (by simp [evalExpr?, pure])
        hargsDai hcallDai hdecDai
  have hvatDaiVar :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.var "vatDai") =
        .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai)
        (name := "vatDai") (value := vatDai)
        (flopLocalsVatSinFreeSinDebtDai_get_vatDai vatSin freeSin flopDebt vatDai)
  have hreqVatDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) := by
    have hzeroNat : vatDai.toNat = 0 := by
      rw [hvatDaiZero]
      rfl
    simp [evalExpr?, EvalResult.bind, bind, hvatDaiVar, evalBinaryOp?, hzeroNat]
  have hAshDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.storage AshRef) =
        .ok (.int (Int.ofNat AshValDai.toNat)) := by
    simpa [locals4, hAshLoadDai] using
      evalExpr_kissAshStorage (evm := evmDai) (locals := locals4)
        (by simp [locals4, flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hSumpDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.storage sumpRef) =
        .ok (.int (Int.ofNat SumpValDai.toNat)) := by
    simpa [locals4, hSumpLoadDai] using
      evalExpr_flopSumpStorage (evm := evmDai) (locals := locals4)
        (by simp [locals4, flopLocalsVatSinFreeSinDebtDai, flopLocalsVatSinFreeSinDebt,
          flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hargsAdd :
      evalExprs? config { contract := contract, locals := locals4 } evmDai
        [.storage AshRef, .storage sumpRef] =
          .ok [.int (Int.ofNat AshValDai.toNat), .int (Int.ofNat SumpValDai.toNat)] := by
    simp [evalExprs?, hAshDai, hSumpDai, EvalResult.bind, bind, pure]
  have hbindAdd :
      bindParams? addFunction.params
          [.int (Int.ofNat AshValDai.toNat), .int (Int.ofNat SumpValDai.toNat)] =
        some (uintBinaryLocals AshValDai SumpValDai) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := locals4 } evmDai
        (.internalCall "add" [.storage AshRef, .storage sumpRef] "AshNew") .reverted := by
    have hbody := execAddFunctionRevert (evm := evmDai) (x := AshValDai)
      (y := SumpValDai) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals4 })
      (evm := evmDai) (name := "add") (retVar := "AshNew")
      (args := [.storage AshRef, .storage sumpRef])
      (argVals := [.int (Int.ofNat AshValDai.toNat), .int (Int.ofNat SumpValDai.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals AshValDai SumpValDai)
      hargsAdd (by rfl) hbindAdd hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    refine ExecBlock.consNormal hdebtStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDebt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDai) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqVatDai) ?_
    exact ExecBlock.consRevert haddStmt
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopAshAddOverflowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal AshValDai SumpValDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai : EVM.State} {mem outSin outDai : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd3832 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outDai.write 0 (vatDaiCalldataMem I mem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
      (UInt256.ofNat 6) outDai acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ outDai.size)
    (hosz : outDai.size < UInt256.size)
    (hvatDai :
      vatDai = UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32)))
    (hvatDaiZero : vatDai = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : flopDebt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hSumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpVal)
    (henough : SumpVal.toNat ≤ flopDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ_solm I)) "dai" 0
        [.address I.codeOwner] (true, evmDai, outDai) false)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ = AshValDai)
    (hSumpLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ = SumpValDai)
    (hAshEvm : AshValDai = vowSlotWord ⟨6⟩ acc.2 I)
    (hSumpEvm : SumpValDai = vowSlotWord ⟨9⟩ acc.2 I)
    (hover : UInt256.size ≤ AshValDai.toNat + SumpValDai.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd3832' := rd3832
  rw [hmin] at rd3832'
  obtain ⟨_, _, rd3850⟩ :=
    RD.vowFlopDai1CallSuccessToDecode rd3832' (by simp)
  have hmemWrite : (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size =
      164 :=
    vatDaiWrite_size I outDai 32 hmem (by omega) ho32
  have hread64Write :
      (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    vatDaiWrite_read64 I outDai 32 hmem hread64 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 (vatDaiCalldataMem I mem) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
            (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 (vatDaiCalldataMem I mem) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥
              (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmemWrite]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      vatDaiWrite_read128_32 I outDai hmem ho32]
  obtain ⟨_, _, rd3873⟩ :=
    RD.vowFlopDai1ReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32)))
      rd3850 ho32 hosz hmload64 hmload128
  have hoverEvm :
      UInt256.size ≤
        (vowSlotWord ⟨6⟩ acc.2 I).toNat + (vowSlotWord ⟨9⟩ acc.2 I).toNat := by
    simpa [← hAshEvm, ← hSumpEvm] using hover
  have hrev := RD.vowFlopAshAddOverflow (vatDai := vatDai)
    (by simpa [hvatDai] using rd3873)
    hvatDaiZero hoverEvm
  have hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)] := by
    simpa [hvatDai] using kissDaiDecode_ok (o := outDai) ho32
  have hbody := vowFlopSourceAshAddOverflow (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpVal := SumpVal) (vatDai := vatDai)
    (AshValDai := AshValDai) (SumpValDai := SumpValDai)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai hvatDaiZero
    hAshLoadDai hSumpLoadDai hover
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem RD.vowFlopAshAddSuccess
    {cA gh bl σ σ₀ A I} {g sel vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3873⟩
      (vatDai :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hvatDaiZero : vatDai = ⟨0⟩)
    (hfit :
      (vowSlotWord ⟨6⟩ acc.2 I).toNat + (vowSlotWord ⟨9⟩ acc.2 I).toNat <
        UInt256.size) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
      ((vowSlotWord ⟨6⟩ acc.2 I + vowSlotWord ⟨9⟩ acc.2 I) ::
        ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let AshVal := vowSlotWord ⟨6⟩ acc.2 I
  let SumpVal := vowSlotWord ⟨9⟩ acc.2 I
  have rd3874₀ := rd.iszero (by native_decide) (by evm_ov)
  have rd3874 := rd3874₀
  rw [hvatDaiZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3874
  have rd3877 := rd3874.push2 ⟨3945⟩ (by native_decide) (by evm_ov)
  have rd3945 := rd3877.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd3946 := rd3945.jumpdest (by native_decide) (by evm_ov)
  have rd3949 := rd3946.push2 ⟨3959⟩ (by native_decide) (by evm_ov)
  have rd3951 := rd3949.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3952, C3952, rd3952Raw⟩ := rd3951.sload (by native_decide) (by evm_ov)
  have rd3952 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3952⟩
      (AshVal :: ⟨3959⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k3952 C3952 := by
    simpa [AshVal, vowSlotWord, solcSlotWord] using rd3952Raw
  have rd3954 := rd3952.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3955, C3955, rd3955Raw⟩ := rd3954.sload (by native_decide) (by evm_ov)
  have rd3955 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3955⟩
      (SumpVal :: AshVal :: ⟨3959⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k3955 C3955 := by
    simpa [SumpVal, vowSlotWord, solcSlotWord] using rd3955Raw
  have rd3958 := rd3955.push2 ⟨5074⟩ (by native_decide) (by evm_ov)
  have rd5074 := rd3958.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k', C', rd3959⟩ :=
    RD.solcCheckedAddSuccess
      (pc := ⟨5074⟩) (okPc := ⟨5090⟩) (a := AshVal) (b := SumpVal)
      (ret := ⟨3959⟩) (R := [⟨0⟩, ⟨357⟩, sel])
      (by simpa [AshVal, SumpVal] using rd5074)
      (by
        unfold solcCheckedAddSuccessWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [AshVal, SumpVal] using hfit)
      (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k', C', by simpa [AshVal, SumpVal] using rd3959⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowFlopToKickExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel AshNew : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
      (AshNew :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
    let target := vowAddressReturnWord ⟨3⟩ σAsh I
    let dump := vowSlotWord ⟨8⟩ σAsh I
    let sump := vowSlotWord ⟨9⟩ σAsh I
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4048⟩
      (target :: target :: ⟨0⟩ :: flopKickOutPtr :: flopKickInSize ::
        flopKickOutPtr :: flopKickOutSize :: flopKickEndPtr ::
        flopKickSelectorWord :: target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (flopKickCalldataMem I dump sump mem)
      (UInt256.ofNat 8) o (acc.1, σAsh) k' C' := by
  intro σAsh target dump sump
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hKickMem : (flopKickCalldataMem I dump sump mem).size = 228 := by
    simpa [dump, sump] using flopKickCalldataMem_size I dump sump hmem
  have hKickRead64 :
      (flopKickCalldataMem I dump sump mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    simpa [dump, sump] using flopKickCalldataMem_read64 I dump sump hmem hread64
  have hmload64Kick :
      (if (⟨64⟩ : UInt256).toNat ≥ (flopKickCalldataMem I dump sump mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((flopKickCalldataMem I dump sump mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hKickMem]; decide) (by decide) hKickRead64
  have rd3960 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd3962 := rd3960.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3963, C3963, rd3963Raw⟩ :=
    rd3962.sstore hperm (by native_decide) (by evm_ov)
  have rd3963 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3963⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (acc.1, σAsh) k3963 C3963 := by
    simpa [σAsh] using rd3963Raw
  have rd3965 := rd3963.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3966, C3966, rd3966Raw⟩ := rd3965.sload (by native_decide) (by evm_ov)
  have rd3966 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3966⟩
      (vowSlotWord ⟨3⟩ σAsh I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (acc.1, σAsh) k3966 C3966 := by
    simpa [σAsh, vowSlotWord, solcSlotWord] using rd3966Raw
  have rd3968 := rd3966.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3969, C3969, rd3969Raw⟩ := rd3968.sload (by native_decide) (by evm_ov)
  have rd3969 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3969⟩
      (dump :: vowSlotWord ⟨3⟩ σAsh I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (acc.1, σAsh) k3969 C3969 := by
    simpa [dump, σAsh, vowSlotWord, solcSlotWord] using rd3969Raw
  have rd3971 := rd3969.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3972, C3972, rd3972Raw⟩ := rd3971.sload (by native_decide) (by evm_ov)
  have rd3972 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3972⟩
      (sump :: dump :: vowSlotWord ⟨3⟩ σAsh I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (acc.1, σAsh) k3972 C3972 := by
    simpa [sump, σAsh, vowSlotWord, solcSlotWord] using rd3972Raw
  have rd4048 := evm_run rd3972 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨771388233⟩,
    push1 ⟨226⟩,
    shl,
    dup2,
    raw mstore 0 (flopKickSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    uniswapAddress,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (flopKickAddressMem I mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩,
    dup2,
    add,
    swap4,
    swap1,
    swap4,
    raw mstore 3 (flopKickDumpMem I dump mem) (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩,
    dup4,
    add,
    swap2,
    swap1,
    swap2,
    raw mstore 3 (flopKickCalldataMem I dump sump mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Kick (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap2,
    push4 flopKickSelectorWord,
    swap2,
    push1 flopKickInSize,
    dup1,
    dup3,
    add,
    swap3,
    push1 flopKickOutSize,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    push1 ⟨0⟩,
    dup8,
    dup1]
  have hpc4048 :
      (⟨3972⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ =
        ⟨4048⟩ := by
    native_decide
  rw [hpc4048] at rd4048
  exact ⟨_, _, by
    simpa [target, dump, sump, σAsh, flopKickSelectorShifted, flopKickSelectorWord,
      flopKickSelectorMem, flopKickAddressMem, flopKickDumpMem, flopKickCalldataMem,
      flopKickOutPtr, flopKickInSize, flopKickOutSize, flopKickEndPtr,
      vowAddressReturnWord, vowSlotWord, solcSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd4048⟩

theorem flopKickAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨3⟩ σ I).toNat) =
      AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simp [EVM.twoPow, AccountAddress.size])

theorem RD.vowFlopKickNoCode
    {cA gh bl σ σ₀ A I} {g sel AshNew : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
      (AshNew :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
      Reasoning.Theory.uniswapExtCodeSizeWord σAsh
        (vowAddressReturnWord ⟨3⟩ σAsh I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
  let target := vowAddressReturnWord ⟨3⟩ σAsh I
  let dump := vowSlotWord ⟨8⟩ σAsh I
  let sump := vowSlotWord ⟨9⟩ σAsh I
  obtain ⟨_, _, rd4048⟩ :=
    RD.vowFlopToKickExtcodesizeGuard rd hperm hmem hread64
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨4048⟩) (okPc := ⟨1494⟩)
    (by simpa [σAsh, target, dump, sump] using rd4048)
    (by simpa [σAsh, target] using hcodeSize)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFlopKickCall
    {cA gh bl σ σ₀ A I} {g sel AshNew : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
      (AshNew :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
      Reasoning.Theory.uniswapExtCodeSizeWord σAsh
        (vowAddressReturnWord ⟨3⟩ σAsh I) ≠ ⟨0⟩) :
    let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
    let target := vowAddressReturnWord ⟨3⟩ σAsh I
    let dump := vowSlotWord ⟨8⟩ σAsh I
    let sump := vowSlotWord ⟨9⟩ σAsh I
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1497⟩
      (gasWord :: target :: ⟨0⟩ :: flopKickOutPtr :: flopKickInSize ::
        flopKickOutPtr :: flopKickOutSize :: flopKickEndPtr ::
        flopKickSelectorWord :: target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (flopKickCalldataMem I dump sump mem)
      (UInt256.ofNat 8) o (acc.1, σAsh) k' C' := by
  intro σAsh target dump sump
  obtain ⟨_, _, rd4048⟩ :=
    RD.vowFlopToKickExtcodesizeGuard rd hperm hmem hread64
  obtain ⟨gasWord, k', C', rd1497⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4048⟩) (okPc := ⟨1494⟩)
      (by simpa [σAsh, target, dump, sump] using rd4048)
      (by simpa [σAsh, target] using hcodeSize)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k', C', by simpa [σAsh, target, dump, sump] using rd1497⟩

theorem RD.vowFlopKickPostCall
    {cA gh bl σ σ₀ A I} {g sel AshNew : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
      (AshNew :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
      Reasoning.Theory.uniswapExtCodeSizeWord σAsh
        (vowAddressReturnWord ⟨3⟩ σAsh I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
    let target := vowAddressReturnWord ⟨3⟩ σAsh I
    let dump := vowSlotWord ⟨8⟩ σAsh I
    let sump := vowSlotWord ⟨9⟩ σAsh I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flopKickEndPtr :: flopKickSelectorWord ::
          target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (out.write 0 (flopKickCalldataMem I dump sump mem) flopKickOutPtr.toNat
          (min flopKickOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σAsh, createdAccounts := acc.1 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "kick" 0
        [.address I.codeOwner, .int (Int.ofNat dump.toNat), .int (Int.ofNat sump.toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro σAsh target dump sump
  obtain ⟨gasWord, _, _, rd1497⟩ :=
    RD.vowFlopKickCall rd hperm hmem hread64 hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k1498, C1498, hΘpack, rd1498raw, houtsz⟩ :=
    RD.call rd1497 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1498, C1498, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          flopKickOutPtr.toNat flopKickInSize.toNat)
          flopKickOutPtr.toNat flopKickOutSize.toNat) = UInt256.ofNat 8 := by
      unfold flopKickOutPtr flopKickInSize flopKickOutSize
      native_decide
    exact haw ▸ rd1498raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target)
      (mem := flopKickCalldataMem I dump sump mem)
      (inOff := flopKickOutPtr) (inSize := flopKickInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (by simpa [target] using flopKickAddress_eq_target σAsh I)
      (flopKickEncode_eq I dump sump hmem) ?_
    simpa [initState, hperm, σAsh] using hΘ

theorem flopKickWrite_size (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (flopKickCalldataMem I dump sump mem) 128 L).size = 228 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact flopKickCalldataMem_size I dump sump hmem
  · rw [write_eq_gen o (flopKickCalldataMem I dump sump mem) 128 L (by omega) hLo
      (by rw [flopKickCalldataMem_size I dump sump hmem]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      flopKickCalldataMem_size I dump sump hmem]
    omega

theorem flopKickWrite_read64 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (flopKickCalldataMem I dump sump mem) 128 L).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact flopKickCalldataMem_read64 I dump sump hmem hread64
  · rw [write_read_below_gen o (flopKickCalldataMem I dump sump mem) 128 L 64
      (by omega) hLo (by rw [flopKickCalldataMem_size I dump sump hmem]; omega)
      (by omega),
      flopKickCalldataMem_read64 I dump sump hmem hread64]

theorem flopKickWrite_read128_32 (I : ExecutionEnv) (dump sump : UInt256)
    {mem : ByteArray} (o : ByteArray)
    (hmem : mem.size = 164) (ho32 : 32 ≤ o.size) :
    (o.write 0 (flopKickCalldataMem I dump sump mem) 128 32).readWithPadding 128 32 =
      o.extract 0 32 :=
  write32_read_back o (flopKickCalldataMem I dump sump mem) 128 ho32
    (by rw [flopKickCalldataMem_size I dump sump hmem]; omega)

theorem RD.vowFlopKickCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨1498⟩) (okPc := ⟨1514⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowFlopKickCallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨1498⟩) (okPc := ⟨1514⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowFlopKickReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1516⟩) (okPc := ⟨1536⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowFlopKickReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1539⟩
      (retWord :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1516⟩) (okPc := ⟨1536⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.vowFlopKickDecodedToPublicReturn
    {cA gh bl σ σ₀ A I} {g sel id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1539⟩
      (id :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) o acc k C) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      (id :: sel :: []) mem (UInt256.ofNat 8) o acc k' C' := by
  have rd1540 := rd.swap2 (by native_decide) (by evm_ov)
  have rd1541 := rd1540.swap1 (by native_decide) (by evm_ov)
  have rd1542 := rd1541.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1542.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

-- GENERALIZES Reasoning.Solc.RD.solcReturnWordFromMem — active words are already 8.
theorem RD.vowFlopKickPublicReturn
    {cA gh bl σ σ₀ A I} {g sel id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem memout o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      (id :: sel :: []) mem (UInt256.ofNat 8) o acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hmemout : (UInt256.toByteArray id).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray id) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc
      (UInt256.toByteArray id) := by
  exact evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray id) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem RD.vowFlopKickSuccess
    {cA gh bl σ σ₀ A I} {g sel target dump sump id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨1⟩ :: flopKickEndPtr :: flopKickSelectorWord ::
        target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (out.write 0 (flopKickCalldataMem I dump sump mem) flopKickOutPtr.toNat
        (min flopKickOutSize (UInt256.ofNat out.size)).toNat)
      (UInt256.ofNat 8) out acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ out.size)
    (hosz : out.size < UInt256.size)
    (hid : id = UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc
      (UInt256.toByteArray id) := by
  have hmin : (min flopKickOutSize (UInt256.ofNat out.size)).toNat = 32 := by
    simpa [flopKickOutSize] using kissDaiMin32_toNat_of_ge ho32 hosz
  have rd1498 := rd
  rw [hmin, show flopKickOutPtr.toNat = 128 from by native_decide] at rd1498
  obtain ⟨_, _, rd1516⟩ :=
    RD.vowFlopKickCallSuccessToDecode rd1498 (by simp)
  have hmemWrite : (out.write 0 (flopKickCalldataMem I dump sump mem) 128 32).size =
      228 :=
    flopKickWrite_size I dump sump out 32 hmem (by omega) ho32
  have hread64Write :
      (out.write 0 (flopKickCalldataMem I dump sump mem) 128 32).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    flopKickWrite_read64 I dump sump out 32 hmem hread64 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (out.write 0 (flopKickCalldataMem I dump sump mem) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((out.write 0 (flopKickCalldataMem I dump sump mem) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
            (out.write 0 (flopKickCalldataMem I dump sump mem) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((out.write 0 (flopKickCalldataMem I dump sump mem) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥
              (out.write 0 (flopKickCalldataMem I dump sump mem) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩) := by
      rw [hmemWrite]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      flopKickWrite_read128_32 I dump sump out hmem ho32]
  obtain ⟨_, _, rd1539Raw⟩ :=
    RD.vowFlopKickReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
      rd1516 ho32 hosz hmload64 hmload128
  have rd1539 := by
    simpa [← hid] using rd1539Raw
  obtain ⟨_, _, rd357⟩ := RD.vowFlopKickDecodedToPublicReturn rd1539
  let memCall := out.write 0 (flopKickCalldataMem I dump sump mem) 128 32
  let memRet := (UInt256.toByteArray id).write 0 memCall 128 32
  have hmemCallSize : memCall.size = 228 := by
    simpa [memCall] using hmemWrite
  have hread64Call : memCall.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memCall] using hread64Write
  have hmemRetSize : memRet.size = 228 := by
    unfold memRet
    exact toByteArray_write32_size_of_le memCall id 128 228 228 hmemCallSize
      (by rw [hmemCallSize]; omega) (by omega)
  have hread64Ret : memRet.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold memRet
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmemCallSize]; omega) (by omega), hread64Call]
  have hmload64Ret :
      (if (⟨64⟩ : UInt256).toNat ≥ memRet.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memRet.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemRetSize]; decide) (by decide) hread64Ret
  have hread128Ret : memRet.readWithPadding 128 32 = UInt256.toByteArray id := by
    unfold memRet
    exact toByteArray_write32_read_back memCall id 128 (by rw [hmemCallSize]; omega)
  exact RD.vowFlopKickPublicReturn
    (memout := memRet) rd357 hmload64 (by rfl) hmload64Ret hread128Ret

end Benchmarks.Dss.Vow
