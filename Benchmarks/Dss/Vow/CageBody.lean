import Benchmarks.Dss.Vow.Arithmetic
import Benchmarks.Dss.Vow.Cage
import Benchmarks.Dss.Vow.FlopAsh

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` source-body helpers -/

abbrev cageLocalsFlapperDai (flapperDai : UInt256) : Store :=
  (∅ : Store).insert "flapperDai" (.int (Int.ofNat flapperDai.toNat))

theorem cageLocalsFlapperDai_get_flapperDai (flapperDai : UInt256) :
    (cageLocalsFlapperDai flapperDai).get? "flapperDai" =
      some (.int (Int.ofNat flapperDai.toNat)) := by
  rw [cageLocalsFlapperDai, store_get_self]

abbrev cageLocalsAfterFlapCage (flapperDai : UInt256) : Store :=
  (cageLocalsFlapperDai flapperDai).insert "_flapCageRet" (collapseReturns [])

theorem cageLocalsAfterFlapCage_get_flapperDai (flapperDai : UInt256) :
    (cageLocalsAfterFlapCage flapperDai).get? "flapperDai" =
      some (.int (Int.ofNat flapperDai.toNat)) := by
  rw [cageLocalsAfterFlapCage, store_get_ne _ _ (by decide),
    cageLocalsFlapperDai_get_flapperDai]

abbrev cageLocalsAfterFlopCage (flapperDai : UInt256) : Store :=
  (cageLocalsAfterFlapCage flapperDai).insert "_flopCageRet" (collapseReturns [])

theorem cageLocalsAfterFlopCage_get_flapperDai (flapperDai : UInt256) :
    (cageLocalsAfterFlopCage flapperDai).get? "flapperDai" =
      some (.int (Int.ofNat flapperDai.toNat)) := by
  rw [cageLocalsAfterFlopCage, store_get_ne _ _ (by decide),
    cageLocalsAfterFlapCage_get_flapperDai]

abbrev cageLocalsAfterVatDai (flapperDai vatDai : UInt256) : Store :=
  (cageLocalsAfterFlopCage flapperDai).insert "vatDai"
    (.int (Int.ofNat vatDai.toNat))

theorem cageLocalsAfterVatDai_get_flapperDai (flapperDai vatDai : UInt256) :
    (cageLocalsAfterVatDai flapperDai vatDai).get? "flapperDai" =
      some (.int (Int.ofNat flapperDai.toNat)) := by
  rw [cageLocalsAfterVatDai, store_get_ne _ _ (by decide),
    cageLocalsAfterFlopCage_get_flapperDai]

theorem cageLocalsAfterVatDai_get_vatDai (flapperDai vatDai : UInt256) :
    (cageLocalsAfterVatDai flapperDai vatDai).get? "vatDai" =
      some (.int (Int.ofNat vatDai.toNat)) := by
  rw [cageLocalsAfterVatDai, store_get_self]

abbrev cageLocalsAfterVatSin (flapperDai vatDai vatSin : UInt256) : Store :=
  (cageLocalsAfterVatDai flapperDai vatDai).insert "vatSin"
    (.int (Int.ofNat vatSin.toNat))

theorem cageLocalsAfterVatSin_get_vatDai (flapperDai vatDai vatSin : UInt256) :
    (cageLocalsAfterVatSin flapperDai vatDai vatSin).get? "vatDai" =
      some (.int (Int.ofNat vatDai.toNat)) := by
  rw [cageLocalsAfterVatSin, store_get_ne _ _ (by decide),
    cageLocalsAfterVatDai_get_vatDai]

theorem cageLocalsAfterVatSin_get_vatSin (flapperDai vatDai vatSin : UInt256) :
    (cageLocalsAfterVatSin flapperDai vatDai vatSin).get? "vatSin" =
      some (.int (Int.ofNat vatSin.toNat)) := by
  rw [cageLocalsAfterVatSin, store_get_self]

abbrev cageLocalsAfterHealRad
    (flapperDai vatDai vatSin healRad : UInt256) : Store :=
  (cageLocalsAfterVatSin flapperDai vatDai vatSin).insert "healRad"
    (.int (Int.ofNat healRad.toNat))

theorem cageLocalsAfterHealRad_get_healRad
    (flapperDai vatDai vatSin healRad : UInt256) :
    (cageLocalsAfterHealRad flapperDai vatDai vatSin healRad).get? "healRad" =
      some (.int (Int.ofNat healRad.toNat)) := by
  rw [cageLocalsAfterHealRad, store_get_self]

abbrev cageLocalsAfterHealRet
    (flapperDai vatDai vatSin healRad : UInt256) : Store :=
  (cageLocalsAfterHealRad flapperDai vatDai vatSin healRad).insert "_healRet"
    (collapseReturns [])

abbrev cageVatAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask).toNat

def cageFlopperCageStmts : List Stmt :=
  checkedExternalCallStmts (.storage flopperRef) "cage" (.intLit 0) [] "_flopCageRet"

def cageVatDaiStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
    (perm := false)

def cageVatSinStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
    (perm := false)

def cageMinStmts : List Stmt :=
  [.internalCall "min" [.var "vatDai", .var "vatSin"] "healRad"]

def cageVatHealStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "heal" (.intLit 0) [.var "healRad"] "_healRet"

noncomputable def cageHealCalldataMem (healRad : UInt256) (mem : ByteArray) : ByteArray :=
  healRad.toByteArray.write 0 (kissHealSelectorMem mem) 132 32

theorem cageHealCalldataMem_size (healRad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (cageHealCalldataMem healRad mem).size = 164 := by
  unfold cageHealCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [kissHealSelectorMem_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, kissHealSelectorMem_size hmem,
    toByteArray_size]
  omega

theorem cageHealCalldataMem_read64 (healRad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (cageHealCalldataMem healRad mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold cageHealCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [kissHealSelectorMem_size hmem]; omega) (by omega),
    kissHealSelectorMem_read64 hmem hread64]

theorem cageHealCalldataMem_read128_36 (healRad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (cageHealCalldataMem healRad mem).readWithPadding 128 36 =
      vatHealSelector ++ healRad.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [cageHealCalldataMem_size healRad hmem]), cageHealCalldataMem,
    write32_eq _ (kissHealSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [kissHealSelectorMem_size hmem]; omega)]
  have hAsz : ((kissHealSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, kissHealSelectorMem_size hmem]
    omega
  have hBsz : (healRad.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((kissHealSelectorMem mem).extract 0 132 ++
        healRad.toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : healRad.toByteArray.extract 0 32 = healRad.toByteArray := by
    have h := @ByteArray.extract_zero_size healRad.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), kissHealSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem cageHealEncode_eq (healRad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    config.externalABI.encode? "heal" [.int (Int.ofNat healRad.toNat)] =
      some ((cageHealCalldataMem healRad mem).readWithPadding
        kissHealOutPtr.toNat kissHealInSize.toNat) := by
  rw [kissHealInSize_eq]
  change config.externalABI.encode? "heal" [.int (Int.ofNat healRad.toNat)] =
    some ((cageHealCalldataMem healRad mem).readWithPadding 128 36)
  rw [cageHealCalldataMem_read128_36 healRad hmem]
  have hlt : healRad.toNat < EVM.twoPow 256 := healRad.val.isLt
  have hword : EVM.word healRad.toNat = healRad := by
    show UInt256.ofNat healRad.toNat = healRad
    exact u256_ofNat_toNat _
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    uint256, uint256Int, vatHealSelector, selectorBytes, hlt, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem cageDecodeVoid_ok (out : ByteArray) :
    config.externalABI.decode? "cage" out = some [] := by
  simp [config, vowExternalABI, decodeVoid?]

theorem cageFlopperCageNoCode
    {evm : EVM.State} {flapperDai : UInt256}
    (hflopperNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := cageLocalsAfterFlapCage flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageFlopperCageStmts .reverted := by
  intro locals
  have hflopper :
      evalExpr? config { contract := contract, locals := locals } evm (.storage flopperRef) =
        .ok (.address (flopFlopperAddressOf evm)) := by
    simpa [locals, cageLocalsAfterFlapCage, cageLocalsFlapperDai] using
      evalExpr_flopFlopperStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterFlapCage, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage flopperRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_extCodeGuard_false hflopper hflopperNoCode
  simp only [cageFlopperCageStmts, checkedExternalCallStmts]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem cageFlopperCageCallFailure
    {evm evmFlop : EVM.State} {outFlop : ByteArray} {flapperDai : UInt256}
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evm (EVM.address (flopFlopperAddressOf evm))
        "cage" 0 [] (false, evmFlop, outFlop) true) :
    let locals := cageLocalsAfterFlapCage flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageFlopperCageStmts .reverted := by
  intro locals
  have hflopper :
      evalExpr? config { contract := contract, locals := locals } evm (.storage flopperRef) =
        .ok (.address (flopFlopperAddressOf evm)) := by
    simpa [locals, cageLocalsAfterFlapCage, cageLocalsFlapperDai] using
      evalExpr_flopFlopperStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterFlapCage, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage flopperRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_extCodeGuard_true hflopper hflopperCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [] = .ok [] := by
    rfl
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage flopperRef) "cage" (.intLit 0) [] "_flopCageRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hflopper (by simp [evalExpr?, pure]) hargs hcallFlop
  simp only [cageFlopperCageStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageFlopperCageSuccess
    {evm evmFlop : EVM.State} {outFlop : ByteArray} {flapperDai : UInt256}
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evm (EVM.address (flopFlopperAddressOf evm))
        "cage" 0 [] (true, evmFlop, outFlop) true) :
    let locals := cageLocalsAfterFlapCage flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageFlopperCageStmts
      (.ok { contract := contract, locals := cageLocalsAfterFlopCage flapperDai }
        evmFlop) := by
  intro locals
  have hflopper :
      evalExpr? config { contract := contract, locals := locals } evm (.storage flopperRef) =
        .ok (.address (flopFlopperAddressOf evm)) := by
    simpa [locals, cageLocalsAfterFlapCage, cageLocalsFlapperDai] using
      evalExpr_flopFlopperStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterFlapCage, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage flopperRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_extCodeGuard_true hflopper hflopperCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [] = .ok [] := by
    rfl
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage flopperRef) "cage" (.intLit 0) [] "_flopCageRet")
        (.ok { contract := contract, locals := cageLocalsAfterFlopCage flapperDai }
          evmFlop) := by
    simpa [locals, cageLocalsAfterFlopCage, cageDecodeVoid_ok, collapseReturns] using
      ExecStmt.externalCallSuccess hflopper (by simp [evalExpr?, pure]) hargs
        hcallFlop (cageDecodeVoid_ok outFlop)
  simp only [cageFlopperCageStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consNormal hcallStmt ExecBlock.nil)

theorem cageVatDaiNoCode
    {evm : EVM.State} {flapperDai : UInt256}
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := cageLocalsAfterFlopCage flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatDaiStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterFlopCage, cageLocalsAfterFlapCage,
          cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_kissVatCodeGuard_false hvat hvatNoCode
  simp only [cageVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem cageVatDaiCallFailure
    {evm evmDai : EVM.State} {outDai : ByteArray} {flapperDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address evm.executionEnv.codeOwner] (false, evmDai, outDai)
        false) :
    let locals := cageLocalsAfterFlopCage flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatDaiStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterFlopCage, cageLocalsAfterFlapCage,
          cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
        .ok [.address evm.executionEnv.codeOwner] := by
    simpa [locals] using evalExprs_kissThis evm locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallDai
  simp only [cageVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageVatDaiReturnDecodeFailure
    {evm evmDai : EVM.State} {outDai : ByteArray} {flapperDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address evm.executionEnv.codeOwner] (true, evmDai, outDai)
        false)
    (hdecDai : config.externalABI.decode? "dai" outDai = none) :
    let locals := cageLocalsAfterFlopCage flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatDaiStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterFlopCage, cageLocalsAfterFlapCage,
          cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
        .ok [.address evm.executionEnv.codeOwner] := by
    simpa [locals] using evalExprs_kissThis evm locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargs hcallDai hdecDai
  simp only [cageVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageVatDaiSuccess
    {evm evmDai : EVM.State} {outDai : ByteArray} {flapperDai vatDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address evm.executionEnv.codeOwner] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)]) :
    let locals := cageLocalsAfterFlopCage flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatDaiStmts
      (.ok { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
        evmDai) := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterFlopCage, cageLocalsAfterFlapCage,
          cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
        .ok [.address evm.executionEnv.codeOwner] := by
    simpa [locals] using evalExprs_kissThis evm locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := cageLocalsAfterVatDai flapperDai vatDai }
          evmDai) := by
    simpa [locals, cageLocalsAfterVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs
        hcallDai hdecDai
  simp only [cageVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consNormal hcallStmt ExecBlock.nil)

theorem cageVatSinNoCode
    {evm : EVM.State} {flapperDai vatDai : UInt256}
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := cageLocalsAfterVatDai flapperDai vatDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatSinStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterVatDai, cageLocalsAfterFlopCage,
          cageLocalsAfterFlapCage, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_kissVatCodeGuard_false hvat hvatNoCode
  simp only [cageVatSinStmts, checkedExternalCallStmts]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem cageVatSinCallFailure
    {evm evmSin : EVM.State} {outSin : ByteArray} {flapperDai vatDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "sin" 0 [.address evm.executionEnv.codeOwner] (false, evmSin, outSin)
        false) :
    let locals := cageLocalsAfterVatDai flapperDai vatDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatSinStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterVatDai, cageLocalsAfterFlopCage,
          cageLocalsAfterFlapCage, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
        .ok [.address evm.executionEnv.codeOwner] := by
    simpa [locals] using evalExprs_kissThis evm locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallSin
  simp only [cageVatSinStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageVatSinReturnDecodeFailure
    {evm evmSin : EVM.State} {outSin : ByteArray} {flapperDai vatDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "sin" 0 [.address evm.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin : config.externalABI.decode? "sin" outSin = none) :
    let locals := cageLocalsAfterVatDai flapperDai vatDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatSinStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterVatDai, cageLocalsAfterFlopCage,
          cageLocalsAfterFlapCage, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
        .ok [.address evm.executionEnv.codeOwner] := by
    simpa [locals] using evalExprs_kissThis evm locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargs hcallSin hdecSin
  simp only [cageVatSinStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageVatSinSuccess
    {evm evmSin : EVM.State} {outSin : ByteArray}
    {flapperDai vatDai vatSin : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "sin" 0 [.address evm.executionEnv.codeOwner] (true, evmSin, outSin)
        false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)]) :
    let locals := cageLocalsAfterVatDai flapperDai vatDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatSinStmts
      (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
        evmSin) := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterVatDai, cageLocalsAfterFlopCage,
          cageLocalsAfterFlapCage, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
        .ok [.address evm.executionEnv.codeOwner] := by
    simpa [locals] using evalExprs_kissThis evm locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := cageLocalsAfterVatSin flapperDai vatDai vatSin }
          evmSin) := by
    simpa [locals, cageLocalsAfterVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs
        hcallSin hdecSin
  simp only [cageVatSinStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consNormal hcallStmt ExecBlock.nil)

theorem cageMinLeft
    {evm : EVM.State} {flapperDai vatDai vatSin : UInt256}
    (hle : vatDai.toNat ≤ vatSin.toNat) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      cageMinStmts
      (.ok { contract := contract, locals := cageLocalsAfterHealRad flapperDai vatDai vatSin vatDai }
        evm) := by
  intro locals
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vatDai") =
        .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (evm := evm)
        (locals := cageLocalsAfterVatSin flapperDai vatDai vatSin)
        (name := "vatDai") (value := vatDai)
        (cageLocalsAfterVatSin_get_vatDai flapperDai vatDai vatSin)
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (evm := evm)
        (locals := cageLocalsAfterVatSin flapperDai vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (cageLocalsAfterVatSin_get_vatSin flapperDai vatDai vatSin)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "vatDai", .var "vatSin"] =
          .ok [.int (Int.ofNat vatDai.toNat), .int (Int.ofNat vatSin.toNat)] := by
    simp [evalExprs?, hvatDai, hvatSin, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? minFunction.params
          [.int (Int.ofNat vatDai.toNat), .int (Int.ofNat vatSin.toNat)] =
        some (uintBinaryLocals vatDai vatSin) := by
    simp [minFunction, uint256, bindParams?, uintBinaryLocals]
  have hcall :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "min" [.var "vatDai", .var "vatSin"] "healRad")
        (.ok { contract := contract, locals := cageLocalsAfterHealRad flapperDai vatDai vatSin vatDai }
          evm) := by
    have hbody := execMinFunctionReturnLeft (evm := evm) (x := vatDai) (y := vatSin) hle
    simpa [locals, cageLocalsAfterHealRad, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals })
        (evm := evm) (calleeEvm := evm) (name := "min") (retVar := "healRad")
        (args := [.var "vatDai", .var "vatSin"])
        (argVals := [.int (Int.ofNat vatDai.toNat), .int (Int.ofNat vatSin.toNat)])
        (callee := minFunction) (locals := uintBinaryLocals vatDai vatSin)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatDai vatSin vatDai })
        (value := some [.int (Int.ofNat vatDai.toNat)])
        hargs (by rfl) hbind hbody)
  simp only [cageMinStmts]
  exact ExecBlock.consNormal hcall ExecBlock.nil

theorem cageMinRight
    {evm : EVM.State} {flapperDai vatDai vatSin : UInt256}
    (hlt : vatSin.toNat < vatDai.toNat) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      cageMinStmts
      (.ok { contract := contract, locals := cageLocalsAfterHealRad flapperDai vatDai vatSin vatSin }
        evm) := by
  intro locals
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vatDai") =
        .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (evm := evm)
        (locals := cageLocalsAfterVatSin flapperDai vatDai vatSin)
        (name := "vatDai") (value := vatDai)
        (cageLocalsAfterVatSin_get_vatDai flapperDai vatDai vatSin)
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals } evm (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (evm := evm)
        (locals := cageLocalsAfterVatSin flapperDai vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (cageLocalsAfterVatSin_get_vatSin flapperDai vatDai vatSin)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "vatDai", .var "vatSin"] =
          .ok [.int (Int.ofNat vatDai.toNat), .int (Int.ofNat vatSin.toNat)] := by
    simp [evalExprs?, hvatDai, hvatSin, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? minFunction.params
          [.int (Int.ofNat vatDai.toNat), .int (Int.ofNat vatSin.toNat)] =
        some (uintBinaryLocals vatDai vatSin) := by
    simp [minFunction, uint256, bindParams?, uintBinaryLocals]
  have hcall :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "min" [.var "vatDai", .var "vatSin"] "healRad")
        (.ok { contract := contract, locals := cageLocalsAfterHealRad flapperDai vatDai vatSin vatSin }
          evm) := by
    have hbody := execMinFunctionReturnRight (evm := evm) (x := vatDai) (y := vatSin) hlt
    simpa [locals, cageLocalsAfterHealRad, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals })
        (evm := evm) (calleeEvm := evm) (name := "min") (retVar := "healRad")
        (args := [.var "vatDai", .var "vatSin"])
        (argVals := [.int (Int.ofNat vatDai.toNat), .int (Int.ofNat vatSin.toNat)])
        (callee := minFunction) (locals := uintBinaryLocals vatDai vatSin)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatDai vatSin vatSin })
        (value := some [.int (Int.ofNat vatSin.toNat)])
        hargs (by rfl) hbind hbody)
  simp only [cageMinStmts]
  exact ExecBlock.consNormal hcall ExecBlock.nil

theorem cageVatHealNoCode
    {evm : EVM.State} {flapperDai vatDai vatSin healRad : UInt256}
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := cageLocalsAfterHealRad flapperDai vatDai vatSin healRad
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatHealStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterHealRad, cageLocalsAfterVatSin,
          cageLocalsAfterVatDai, cageLocalsAfterFlopCage, cageLocalsAfterFlapCage,
          cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_kissVatCodeGuard_false hvat hvatNoCode
  simp only [cageVatHealStmts, checkedExternalCallStmts]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem cageVatHealCallFailure
    {evm evmHeal : EVM.State} {outHeal : ByteArray}
    {flapperDai vatDai vatSin healRad : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "heal" 0 [.int (Int.ofNat healRad.toNat)] (false, evmHeal, outHeal)
        true) :
    let locals := cageLocalsAfterHealRad flapperDai vatDai vatSin healRad
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatHealStmts .reverted := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterHealRad, cageLocalsAfterVatSin,
          cageLocalsAfterVatDai, cageLocalsAfterFlopCage, cageLocalsAfterFlapCage,
          cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hhealRad :
      evalExpr? config { contract := contract, locals := locals } evm (.var "healRad") =
        .ok (.int (Int.ofNat healRad.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (evm := evm)
        (locals := cageLocalsAfterHealRad flapperDai vatDai vatSin healRad)
        (name := "healRad") (value := healRad)
        (cageLocalsAfterHealRad_get_healRad flapperDai vatDai vatSin healRad)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "healRad"] =
        .ok [.int (Int.ofNat healRad.toNat)] := by
    simp [evalExprs?, hhealRad, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "heal" (.intLit 0) [.var "healRad"] "_healRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallHeal
  simp only [cageVatHealStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageVatHealSuccess
    {evm evmHeal : EVM.State} {outHeal : ByteArray}
    {flapperDai vatDai vatSin healRad : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "heal" 0 [.int (Int.ofNat healRad.toNat)] (true, evmHeal, outHeal)
        true) :
    let locals := cageLocalsAfterHealRad flapperDai vatDai vatSin healRad
    ExecBlock config { contract := contract, locals := locals } evm
      cageVatHealStmts
      (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin healRad }
        evmHeal) := by
  intro locals
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [locals, cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsAfterHealRad, cageLocalsAfterVatSin,
          cageLocalsAfterVatDai, cageLocalsAfterFlopCage, cageLocalsAfterFlapCage,
          cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hhealRad :
      evalExpr? config { contract := contract, locals := locals } evm (.var "healRad") =
        .ok (.int (Int.ofNat healRad.toNat)) := by
    simpa [locals] using
      evalExpr_varUInt256 (evm := evm)
        (locals := cageLocalsAfterHealRad flapperDai vatDai vatSin healRad)
        (name := "healRad") (value := healRad)
        (cageLocalsAfterHealRad_get_healRad flapperDai vatDai vatSin healRad)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "healRad"] =
        .ok [.int (Int.ofNat healRad.toNat)] := by
    simp [evalExprs?, hhealRad, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage vatRef) "heal" (.intLit 0) [.var "healRad"] "_healRet")
        (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin healRad }
          evmHeal) := by
    simpa [locals, cageLocalsAfterHealRet, cageDecodeVoid_ok, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs
        hcallHeal (cageDecodeVoid_ok outHeal)
  simp only [cageVatHealStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consNormal hcallStmt ExecBlock.nil)

set_option maxHeartbeats 0 in
theorem RD.vowCageSecondDaiExtcodesizeGuard {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2983⟩
      (d1 :: d2 :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (_hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3058⟩
      (kissDaiTargetWord acc.2 ee :: kissDaiTargetWord acc.2 ee ::
        ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        kissDaiTargetWord acc.2 ee :: ⟨3238⟩ :: ⟨4084909596⟩ ::
        kissDaiTargetWord acc.2 ee :: R)
      (vatDaiCalldataMem ee mem) (UInt256.ofNat 6) rdata acc k' C' := by
  let target := kissDaiTargetWord acc.2 ee
  let rawTarget := vowSlotWord ⟨1⟩ acc.2 ee
  have rd2985 := rd.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  obtain ⟨k2986, C2986, rd2986Raw⟩ := rd2985.sload (by decide +native) (by evm_ov)
  have rd2986 : RD vowBytecode ee g s0 ⟨2986⟩
      (rawTarget :: d1 :: d2 :: R) mem (UInt256.ofNat 6) rdata acc k2986 C2986 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd2986Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hDaiMem : (vatDaiCalldataMem ee mem).size = 164 :=
    vatDaiCalldataMem_size ee hmem
  have hDaiRead64 :
      (vatDaiCalldataMem ee mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    vatDaiCalldataMem_read64 ee hmem hread64
  have hmload64Dai :
      (if (⟨64⟩ : UInt256).toNat ≥ (vatDaiCalldataMem ee mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((vatDaiCalldataMem ee mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hDaiMem]; decide) (by decide) hDaiRead64
  have rd3058 := evm_run rd2986 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨907205027⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 0 (vatDaiSelectorMem mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    address,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (vatDaiCalldataMem ee mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Dai (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap4,
    pop,
    push4 ⟨4084909596⟩,
    swap3,
    pop,
    push2 ⟨3238⟩,
    swap2,
    dup5,
    swap2,
    push4 ⟨1814410054⟩,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup4,
    add,
    swap3,
    push1 ⟨32⟩,
    swap3,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup7,
    dup1]
  have hpc3058 :
      (⟨2986⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ =
        ⟨3058⟩ := by
    decide +native
  rw [hpc3058] at rd3058
  exact ⟨_, _, by
    simpa [target, rawTarget, kissDaiTargetWord, kissDaiSelectorShifted,
      vatDaiSelectorMem, vatDaiCalldataMem, vowSlotWord, solcSlotWord, solcAddrMask,
      u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩ = ⟨36⟩
        from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide +native]
      using rd3058⟩

theorem RD.vowCageSecondDaiNoCode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2983⟩
      (d1 :: d2 :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 ee) = ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd3058⟩ := RD.vowCageSecondDaiExtcodesizeGuard
    rd hmem hread64 hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3058⟩) (okPc := ⟨3070⟩)
    rd3058 hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp; omega)

theorem RD.vowCageSecondDaiStaticcallSetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨2983⟩
      (d1 :: d2 :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (kissDaiTargetWord acc.2 ee) ≠ ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨3073⟩
      (gasWord :: kissDaiTargetWord acc.2 ee :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ ::
        ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord acc.2 ee ::
        ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc.2 ee :: R)
      (vatDaiCalldataMem ee mem) (UInt256.ofNat 6) rdata acc k' C' := by
  obtain ⟨_, _, rd3058⟩ := RD.vowCageSecondDaiExtcodesizeGuard
    rd hmem hread64 hov
  obtain ⟨gasWord, k3073, C3073, rd3073⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3058⟩) (okPc := ⟨3070⟩) rd3058
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp; omega)
  exact ⟨gasWord, k3073, C3073, rd3073⟩

theorem RD.vowCageSecondDaiStaticcall
    {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {cA_call : Batteries.RBSet AccountAddress compare}
    {mem rdata : ByteArray} {k C : ℕ} {d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2983⟩
      (d1 :: d2 :: R) mem (UInt256.ofNat 6) rdata (cA_call, σCall) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (kissDaiTargetWord σCall I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 16 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outDai : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3074⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨1814410054⟩ ::
          kissDaiTargetWord σCall I :: ⟨3238⟩ :: ⟨4084909596⟩ ::
          kissDaiTargetWord σCall I :: R)
        (outDai.write 0 (vatDaiCalldataMem I mem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
        (UInt256.ofNat 6) outDai (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σCall
          createdAccounts := cA_call }
        (EVM.address (kissVatAddress σCall I)) "dai" 0 [.address I.codeOwner]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ'
            substate := A'
            createdAccounts := cA' },
          outDai) false
    ∧ outDai.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3073⟩ := RD.vowCageSecondDaiStaticcallSetup
    rd hmem hread64 hcodeSize hov
  obtain ⟨cA', σ', z, outDai, A_in, callGas, k3074, C3074, hΘpack, rd3074raw,
      houtsz⟩ :=
    RD.solcStaticcall rd3073 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmDaiIn := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σCall
    createdAccounts := cA_call }
  refine ⟨cA', σ', z, outDai, A', k3074, C3074, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      decide +native
    exact haw ▸ rd3074raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σCall I)
      (mem := vatDaiCalldataMem I mem) (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmDaiIn, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      (kissVatAddress_eq_daiTarget σCall I) (vatDaiEncode_eq I hmem) ?_
    simpa [evmDaiIn, initState] using hΘ

theorem RD.vowCageSecondDaiCallFailure {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3074⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3074⟩) (okPc := ⟨3090⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) hosz hov

theorem RD.vowCageSecondDaiCallSuccessToDecode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3074⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3092⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨3074⟩) (okPc := ⟨3090⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowCageSecondDaiReturnDecodeShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3092⟩
      (d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨3092⟩) (okPc := ⟨3112⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by simp; omega)

theorem RD.vowCageSecondDaiReturnDecodeOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {retWord d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3092⟩
      (d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 6) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3115⟩
      (retWord :: R) mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨3092⟩) (okPc := ⟨3112⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) (by decide +native) (by decide +native) (by decide +native) (by simp; omega)

set_option maxHeartbeats 0 in
theorem RD.vowCageVatSinExtcodesizeGuard {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {vatDai : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3115⟩
      (vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc.2 ee :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (_hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3177⟩
      (kissDaiTargetWord acc.2 ee :: kissDaiTargetWord acc.2 ee :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord acc.2 ee :: vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ ::
        kissDaiTargetWord acc.2 ee :: R)
      (healSinCalldataMem ee mem) (UInt256.ofNat 6) rdata acc k' C' := by
  let target := kissDaiTargetWord acc.2 ee
  let rawTarget := vowSlotWord ⟨1⟩ acc.2 ee
  have rd3117 := rd.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  obtain ⟨k3118, C3118, rd3118Raw⟩ := rd3117.sload (by decide +native) (by evm_ov)
  have rd3118 : RD vowBytecode ee g s0 ⟨3118⟩
      (rawTarget :: vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: target :: R)
      mem (UInt256.ofNat 6) rdata acc k3118 C3118 := by
    simpa [target, rawTarget, vowSlotWord, solcSlotWord] using rd3118Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hSinMem : (healSinCalldataMem ee mem).size = 164 :=
    healSinCalldataMem_size ee hmem
  have hSinRead64 :
      (healSinCalldataMem ee mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    healSinCalldataMem_read64 ee hmem hread64
  have hmload64Sin :
      (if (⟨64⟩ : UInt256).toNat ≥ (healSinCalldataMem ee mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((healSinCalldataMem ee mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSinMem]; decide) (by decide) hSinRead64
  have rd3177 := evm_run rd3118 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨2016186517⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 0 (healSinSelectorMem mem) (UInt256.ofNat 6) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    address,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (healSinCalldataMem ee mem) (UInt256.ofNat 6) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Sin (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap2,
    push4 healSinSelector,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 ⟨32⟩,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup7,
    dup1]
  have hpc3177 :
      (⟨3118⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨3177⟩ := by
    decide +native
  rw [hpc3177] at rd3177
  exact ⟨_, _, by
    simpa [target, rawTarget, kissDaiTargetWord, healSinSelectorShifted,
      healSinSelector, healSinSelectorMem, healSinCalldataMem, healSinOutPtr,
      healSinInSize, healSinEndPtr, vowSlotWord, solcSlotWord, solcAddrMask,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩ = ⟨36⟩
        from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide +native]
      using rd3177⟩

theorem RD.vowCageVatSinNoCode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {vatDai : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3115⟩
      (vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc.2 ee :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 ee) = ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd3177⟩ := RD.vowCageVatSinExtcodesizeGuard rd hmem hread64 hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3177⟩) (okPc := ⟨3189⟩)
    rd3177 hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp; omega)

theorem RD.vowCageVatSinStaticcallSetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {vatDai : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3115⟩
      (vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord acc.2 ee :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 ee) ≠ ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨3192⟩
      (gasWord :: kissDaiTargetWord acc.2 ee :: healSinOutPtr :: healSinInSize ::
        healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord acc.2 ee :: vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ ::
        kissDaiTargetWord acc.2 ee :: R)
      (healSinCalldataMem ee mem) (UInt256.ofNat 6) rdata acc k' C' := by
  obtain ⟨_, _, rd3177⟩ := RD.vowCageVatSinExtcodesizeGuard rd hmem hread64 hov
  obtain ⟨gasWord, k3192, C3192, rd3192⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3177⟩) (okPc := ⟨3189⟩) rd3177
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp; omega)
  exact ⟨gasWord, k3192, C3192, by simpa using rd3192⟩

set_option maxHeartbeats 0 in
theorem RD.vowCageVatSinStaticcall
    {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {cA_call : Batteries.RBSet AccountAddress compare}
    {mem rdata : ByteArray} {k C : ℕ} {vatDai : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3115⟩
      (vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ :: kissDaiTargetWord σCall I :: R)
      mem (UInt256.ofNat 6) rdata (cA_call, σCall) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (kissDaiTargetWord σCall I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 18 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outSin : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3193⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord σCall I :: vatDai :: ⟨3238⟩ :: ⟨4084909596⟩ ::
          kissDaiTargetWord σCall I :: R)
        (outSin.write 0 (healSinCalldataMem I mem) healSinOutPtr.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
        (UInt256.ofNat 6) outSin (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σCall
          createdAccounts := cA_call }
        (EVM.address (kissVatAddress σCall I)) "sin" 0 [.address I.codeOwner]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ'
            substate := A'
            createdAccounts := cA' },
          outSin) false
    ∧ outSin.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3192⟩ := RD.vowCageVatSinStaticcallSetup
    (ee := I) (acc := (cA_call, σCall)) (mem := mem) (rdata := rdata)
    (vatDai := vatDai) (R := R) rd hmem hread64 hcodeSize hov
  obtain ⟨cA', σ', z, outSin, A_in, callGas, k3193, C3193, hΘpack,
      rd3193raw, houtsz⟩ :=
    RD.solcStaticcall rd3192 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmSinIn := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σCall
    createdAccounts := cA_call }
  refine ⟨cA', σ', z, outSin, A', k3193, C3193, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          healSinOutPtr.toNat healSinInSize.toNat)
          healSinOutPtr.toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      rw [healSinInSize_eq]
      unfold healSinOutPtr
      decide +native
    exact haw ▸ rd3193raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σCall I)
      (mem := healSinCalldataMem I mem) (inOff := healSinOutPtr) (inSize := healSinInSize)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmSinIn, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      (kissVatAddress_eq_daiTarget σCall I) (healSinEncode_eq I hmem) ?_
    simpa [evmSinIn, initState] using hΘ

theorem RD.vowCageVatSinCallFailure {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3193⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3193⟩) (okPc := ⟨3209⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) hosz hov

theorem RD.vowCageVatSinCallSuccessToDecode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3193⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3211⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨3193⟩) (okPc := ⟨3209⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowCageVatSinReturnDecodeShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3211⟩
      (d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨3211⟩) (okPc := ⟨3231⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by simp; omega)

theorem RD.vowCageVatSinReturnDecodeOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {retWord d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3211⟩
      (d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 6) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3234⟩
      (retWord :: R) mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨3211⟩) (okPc := ⟨3231⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) (by decide +native) (by decide +native) (by decide +native) (by simp; omega)

theorem RD.vowCageMinReturnLeft {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {vatDai vatSin : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3234⟩ (vatSin :: vatDai :: ⟨3238⟩ :: R)
      mem aw o acc k C)
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3238⟩ (vatDai :: R) mem aw o acc k' C' := by
  have rd3237 := rd.push2 ⟨5112⟩ (by decide +native) (by evm_ov)
  have rd5112 := rd3237.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd5113 := rd5112.jumpdest (by decide +native) (by evm_ov)
  have rd5115 := rd5113.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd5116 := rd5115.dup2 (by decide +native) (by evm_ov)
  have rd5117 := rd5116.dup4 (by decide +native) (by evm_ov)
  have rd5118Raw := rd5117.gt (by decide +native) (by evm_ov)
  have hgt : UInt256.gt vatDai vatSin = ⟨0⟩ := ugt_zero hle
  have rd5118 := rd5118Raw
  rw [hgt] at rd5118
  have rd5119Raw := rd5118.iszero (by decide +native) (by evm_ov)
  have rd5119 := rd5119Raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5119
  have rd5122 := rd5119.push2 ⟨5128⟩ (by decide +native) (by evm_ov)
  have rd5128 := rd5122.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd5129 := rd5128.jumpdest (by decide +native) (by evm_ov)
  have rd5130 := rd5129.dup3 (by decide +native) (by evm_ov)
  have rd5131 := rd5130.jumpdest (by decide +native) (by evm_ov)
  have rd5132 := rd5131.swap4 (by decide +native) (by evm_ov)
  have rd5133 := rd5132.swap3 (by decide +native) (by evm_ov)
  have rd5134 := rd5133.pop (by decide +native) (by evm_ov)
  have rd5135 := rd5134.pop (by decide +native) (by evm_ov)
  have rd5136 := rd5135.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd5136.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem RD.vowCageMinReturnRight {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {vatDai vatSin : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3234⟩ (vatSin :: vatDai :: ⟨3238⟩ :: R)
      mem aw o acc k C)
    (hlt : vatSin.toNat < vatDai.toNat)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3238⟩ (vatSin :: R) mem aw o acc k' C' := by
  have rd3237 := rd.push2 ⟨5112⟩ (by decide +native) (by evm_ov)
  have rd5112 := rd3237.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd5113 := rd5112.jumpdest (by decide +native) (by evm_ov)
  have rd5115 := rd5113.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd5116 := rd5115.dup2 (by decide +native) (by evm_ov)
  have rd5117 := rd5116.dup4 (by decide +native) (by evm_ov)
  have rd5118Raw := rd5117.gt (by decide +native) (by evm_ov)
  have hgt : UInt256.gt vatDai vatSin = ⟨1⟩ := ugt_one hlt
  have rd5118 := rd5118Raw
  rw [hgt] at rd5118
  have rd5119Raw := rd5118.iszero (by decide +native) (by evm_ov)
  have rd5119 := rd5119Raw
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5119
  have rd5122 := rd5119.push2 ⟨5128⟩ (by decide +native) (by evm_ov)
  have rd5123 := rd5122.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd5124 := rd5123.dup2 (by decide +native) (by evm_ov)
  have rd5127 := rd5124.push2 ⟨5130⟩ (by decide +native) (by evm_ov)
  have rd5130 := rd5127.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd5131 := rd5130.jumpdest (by decide +native) (by evm_ov)
  have rd5132 := rd5131.swap4 (by decide +native) (by evm_ov)
  have rd5133 := rd5132.swap3 (by decide +native) (by evm_ov)
  have rd5134 := rd5133.pop (by decide +native) (by evm_ov)
  have rd5135 := rd5134.pop (by decide +native) (by evm_ov)
  have rd5136 := rd5135.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd5136.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 0 in
theorem RD.vowCageHealExtcodesizeGuard {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {healRad : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3238⟩
      (healRad :: kissHealSelector :: kissDaiTargetWord acc.2 ee :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (_hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨3280⟩
      (kissDaiTargetWord acc.2 ee :: kissDaiTargetWord acc.2 ee :: kissHealOutSize ::
        kissHealOutPtr :: kissHealInSize :: kissHealOutPtr :: kissHealOutSize ::
        kissHealEndPtr :: kissHealSelector :: kissDaiTargetWord acc.2 ee :: R)
      (cageHealCalldataMem healRad mem) (UInt256.ofNat 6) rdata acc k' C' := by
  let target := kissDaiTargetWord acc.2 ee
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hHealMem : (cageHealCalldataMem healRad mem).size = 164 :=
    cageHealCalldataMem_size healRad hmem
  have hHealRead64 :
      (cageHealCalldataMem healRad mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    cageHealCalldataMem_read64 healRad hmem hread64
  have hmload64Heal :
      (if (⟨64⟩ : UInt256).toNat ≥ (cageHealCalldataMem healRad mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((cageHealCalldataMem healRad mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hHealMem]; decide) (by decide) hHealRead64
  have rd3280 := evm_run rd with [
    jumpdest,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    dup3,
    push4 ⟨4294967295⟩,
    and,
    push1 ⟨224⟩,
    shl,
    dup2,
    raw mstore 0 (kissHealSelectorMem mem) (UInt256.ofNat 6) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    add,
    dup1,
    dup3,
    dup2,
    raw mstore 0 (cageHealCalldataMem healRad mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    add,
    swap2,
    pop,
    pop,
    push1 kissHealOutSize,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Heal (by decide) (by evm_ov),
    dup1,
    dup4,
    sub,
    dup2,
    push1 kissHealOutSize,
    dup8,
    dup1]
  have hpc3280 :
      (⟨3238⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ =
        ⟨3280⟩ := by
    decide +native
  rw [hpc3280] at rd3280
  exact ⟨_, _, by
    simpa [target, kissDaiTargetWord, kissHealSelectorShifted, kissHealSelector,
      kissHealSelectorMem, cageHealCalldataMem, kissHealOutPtr, kissHealOutSize,
      kissHealInSize, kissHealEndPtr,
      show UInt256.shiftLeft (UInt256.land kissHealSelector ⟨4294967295⟩) ⟨224⟩ =
        kissHealSelectorShifted from by decide +native,
      show UInt256.sub (⟨164⟩ : UInt256) ⟨128⟩ = ⟨36⟩ from by decide +native,
      show UInt256.sub ((⟨4⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨4⟩
        from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide +native]
      using rd3280⟩

theorem RD.vowCageHealNoCode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {healRad : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3238⟩
      (healRad :: kissHealSelector :: kissDaiTargetWord acc.2 ee :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 ee) = ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  obtain ⟨_, _, rd3280⟩ := RD.vowCageHealExtcodesizeGuard rd hmem hread64 hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3280⟩) (okPc := ⟨3292⟩)
    rd3280 hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vowCageHealCallSetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {healRad : UInt256} {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3238⟩
      (healRad :: kissHealSelector :: kissDaiTargetWord acc.2 ee :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 ee) ≠ ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨3295⟩
      (gasWord :: kissDaiTargetWord acc.2 ee :: kissHealOutSize ::
        kissHealOutPtr :: kissHealInSize :: kissHealOutPtr :: kissHealOutSize ::
        kissHealEndPtr :: kissHealSelector :: kissDaiTargetWord acc.2 ee :: R)
      (cageHealCalldataMem healRad mem) (UInt256.ofNat 6) rdata acc k' C' := by
  obtain ⟨_, _, rd3280⟩ := RD.vowCageHealExtcodesizeGuard rd hmem hread64 hov
  obtain ⟨gasWord, k3295, C3295, rd3295⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3280⟩) (okPc := ⟨3292⟩) rd3280
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp; omega)
  exact ⟨gasWord, k3295, C3295, by simpa using rd3295⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowCageHealPostCall
    {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {cA_call : Batteries.RBSet AccountAddress compare}
    {mem rdata : ByteArray} {k C : ℕ} {healRad : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3238⟩
      (healRad :: kissHealSelector :: kissDaiTargetWord σCall I :: R)
      mem (UInt256.ofNat 6) rdata (cA_call, σCall) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (kissDaiTargetWord σCall I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true)
    (hov : R.length + 15 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3296⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissHealEndPtr :: kissHealSelector ::
          kissDaiTargetWord σCall I :: R)
        (cageHealCalldataMem healRad mem) (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σCall
          createdAccounts := cA_call }
        (EVM.address (kissVatAddress σCall I)) "heal" 0
        [.int (Int.ofNat healRad.toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'
              substate := A'
              createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3295⟩ :=
    RD.vowCageHealCallSetup
      (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (ee := I)
      (acc := (cA_call, σCall))
      (healRad := healRad)
      (R := R)
      rd hmem hread64 hcodeSize hov
  obtain ⟨cA', σ', z, out, A_in, callGas, k3296, C3296, hΘpack, rd3296raw,
      houtsz⟩ :=
    RD.call rd3295 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmCall := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σCall
    createdAccounts := cA_call }
  refine ⟨cA', σ', z, out, A', k3296, C3296, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          kissHealOutPtr.toNat kissHealInSize.toNat)
          kissHealOutPtr.toNat kissHealOutSize.toNat) = UInt256.ofNat 6 := by
      rw [kissHealInSize_eq]
      unfold kissHealOutPtr kissHealOutSize
      decide +native
    have hmin : (min kissHealOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold kissHealOutSize
      rfl
    have rd3296 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3296⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissHealEndPtr :: kissHealSelector ::
          kissDaiTargetWord σCall I :: R)
        (out.write 0 (cageHealCalldataMem healRad mem) kissHealOutPtr.toNat
          (min kissHealOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k3296 C3296 :=
      haw ▸ rd3296raw
    rw [hmin, byteArray_write_len_zero] at rd3296
    exact rd3296
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := kissDaiTargetWord σCall I)
      (mem := cageHealCalldataMem healRad mem)
      (inOff := kissHealOutPtr) (inSize := kissHealInSize)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmCall, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      (kissVatAddress_eq_daiTarget σCall I)
      (cageHealEncode_eq healRad hmem) ?_
    simpa [evmCall, initState, hperm] using hΘ

theorem RD.vowCageHealCallFailure {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3296⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3296⟩) (okPc := ⟨3312⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) hosz hov

theorem RD.vowCageHealCallSuccessCleanup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 ret : UInt256}
    {R : List UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3296⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: ret :: R) mem aw o acc k C)
    (hret : (D_J vowBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ret R mem aw o acc k' C' := by
  obtain ⟨_, _, rd3314⟩ := RD.solcCallSuccessGuardOk
    (pc := ⟨3296⟩) (okPc := ⟨3312⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd3315 := rd3314.pop (by decide +native) (by simp; omega)
  have rd3316 := rd3315.pop (by decide +native) (by simp; omega)
  have rd3317 := rd3316.pop (by decide +native) (by simp; omega)
  exact ⟨_, _, rd3317.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vowCageHealCallSuccess {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {target sel : UInt256}
    (rd : RD vowBytecode ee g s0 ⟨3296⟩
      (⟨1⟩ :: kissHealEndPtr :: kissHealSelector :: target :: ⟨412⟩ :: sel :: [])
      mem aw o acc k C) :
    RDret vowBytecode g s0 acc ByteArray.empty := by
  obtain ⟨_, _, rd412⟩ := RD.vowCageHealCallSuccessCleanup rd
    (by jump_dest) (by simp)
  have rd413 := rd412.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd413 (by decide +native) (by simp)

end Benchmarks.Dss.Vow
