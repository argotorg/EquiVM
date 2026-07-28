import Benchmarks.Dss.Vow.CageBody
import Benchmarks.Dss.Vow.FlapBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `cage()` runtime assembly helpers -/

def cageFirstVatDaiStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [.storage flapperRef]
    "flapperDai" (perm := false)

def cageFlapperCageStmts : List Stmt :=
  checkedExternalCallStmts (.storage flapperRef) "cage" (.intLit 0)
    [.var "flapperDai"] "_flapCageRet"

def cageAfterFlapperStmts : List Stmt :=
  cageFlopperCageStmts ++ cageVatDaiStmts ++ cageVatSinStmts ++ cageMinStmts ++
  cageVatHealStmts

theorem returnWrite_size_164 {base : ByteArray} (o : ByteArray) (L : ℕ)
    (hbase : base.size = 164) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen o base 128 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem returnWrite_read64 {base : ByteArray} (o : ByteArray) (L : ℕ)
    (hbase : base.size = 164)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen o base 128 L 64 (by omega) hLo (by rw [hbase]; omega)
      (by omega), hread64]

theorem returnWrite_read128_32 {base : ByteArray} (o : ByteArray)
    (hbase : base.size = 164) (ho32 : 32 ≤ o.size) :
    (o.write 0 base 128 32).readWithPadding 128 32 = o.extract 0 32 :=
  write32_read_back o base 128 ho32 (by rw [hbase]; omega)

theorem cageFirstVatDaiNoCode
    {evm : EVM.State}
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      cageFirstVatDaiStmts .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := ∅ } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := ∅) (by simp)
  have hguard :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_kissVatCodeGuard_false hvat hvatNoCode
  simp only [cageFirstVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem cageFirstVatDaiCallFailure
    {evm evmDai : EVM.State} {outDai : ByteArray}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (false, evmDai, outDai)
        false) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      cageFirstVatDaiStmts .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := ∅ } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := ∅) (by simp)
  have hguard :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hflapper :
      evalExpr? config { contract := contract, locals := ∅ } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa using evalExpr_flapFlapperStorage (evm := evm) (locals := ∅) (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := ∅ } evm [.storage flapperRef] =
        .ok [.address (flapFlapperAddressOf evm)] := by
    simp [evalExprs?, hflapper, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := ∅ } evm
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [.storage flapperRef]
          "flapperDai" (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallDai
  simp only [cageFirstVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageFirstVatDaiReturnDecodeFailure
    {evm evmDai : EVM.State} {outDai : ByteArray}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (true, evmDai, outDai)
        false)
    (hdecDai : config.externalABI.decode? "dai" outDai = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      cageFirstVatDaiStmts .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := ∅ } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := ∅) (by simp)
  have hguard :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hflapper :
      evalExpr? config { contract := contract, locals := ∅ } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa using evalExpr_flapFlapperStorage (evm := evm) (locals := ∅) (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := ∅ } evm [.storage flapperRef] =
        .ok [.address (flapFlapperAddressOf evm)] := by
    simp [evalExprs?, hflapper, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := ∅ } evm
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [.storage flapperRef]
          "flapperDai" (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargs hcallDai hdecDai
  simp only [cageFirstVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageFirstVatDaiSuccess
    {evm evmDai : EVM.State} {outDai : ByteArray} {flapperDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)]) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      cageFirstVatDaiStmts
      (.ok { contract := contract, locals := cageLocalsFlapperDai flapperDai }
        evmDai) := by
  have hvat :
      evalExpr? config { contract := contract, locals := ∅ } evm (.storage vatRef) =
        .ok (.address (cageVatAddressOf evm)) := by
    simpa [cageVatAddressOf] using
      evalExpr_kissVatStorage (evm := evm) (locals := ∅) (by simp)
  have hguard :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvat hvatCode
  have hflapper :
      evalExpr? config { contract := contract, locals := ∅ } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa using evalExpr_flapFlapperStorage (evm := evm) (locals := ∅) (by simp)
  have hargs :
      evalExprs? config { contract := contract, locals := ∅ } evm [.storage flapperRef] =
        .ok [.address (flapFlapperAddressOf evm)] := by
    simp [evalExprs?, hflapper, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := ∅ } evm
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [.storage flapperRef]
          "flapperDai" (perm := false))
        (.ok { contract := contract, locals := cageLocalsFlapperDai flapperDai }
          evmDai) := by
    simpa [cageLocalsFlapperDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs
        hcallDai hdecDai
  simp only [cageFirstVatDaiStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consNormal hcallStmt ExecBlock.nil)

theorem cageFlapperCageNoCode
    {evm : EVM.State} {flapperDai : UInt256}
    (hflapperNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := cageLocalsFlapperDai flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageFlapperCageStmts .reverted := by
  intro locals
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa [locals, cageLocalsFlapperDai] using
      evalExpr_flapFlapperStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage flapperRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_extCodeGuard_false hflapper hflapperNoCode
  simp only [cageFlapperCageStmts, checkedExternalCallStmts]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem cageFlapperCageCallFailure
    {evm evmFlap : EVM.State} {outFlap : ByteArray} {flapperDai : UInt256}
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evm (EVM.address (flapFlapperAddressOf evm))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (false, evmFlap, outFlap)
        true) :
    let locals := cageLocalsFlapperDai flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageFlapperCageStmts .reverted := by
  intro locals
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa [locals, cageLocalsFlapperDai] using
      evalExpr_flapFlapperStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage flapperRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_extCodeGuard_true hflapper hflapperCode
  have harg :
      evalExpr? config { contract := contract, locals := locals } evm (.var "flapperDai") =
        .ok (.int (Int.ofNat flapperDai.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "flapperDai")
      (value := flapperDai) (by simp [locals])
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "flapperDai"] =
        .ok [.int (Int.ofNat flapperDai.toNat)] := by
    simp [evalExprs?, harg, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage flapperRef) "cage" (.intLit 0)
          [.var "flapperDai"] "_flapCageRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hflapper (by simp [evalExpr?, pure])
      hargs hcallFlap
  simp only [cageFlapperCageStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hcallStmt)

theorem cageFlapperCageSuccess
    {evm evmFlap : EVM.State} {outFlap : ByteArray} {flapperDai : UInt256}
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evm (EVM.address (flapFlapperAddressOf evm))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true) :
    let locals := cageLocalsFlapperDai flapperDai
    ExecBlock config { contract := contract, locals := locals } evm
      cageFlapperCageStmts
      (.ok { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
        evmFlap) := by
  intro locals
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa [locals, cageLocalsFlapperDai] using
      evalExpr_flapFlapperStorage (evm := evm) (locals := locals)
        (by simp [locals, cageLocalsFlapperDai])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage flapperRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_extCodeGuard_true hflapper hflapperCode
  have harg :
      evalExpr? config { contract := contract, locals := locals } evm (.var "flapperDai") =
        .ok (.int (Int.ofNat flapperDai.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "flapperDai")
      (value := flapperDai) (by simp [locals])
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "flapperDai"] =
        .ok [.int (Int.ofNat flapperDai.toNat)] := by
    simp [evalExprs?, harg, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.externalCall (.storage flapperRef) "cage" (.intLit 0)
          [.var "flapperDai"] "_flapCageRet")
        (.ok { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
          evmFlap) := by
    simpa [locals, cageLocalsAfterFlapCage, cageDecodeVoid_ok, collapseReturns] using
      ExecStmt.externalCallSuccess hflapper (by simp [evalExpr?, pure]) hargs
        hcallFlap (cageDecodeVoid_ok outFlap)
  simp only [cageFlapperCageStmts, checkedExternalCallStmts]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consNormal hcallStmt ExecBlock.nil)

theorem cageFirstDaiFlapperNoCode
    {evm : EVM.State}
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
  have hfirst := cageFirstVatDaiNoCode (evm := evm) hvatNoCode
  exact.execBlock_append_term (s2 := cageFlapperCageStmts) hfirst
    (by intro f e h; cases h)

theorem cageFirstDaiFlapperCallFailure
    {evm evmDai : EVM.State} {outDai : ByteArray}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (false, evmDai, outDai)
        false) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
  have hfirst := cageFirstVatDaiCallFailure (evm := evm) (evmDai := evmDai)
    (outDai := outDai) hvatCode hcallDai
  exact.execBlock_append_term (s2 := cageFlapperCageStmts) hfirst
    (by intro f e h; cases h)

theorem cageFirstDaiFlapperReturnDecodeFailure
    {evm evmDai : EVM.State} {outDai : ByteArray}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (true, evmDai, outDai)
        false)
    (hdecDai : config.externalABI.decode? "dai" outDai = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
  have hfirst := cageFirstVatDaiReturnDecodeFailure (evm := evm) (evmDai := evmDai)
    (outDai := outDai) hvatCode hcallDai hdecDai
  exact.execBlock_append_term (s2 := cageFlapperCageStmts) hfirst
    (by intro f e h; cases h)

theorem cageFirstDaiFlapperCageNoCode
    {evm evmDai : EVM.State} {outDai : ByteArray} {flapperDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperNoCode :
      (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
  have hfirst := cageFirstVatDaiSuccess (evm := evm) (evmDai := evmDai)
    (outDai := outDai) (flapperDai := flapperDai) hvatCode hcallDai hdecDai
  have hflapper := cageFlapperCageNoCode (evm := evmDai)
    (flapperDai := flapperDai) hflapperNoCode
  exact.execBlock_append hfirst hflapper

theorem cageFirstDaiFlapperCageCallFailure
    {evm evmDai evmFlap : EVM.State} {outDai outFlap : ByteArray}
    {flapperDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (false, evmFlap, outFlap)
        true) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
  have hfirst := cageFirstVatDaiSuccess (evm := evm) (evmDai := evmDai)
    (outDai := outDai) (flapperDai := flapperDai) hvatCode hcallDai hdecDai
  have hflapper := cageFlapperCageCallFailure (evm := evmDai) (evmFlap := evmFlap)
    (outFlap := outFlap) (flapperDai := flapperDai) hflapperCode hcallFlap
  exact.execBlock_append hfirst hflapper

theorem cageFirstDaiFlapperCageSuccess
    {evm evmDai evmFlap : EVM.State} {outDai outFlap : ByteArray}
    {flapperDai : UInt256}
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "dai" 0 [.address (flapFlapperAddressOf evm)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (cageFirstVatDaiStmts ++ cageFlapperCageStmts)
      (.ok { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
        evmFlap) := by
  have hfirst := cageFirstVatDaiSuccess (evm := evm) (evmDai := evmDai)
    (outDai := outDai) (flapperDai := flapperDai) hvatCode hcallDai hdecDai
  have hflapper := cageFlapperCageSuccess (evm := evmDai) (evmFlap := evmFlap)
    (outFlap := outFlap) (flapperDai := flapperDai) hflapperCode hcallFlap
  exact.execBlock_append hfirst hflapper

theorem cageSourceFirstDaiNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatNoCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
    exact cageFirstDaiFlapperNoCode (evm := evmAsh)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatNoCode)
  have hprefix :=.execBlock_append hclear hfirst
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++ cageAfterFlapperStmts)
        .reverted :=
   .execBlock_append_term (s2 := cageAfterFlapperStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceFirstDaiCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {outDai : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (false, evmDai, outDai)
        false) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
    exact cageFirstDaiFlapperCallFailure (evm := evmAsh) (evmDai := evmDai)
      (outDai := outDai)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
  have hprefix :=.execBlock_append hclear hfirst
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++ cageAfterFlapperStmts)
        .reverted :=
   .execBlock_append_term (s2 := cageAfterFlapperStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceFirstDaiReturnDecodeFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {outDai : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai : config.externalABI.decode? "dai" outDai = none) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
    exact cageFirstDaiFlapperReturnDecodeFailure (evm := evmAsh) (evmDai := evmDai)
      (outDai := outDai)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
      hdecDai
  have hprefix :=.execBlock_append hclear hfirst
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++ cageAfterFlapperStmts)
        .reverted :=
   .execBlock_append_term (s2 := cageAfterFlapperStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceFlapperCageNoCode
    {cA gh bl σ σ₀ A I} {g flapperDai : UInt256}
    {evmDai : EVM.State} {outDai : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperNoCode :
      (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
    exact cageFirstDaiFlapperCageNoCode (evm := evmAsh) (evmDai := evmDai)
      (outDai := outDai) (flapperDai := flapperDai)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
      hdecDai hflapperNoCode
  have hprefix :=.execBlock_append hclear hfirst
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++ cageAfterFlapperStmts)
        .reverted :=
   .execBlock_append_term (s2 := cageAfterFlapperStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceFlapperCageCallFailure
    {cA gh bl σ σ₀ A I} {g flapperDai : UInt256}
    {evmDai evmFlap : EVM.State} {outDai outFlap : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (false, evmFlap, outFlap)
        true) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts) .reverted := by
    exact cageFirstDaiFlapperCageCallFailure (evm := evmAsh) (evmDai := evmDai)
      (evmFlap := evmFlap) (outDai := outDai) (outFlap := outFlap)
      (flapperDai := flapperDai)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
      hdecDai hflapperCode hcallFlap
  have hprefix :=.execBlock_append hclear hfirst
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        ((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++ cageAfterFlapperStmts)
        .reverted :=
   .execBlock_append_term (s2 := cageAfterFlapperStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceFlopperCageNoCode
    {cA gh bl σ σ₀ A I} {g flapperDai : UInt256}
    {evmDai evmFlap : EVM.State} {outDai outFlap : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperNoCode :
      (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts)
        (.ok { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
          evmFlap) := by
    exact cageFirstDaiFlapperCageSuccess (evm := evmAsh) (evmDai := evmDai)
      (evmFlap := evmFlap) (outDai := outDai) (outFlap := outFlap)
      (flapperDai := flapperDai)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
      hdecDai hflapperCode hcallFlap
  have hflopper :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
        evmFlap cageFlopperCageStmts .reverted :=
    cageFlopperCageNoCode (evm := evmFlap) (flapperDai := flapperDai)
      hflopperNoCode
  have hprefix :=.execBlock_append
    (Reasoning.Theory.execBlock_append hclear hfirst) hflopper
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++
          cageFlopperCageStmts) ++
          cageVatDaiStmts ++ cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
        .reverted :=
   .execBlock_append_term
      (s2 := cageVatDaiStmts ++ cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem cageSourceFlopperCageCallFailure
    {cA gh bl σ σ₀ A I} {g flapperDai : UInt256}
    {evmDai evmFlap evmFlop : EVM.State} {outDai outFlap outFlop : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩)
    (hvatCode :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (false, evmFlop, outFlop) true) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      cageTransition.body .reverted := by
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have hclear :
      ExecBlock config { contract := contract, locals := locals } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ])
        (.ok { contract := contract, locals := locals } evmAsh) := by
    simpa [locals, evm0, evmLive, evmSin, evmAsh] using
      vowCageSourceClearPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evmAsh
        (cageFirstVatDaiStmts ++ cageFlapperCageStmts)
        (.ok { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
          evmFlap) := by
    exact cageFirstDaiFlapperCageSuccess (evm := evmAsh) (evmDai := evmDai)
      (evmFlap := evmFlap) (outDai := outDai) (outFlap := outFlap)
      (flapperDai := flapperDai)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatCode)
      (by simpa [evm0, evmLive, evmSin, evmAsh] using hcallDai)
      hdecDai hflapperCode hcallFlap
  have hflopper :
      ExecBlock config
        { contract := contract, locals := cageLocalsAfterFlapCage flapperDai }
        evmFlap cageFlopperCageStmts .reverted :=
    cageFlopperCageCallFailure (evm := evmFlap) (evmFlop := evmFlop)
      (outFlop := outFlop) (flapperDai := flapperDai) hflopperCode hcallFlop
  have hprefix :=.execBlock_append
    (Reasoning.Theory.execBlock_append hclear hfirst) hflopper
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        (((.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
          .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
          [ .assign .storage liveRef (.intLit 0),
            .assign .storage SinRef (.intLit 0),
            .assign .storage AshRef (.intLit 0) ] ++
          cageFirstVatDaiStmts ++ cageFlapperCageStmts) ++
          cageFlopperCageStmts) ++
          cageVatDaiStmts ++ cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
        .reverted :=
   .execBlock_append_term
      (s2 := cageVatDaiStmts ++ cageVatSinStmts ++ cageMinStmts ++ cageVatHealStmts)
      (by simpa [List.append_assoc] using hprefix)
      (by intro f e h; cases h)
  have hbody := ExecFuncBody.execBlockRevert hblock
  simpa [ExecTransitionBody, cageTransition, cageAfterAuth, cageAfterLive, nonpayable, auth,
    cageFirstVatDaiStmts, cageFlapperCageStmts, cageAfterFlapperStmts, cageFlopperCageStmts,
    cageVatDaiStmts, cageVatSinStmts, cageMinStmts, cageVatHealStmts, locals, evm0,
    List.append_assoc] using hbody

theorem RD.vowCageFirstDaiPostCallDecodeOk
    {cA gh bl σ σ₀ A I} {g ret target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outDai : ByteArray} {k C : ℕ} {R : List UInt256}
    (rd2754 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord acc.2 I ::
        flapCageSelectorWord :: target :: ret :: R)
      (outDai.write 0 (vatDaiCalldataMemFor target mem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
      (UInt256.ofNat 6) outDai acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ outDai.size) (hosz : outDai.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024) :
    let flapperDai := UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32))
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2795⟩
      (flapperDai :: flapCageSelectorWord :: target :: ret :: R)
      (outDai.write 0 (vatDaiCalldataMemFor target mem) 128 32)
      (UInt256.ofNat 6) outDai acc k' C' := by
  intro flapperDai
  let base := vatDaiCalldataMemFor target mem
  have hbase : base.size = 164 := by
    simpa [base] using vatDaiCalldataMemFor_size_of_size96 target hmem
  have hbaseRead64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [base] using vatDaiCalldataMemFor_read64_of_size96 target hmem hread64
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd2754Write := rd2754
  rw [hmin] at rd2754Write
  obtain ⟨_, _, rd2772⟩ :=
    RD.vowCageFirstDaiCallSuccessToDecode rd2754Write (by simp; omega)
  have hmemWrite :
      (outDai.write 0 base 128 32).size = 164 :=
    returnWrite_size_164 outDai 32 hbase (by omega) ho32
  have hread64Write :
      (outDai.write 0 base 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    returnWrite_read64 outDai 32 hbase hbaseRead64 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (outDai.write 0 base 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 base 128 32).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (outDai.write 0 base 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 base 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥ (outDai.write 0 base 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmemWrite]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      returnWrite_read128_32 outDai hbase ho32]
  obtain ⟨k', C', rd2795Raw⟩ :=
    RD.vowCageFirstDaiReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32)))
      rd2772 ho32 hosz hmload64 hmload128 (by simp; omega)
  exact ⟨k', C', by simpa [flapperDai, base] using rd2795Raw⟩

theorem vowCageFirstDaiNoCodeBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hliveEvm : vowSlotWord ⟨12⟩ σ_evm I = ⟨1⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord
        (vowCageClearedAccountMap I.codeOwner σ_evm)
        (kissDaiTargetWord (vowCageClearedAccountMap I.codeOwner σ_evm) I) =
          ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σClearedEvm := vowCageClearedAccountMap I.codeOwner σ_evm
  let σClearedSolm := vowCageClearedAccountMap I.codeOwner σ_solm
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    vowDispatch_cage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_cage hsz
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, rdClear⟩ :=
    vowCageReachAfterClear (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hauthEvm hliveEvm
  obtain ⟨_, _, rdLoads⟩ := RD.vowCageFirstDaiLoadTargets
    (R := [vowSelWord I]) rdClear (by simp)
  have hcodeSizeRaw :
      Reasoning.Theory.extCodeSizeWord σClearedEvm
        (UInt256.land solcAddrMask (solcSlotWord σClearedEvm I ⟨1⟩)) = ⟨0⟩ := by
    simpa [σClearedEvm, kissDaiTargetWord, vowSlotWord, solcSlotWord,
      u256_land_comm] using hcodeSize
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageFirstDaiNoCode (R := [vowSelWord I]) rdLoads hmemAuth hread64
      (by simpa [σClearedEvm] using hcodeSizeRaw) (by simp)
  have hauthSolm : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hslot :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (vowCallerWardsSlot I) ⟨0⟩
    exact (by simpa [vowSlotWord] using hslot.symm.trans hauthEvm)
  have hliveSolm : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ := by
    have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
    exact (by simpa [vowSlotWord] using hslot.symm.trans hliveEvm)
  have hClearedAccounts : accountMapEquiv σClearedEvm σClearedSolm := by
    simpa [σClearedEvm, σClearedSolm] using
      accountMapEquiv_vowCageCleared I.codeOwner hAccounts
  have hTargetCleared :
      kissDaiTargetWord σClearedEvm I = kissDaiTargetWord σClearedSolm I := by
    have hslot := accountMapEquiv_storage_findD hClearedAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissDaiTargetWord, vowSlotWord, hslot]
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σClearedSolm
        (kissDaiTargetWord σClearedSolm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hClearedAccounts
        (kissDaiTargetWord σClearedEvm I)
    rw [← hTargetCleared, ← hsame]
    simpa [σClearedEvm] using hcodeSize
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
  let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
  let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
  have haddrCage :
      cageVatAddressOf evmAsh = kissVatAddress σClearedSolm I := by
    have howner : evmAsh.executionEnv.codeOwner = I.codeOwner := by
      simp [evmAsh, evmSin, evmLive, evm0, initState, storageStore_executionEnv]
    have hload :
        Solm.EVM.storageLoad evmAsh I.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ evmAsh.accountMap I := by
      simpa [howner] using flapStorageLoad_codeOwner_eq_vowSlotWord evmAsh I ⟨1⟩ howner
    simp only [cageVatAddressOf, kissVatAddress, vowAddressReturnWord]
    rw [howner, hload]
    simp [
      σClearedSolm, evmAsh, evmSin, evmLive, evm0, initState, storageStore_accountMap,
      vowCageClearedAccountMap]
  have haddr :
      cageVatAddressOf evmAsh = AccountAddress.ofUInt256 (kissDaiTargetWord σClearedSolm I) :=
    haddrCage.trans (kissVatAddress_eq_daiTarget_account σClearedSolm I)
  have hvatNoCode :
      (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    have hzero :=
      extCodeSizeWord_zero_lookup_code_zero
        (σ := σClearedSolm) (target := kissDaiTargetWord σClearedSolm I)
        (addr := cageVatAddressOf evmAsh) haddr hcodeSizeSolm
    simpa [evmAsh, evmSin, evmLive, evm0, initState, State.lookupAccount,
      storageStore_accountMap, σClearedSolm, vowCageClearedAccountMap] using hzero
  have hbody := cageSourceFirstDaiNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hwv hauthSolm hliveSolm
    (by simpa [evm0, evmLive, evmSin, evmAsh] using hvatNoCode)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageFirstDaiCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g ret target flapper : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai : EVM.State} {mem outDai rdata : ByteArray} {aw : UInt256}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd2754 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: ⟨2734234354⟩ ::
        flapper :: ret :: R)
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 11 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (false, evmDai, outDai)
        false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageFirstDaiCallFailure rd2754 hrdataSize (by simpa using hov)
  have hbody := cageSourceFirstDaiCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (outDai := outDai) hwv hauth hlive hvatCode hcallDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageFirstDaiDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g ret target flapper : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai : EVM.State} {base outDai : ByteArray} {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd2754 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2754⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: ⟨2734234354⟩ ::
        flapper :: ret :: R)
      (outDai.write 0 base 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
      (UInt256.ofNat 6) outDai acc k C)
    (hbase : base.size = 164)
    (hbaseRead64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hosz : outDai.size < UInt256.size)
    (hshort : outDai.size < 32)
    (hov : R.length + 12 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat = outDai.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd2754Short := rd2754
  rw [hmin] at rd2754Short
  obtain ⟨_, _, rd2772⟩ :=
    RD.vowCageFirstDaiCallSuccessToDecode rd2754Short (by simp; omega)
  have hmemWrite :
      (outDai.write 0 base 128 outDai.size).size = 164 :=
    returnWrite_size_164 outDai outDai.size hbase (by omega) (by omega)
  have hread64Write :
      (outDai.write 0 base 128 outDai.size).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    returnWrite_read64 outDai outDai.size hbase hbaseRead64 (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (outDai.write 0 base 128 outDai.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 base 128 outDai.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageFirstDaiReturnDecodeShortReverts rd2772 hshort hosz hmload64
      (by simp; omega)
  have hdecDai : config.externalABI.decode? "dai" outDai = none :=
    kissDaiDecode_none_short hshort
  have hbody := cageSourceFirstDaiReturnDecodeFailure (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (outDai := outDai) hwv hauth hlive hvatCode hcallDai
    hdecDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageFlapperCageNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai target ret : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai : EVM.State} {mem outDai rdata : ByteArray} {k C : ℕ}
    {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd2795 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2795⟩
      (flapperDai :: flapCageSelectorWord :: target :: ret :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord acc.2 target = ⟨0⟩)
    (hov : R.length + 13 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperNoCode :
      (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageFlapperCageNoCode rd2795 hmem hread64 hcodeSize (by simp; omega)
  have hbody := cageSourceFlapperCageNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (evmDai := evmDai) (outDai := outDai)
    hwv hauth hlive hvatCode hcallDai hdecDai hflapperNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageFlapperCageCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai target ret : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap : EVM.State} {mem outDai outFlap rdata : ByteArray}
    {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd2860 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2860⟩
      (⟨0⟩ :: flapCageEndPtr :: flapCageSelectorWord :: target :: ret :: R)
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 9 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (false, evmFlap, outFlap)
        true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageFlapperCageCallFailure rd2860 hrdataSize (by simp; omega)
  have hbody := cageSourceFlapperCageCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (outDai := outDai) (outFlap := outFlap) hwv hauth hlive hvatCode hcallDai
    hdecDai hflapperCode hcallFlap
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageFlopperCageNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai ret : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap : EVM.State} {mem outDai outFlap rdata : ByteArray}
    {k C : ℕ} {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd2881 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2881⟩
      (ret :: R) mem (UInt256.ofNat 6) rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (vowAddressReturnWord ⟨3⟩ acc.2 I) = ⟨0⟩)
    (hov : R.length + 15 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperNoCode :
      (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageFlopperCageNoCode rd2881 hmem hread64 hcodeSize hov
  have hbody := cageSourceFlopperCageNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (outDai := outDai) (outFlap := outFlap) hwv hauth hlive hvatCode hcallDai
    hdecDai hflapperCode hcallFlap hflopperNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowCageFlopperCageCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g flapperDai target ret : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmFlap evmFlop : EVM.State}
    {mem outDai outFlap outFlop rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {R : List UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hlive : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (rd2964 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2964⟩
      (⟨0⟩ :: flopCageEndPtr :: flopCageSelectorWord :: target :: ret :: R)
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 9 ≤ 1024)
    (hvatCode :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (cageVatAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨12⟩ ⟨0⟩
      let evmSin := Solm.EVM.storageStore evmLive I.codeOwner ⟨5⟩ ⟨0⟩
      let evmAsh := Solm.EVM.storageStore evmSin I.codeOwner ⟨6⟩ ⟨0⟩
      typedCallViaEVM config evmAsh (EVM.address (cageVatAddressOf evmAsh))
        "dai" 0 [.address (flapFlapperAddressOf evmAsh)] (true, evmDai, outDai)
        false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat flapperDai.toNat)])
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (flapFlapperAddressOf evmDai)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlap :
      typedCallViaEVM config evmDai (EVM.address (flapFlapperAddressOf evmDai))
        "cage" 0 [.int (Int.ofNat flapperDai.toNat)] (true, evmFlap, outFlap)
        true)
    (hflopperCode :
      0 < (UInt256.ofNat
        ((evmFlap.lookupAccount (flopFlopperAddressOf evmFlap)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallFlop :
      typedCallViaEVM config evmFlap (EVM.address (flopFlopperAddressOf evmFlap))
        "cage" 0 [] (false, evmFlop, outFlop) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.vowCageFlopperCageCallFailure rd2964 hrdataSize (by simp; omega)
  have hbody := cageSourceFlopperCageCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (flapperDai := flapperDai) (evmDai := evmDai) (evmFlap := evmFlap)
    (evmFlop := evmFlop) (outDai := outDai) (outFlap := outFlap)
    (outFlop := outFlop) hwv hauth hlive hvatCode hcallDai hdecDai hflapperCode
    hcallFlap hflopperCode hcallFlop
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem cageMinHealLeftNoCode
    {evm : EVM.State} {flapperDai vatDai vatSin : UInt256}
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      (cageMinStmts ++ cageVatHealStmts) .reverted := by
  intro locals
  have hmin := cageMinLeft (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (evm := evm) hle
  have hheal := cageVatHealNoCode (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (healRad := vatDai) (evm := evm) hvatNoCode
  exact.execBlock_append hmin hheal

theorem cageMinHealRightNoCode
    {evm : EVM.State} {flapperDai vatDai vatSin : UInt256}
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      (cageMinStmts ++ cageVatHealStmts) .reverted := by
  intro locals
  have hmin := cageMinRight (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (evm := evm) hlt
  have hheal := cageVatHealNoCode (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (healRad := vatSin) (evm := evm) hvatNoCode
  exact.execBlock_append hmin hheal

theorem cageMinHealLeftCallFailure
    {evm evmHeal : EVM.State} {outHeal : ByteArray}
    {flapperDai vatDai vatSin : UInt256}
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "heal" 0 [.int (Int.ofNat vatDai.toNat)] (false, evmHeal, outHeal) true) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      (cageMinStmts ++ cageVatHealStmts) .reverted := by
  intro locals
  have hmin := cageMinLeft (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (evm := evm) hle
  have hheal := cageVatHealCallFailure (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (healRad := vatDai) (evm := evm) (evmHeal := evmHeal)
    (outHeal := outHeal) hvatCode hcallHeal
  exact.execBlock_append hmin hheal

theorem cageMinHealRightCallFailure
    {evm evmHeal : EVM.State} {outHeal : ByteArray}
    {flapperDai vatDai vatSin : UInt256}
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "heal" 0 [.int (Int.ofNat vatSin.toNat)] (false, evmHeal, outHeal) true) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      (cageMinStmts ++ cageVatHealStmts) .reverted := by
  intro locals
  have hmin := cageMinRight (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (evm := evm) hlt
  have hheal := cageVatHealCallFailure (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (healRad := vatSin) (evm := evm) (evmHeal := evmHeal)
    (outHeal := outHeal) hvatCode hcallHeal
  exact.execBlock_append hmin hheal

theorem cageMinHealLeftSuccess
    {evm evmHeal : EVM.State} {outHeal : ByteArray}
    {flapperDai vatDai vatSin : UInt256}
    (hle : vatDai.toNat ≤ vatSin.toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "heal" 0 [.int (Int.ofNat vatDai.toNat)] (true, evmHeal, outHeal) true) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      (cageMinStmts ++ cageVatHealStmts)
      (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin vatDai }
        evmHeal) := by
  intro locals
  have hmin := cageMinLeft (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (evm := evm) hle
  have hheal := cageVatHealSuccess (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (healRad := vatDai) (evm := evm) (evmHeal := evmHeal)
    (outHeal := outHeal) hvatCode hcallHeal
  exact.execBlock_append hmin hheal

theorem cageMinHealRightSuccess
    {evm evmHeal : EVM.State} {outHeal : ByteArray}
    {flapperDai vatDai vatSin : UInt256}
    (hlt : vatSin.toNat < vatDai.toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (cageVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evm (EVM.address (cageVatAddressOf evm))
        "heal" 0 [.int (Int.ofNat vatSin.toNat)] (true, evmHeal, outHeal) true) :
    let locals := cageLocalsAfterVatSin flapperDai vatDai vatSin
    ExecBlock config { contract := contract, locals := locals } evm
      (cageMinStmts ++ cageVatHealStmts)
      (.ok { contract := contract, locals := cageLocalsAfterHealRet flapperDai vatDai vatSin vatSin }
        evmHeal) := by
  intro locals
  have hmin := cageMinRight (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (evm := evm) hlt
  have hheal := cageVatHealSuccess (flapperDai := flapperDai) (vatDai := vatDai)
    (vatSin := vatSin) (healRad := vatSin) (evm := evm) (evmHeal := evmHeal)
    (outHeal := outHeal) hvatCode hcallHeal
  exact.execBlock_append hmin hheal

end Benchmarks.Dss.Vow
