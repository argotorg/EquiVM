import Benchmarks.Dss.Vow.FlopAsh

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flop()` source continuations for the final `flopper.kick(...)` call -/

def flopPrefixToDaiStmts : List Stmt :=
  nonpayable ++
  checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
    (perm := false) ++
  [ .internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin",
    .internalCall "sub" [.var "freeSin", .storage AshRef] "flopDebt",
    .require (.binary .le (.storage sumpRef) (.var "flopDebt")) ] ++
  checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
    (perm := false)

def flopPostDaiTailStmts : List Stmt :=
  [ .require (.binary .eq (.var "vatDai") (.intLit 0)) ] ++
  flopAshAssignStmts ++ flopKickAndReturnStmts

theorem flopPrefixToDaiSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal vatDai : UInt256}
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
        some [.int (Int.ofNat vatDai.toNat)]) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    ExecBlock config { contract := contract, locals := locals } evm0 flopPrefixToDaiStmts
      (.ok { contract := contract, locals := locals4 } evmDai) := by
  intro locals evm0 locals4
  let locals1 := flopLocalsVatSin vatSin
  let locals2 := flopLocalsVatSinFreeSin vatSin freeSin
  let locals3 := flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt
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
  simp only [flopPrefixToDaiStmts, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  refine ExecBlock.consNormal hcallSinStmt ?_
  refine ExecBlock.consNormal hfreeStmt ?_
  refine ExecBlock.consNormal hdebtStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDebt) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDai) ?_
  exact ExecBlock.consNormal hcallDaiStmt ExecBlock.nil

theorem flopAshAssignThenKickNoCode
    {evmDai : EVM.State}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew : UInt256}
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ = AshValDai)
    (hSumpLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ = SumpValDai)
    (hAshNew : AshNew = AshValDai + SumpValDai)
    (hfit : AshValDai.toNat + SumpValDai.toNat < UInt256.size)
    (hflopperNoCode :
      (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (flopFlopperAddressOf
            (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew))).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai
      (flopAshAssignStmts ++ flopKickAndReturnStmts) .reverted := by
  intro locals4
  let locals5 := flopLocalsVatSinFreeSinDebtDaiAshNew vatSin freeSin flopDebt vatDai AshNew
  let evmAsh := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew
  have hflopperNoCode' :
      (UInt256.ofNat
        ((evmAsh.lookupAccount (flopFlopperAddressOf evmAsh)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [evmAsh] using hflopperNoCode
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
        (.binary .gt (.extCodeSize (.storage flopperRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_extCodeGuard_false hflopper hflopperNoCode'
  have hkickBlock :
      ExecBlock config { contract := contract, locals := locals5 } evmAsh
        flopKickAndReturnStmts .reverted := by
    simp only [flopKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  exact execBlock_append_ok hassignBlock hkickBlock

theorem flopAshAssignThenKickCallFailure
    {evmDai evmKick : EVM.State}
    {outKick : ByteArray}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew DumpVal SumpVal : UInt256}
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
        (false, evmKick, outKick) true) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai
      (flopAshAssignStmts ++ flopKickAndReturnStmts) .reverted := by
  intro locals4
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
        (false, evmKick, outKick) true := by
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
        .reverted := by
    exact ExecStmt.externalCallFailure hflopper (by simp [evalExpr?, pure])
      hargsKick hcallKick'
  have hkickBlock :
      ExecBlock config { contract := contract, locals := locals5 } evmAsh
        flopKickAndReturnStmts .reverted := by
    simp only [flopKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  exact execBlock_append_ok hassignBlock hkickBlock

theorem flopAshAssignThenKickDecodeRevert
    {evmDai evmKick : EVM.State}
    {outKick : ByteArray}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew DumpVal SumpVal : UInt256}
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
    (hdecKick : config.externalABI.decode? "kick" outKick = none) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai
      (flopAshAssignStmts ++ flopKickAndReturnStmts) .reverted := by
  intro locals4
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
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hflopper (by simp [evalExpr?, pure])
      hargsKick hcallKick' hdecKick
  have hkickBlock :
      ExecBlock config { contract := contract, locals := locals5 } evmAsh
        flopKickAndReturnStmts .reverted := by
    simp only [flopKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  exact execBlock_append_ok hassignBlock hkickBlock

theorem evalExpr_flopVatDaiZero
    {evmDai : EVM.State} {vatSin freeSin flopDebt vatDai : UInt256}
    (hvatDaiZero : vatDai = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai } evmDai
      (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) := by
  have hvatDaiVar :
      evalExpr? config
        { contract := contract,
          locals := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmDai)
      (locals := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai)
      (name := "vatDai") (value := vatDai)
      (flopLocalsVatSinFreeSinDebtDai_get_vatDai vatSin freeSin flopDebt vatDai)
  have hzeroNat : vatDai.toNat = 0 := by
    rw [hvatDaiZero]
    rfl
  simp [evalExpr?, EvalResult.bind, bind, hvatDaiVar, evalBinaryOp?, hzeroNat]

theorem flopPostDaiTailNoCode
    {evmDai : EVM.State}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew : UInt256}
    (hvatDaiZero : vatDai = ⟨0⟩)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ = AshValDai)
    (hSumpLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨9⟩ = SumpValDai)
    (hAshNew : AshNew = AshValDai + SumpValDai)
    (hfit : AshValDai.toNat + SumpValDai.toNat < UInt256.size)
    (hflopperNoCode :
      (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (flopFlopperAddressOf
            (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew))).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai flopPostDaiTailStmts
      .reverted := by
  intro locals4
  have hreqVatDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) := by
    simpa [locals4] using
      evalExpr_flopVatDaiZero (evmDai := evmDai) (vatSin := vatSin)
        (freeSin := freeSin) (flopDebt := flopDebt) (vatDai := vatDai) hvatDaiZero
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        (flopAshAssignStmts ++ flopKickAndReturnStmts) .reverted := by
    simpa [locals4] using
      flopAshAssignThenKickNoCode (evmDai := evmDai) (vatSin := vatSin)
        (freeSin := freeSin) (flopDebt := flopDebt) (vatDai := vatDai)
        (AshValDai := AshValDai) (SumpValDai := SumpValDai) (AshNew := AshNew)
        hAshLoadDai hSumpLoadDai hAshNew hfit hflopperNoCode
  simp only [flopPostDaiTailStmts, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreqVatDai) htail

theorem flopPostDaiTailCallFailure
    {evmDai evmKick : EVM.State}
    {outKick : ByteArray}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew DumpVal SumpVal : UInt256}
    (hvatDaiZero : vatDai = ⟨0⟩)
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
        (false, evmKick, outKick) true) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai flopPostDaiTailStmts
      .reverted := by
  intro locals4
  have hreqVatDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) := by
    simpa [locals4] using
      evalExpr_flopVatDaiZero (evmDai := evmDai) (vatSin := vatSin)
        (freeSin := freeSin) (flopDebt := flopDebt) (vatDai := vatDai) hvatDaiZero
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        (flopAshAssignStmts ++ flopKickAndReturnStmts) .reverted := by
    simpa [locals4] using
      flopAshAssignThenKickCallFailure (evmDai := evmDai) (evmKick := evmKick)
        (outKick := outKick) (vatSin := vatSin) (freeSin := freeSin)
        (flopDebt := flopDebt) (vatDai := vatDai) (AshValDai := AshValDai)
        (SumpValDai := SumpValDai) (AshNew := AshNew) (DumpVal := DumpVal)
        (SumpVal := SumpVal) hAshLoadDai hSumpLoadDai hAshNew hfit hDumpLoadAsh
        hSumpLoadAsh hflopperCode hcallKick
  simp only [flopPostDaiTailStmts, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreqVatDai) htail

theorem flopPostDaiTailDecodeRevert
    {evmDai evmKick : EVM.State}
    {outKick : ByteArray}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew DumpVal SumpVal : UInt256}
    (hvatDaiZero : vatDai = ⟨0⟩)
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
    (hdecKick : config.externalABI.decode? "kick" outKick = none) :
    let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai flopPostDaiTailStmts
      .reverted := by
  intro locals4
  have hreqVatDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) := by
    simpa [locals4] using
      evalExpr_flopVatDaiZero (evmDai := evmDai) (vatSin := vatSin)
        (freeSin := freeSin) (flopDebt := flopDebt) (vatDai := vatDai) hvatDaiZero
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        (flopAshAssignStmts ++ flopKickAndReturnStmts) .reverted := by
    simpa [locals4] using
      flopAshAssignThenKickDecodeRevert (evmDai := evmDai) (evmKick := evmKick)
        (outKick := outKick) (vatSin := vatSin) (freeSin := freeSin)
        (flopDebt := flopDebt) (vatDai := vatDai) (AshValDai := AshValDai)
        (SumpValDai := SumpValDai) (AshNew := AshNew) (DumpVal := DumpVal)
        (SumpVal := SumpVal) hAshLoadDai hSumpLoadDai hAshNew hfit hDumpLoadAsh
        hSumpLoadAsh hflopperCode hcallKick hdecKick
  simp only [flopPostDaiTailStmts, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreqVatDai) htail

theorem flopPostDaiTailSuccess
    {evmDai evmKick : EVM.State}
    {outKick : ByteArray}
    {vatSin freeSin flopDebt vatDai AshValDai SumpValDai AshNew DumpVal SumpVal id : UInt256}
    (hvatDaiZero : vatDai = ⟨0⟩)
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
    ExecBlock config { contract := contract, locals := locals4 } evmDai flopPostDaiTailStmts
      (.returned { contract := contract, locals := locals6 } evmKick
        (some [.int (Int.ofNat id.toNat)])) := by
  intro locals4 locals6
  have hreqVatDai :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool true) := by
    simpa [locals4] using
      evalExpr_flopVatDaiZero (evmDai := evmDai) (vatSin := vatSin)
        (freeSin := freeSin) (flopDebt := flopDebt) (vatDai := vatDai) hvatDaiZero
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        (flopAshAssignStmts ++ flopKickAndReturnStmts)
        (.returned { contract := contract, locals := locals6 } evmKick
          (some [.int (Int.ofNat id.toNat)])) := by
    simpa [locals4, locals6] using
      flopAshAssignThenKickSuccess (evmDai := evmDai) (evmKick := evmKick)
        (outKick := outKick) (vatSin := vatSin) (freeSin := freeSin)
        (flopDebt := flopDebt) (vatDai := vatDai) (AshValDai := AshValDai)
        (SumpValDai := SumpValDai) (AshNew := AshNew) (DumpVal := DumpVal)
        (SumpVal := SumpVal) (id := id) hAshLoadDai hSumpLoadDai hAshNew hfit
        hDumpLoadAsh hSumpLoadAsh hflopperCode hcallKick hdecKick
  simp only [flopPostDaiTailStmts, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreqVatDai) htail

theorem flopSourceBlockFromPostDai
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal vatDai : UInt256}
    {result : ExecResult}
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
    (htail :
      let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flopPostDaiTailStmts result) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body result := by
  intro locals evm0
  let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
  have hprefix :
      ExecBlock config { contract := contract, locals := locals } evm0 flopPrefixToDaiStmts
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals, evm0, locals4] using
      flopPrefixToDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmSin := evmSin) (evmDai := evmDai)
        (outSin := outSin) (outDai := outDai) (vatSin := vatSin)
        (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
        (flopDebt := flopDebt) (SumpVal := SumpVal) (vatDai := vatDai)
        hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
        hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai
  have htail' :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flopPostDaiTailStmts result := by
    simpa [locals4] using htail
  have hblock := execBlock_append_ok hprefix htail'
  simpa [flopTransition, flopPrefixToDaiStmts, flopPostDaiTailStmts, flopAshAssignStmts,
    flopKickAndReturnStmts, nonpayable, checkedExternalCallStmts] using hblock

theorem vowFlopSourceKickNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal vatDai AshValDai SumpValDai AshNew :
      UInt256}
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
    (hAshNew : AshNew = AshValDai + SumpValDai)
    (hfit : AshValDai.toNat + SumpValDai.toNat < UInt256.size)
    (hflopperNoCode :
      (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (flopFlopperAddressOf
            (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew))).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flopPostDaiTailStmts .reverted := by
    simpa [locals4] using
      flopPostDaiTailNoCode (evmDai := evmDai) (vatSin := vatSin)
        (freeSin := freeSin) (flopDebt := flopDebt) (vatDai := vatDai)
        (AshValDai := AshValDai) (SumpValDai := SumpValDai) (AshNew := AshNew)
        hvatDaiZero hAshLoadDai hSumpLoadDai hAshNew hfit hflopperNoCode
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    simpa [locals, evm0] using
      flopSourceBlockFromPostDai (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
        (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin)
        (AshVal := AshVal) (flopDebt := flopDebt) (SumpVal := SumpVal)
        (vatDai := vatDai) hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk
        hAshLoad hdebt hdebtOk hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai
        hdecDai (by simpa [locals4] using htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceKickCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai evmKick : EVM.State}
    {outSin outDai outKick : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpValSin vatDai AshValDai SumpValDai AshNew
      DumpVal SumpVal : UInt256}
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
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpValSin)
    (henough : SumpValSin.toNat ≤ flopDebt.toNat)
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
        (false, evmKick, outKick) true) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flopPostDaiTailStmts .reverted := by
    simpa [locals4] using
      flopPostDaiTailCallFailure (evmDai := evmDai) (evmKick := evmKick)
        (outKick := outKick) (vatSin := vatSin) (freeSin := freeSin)
        (flopDebt := flopDebt) (vatDai := vatDai) (AshValDai := AshValDai)
        (SumpValDai := SumpValDai) (AshNew := AshNew) (DumpVal := DumpVal)
        (SumpVal := SumpVal) hvatDaiZero hAshLoadDai hSumpLoadDai hAshNew hfit
        hDumpLoadAsh hSumpLoadAsh hflopperCode hcallKick
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    simpa [locals, evm0] using
      flopSourceBlockFromPostDai (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
        (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin)
        (AshVal := AshVal) (flopDebt := flopDebt) (SumpVal := SumpValSin)
        (vatDai := vatDai) hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk
        hAshLoad hdebt hdebtOk hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai
        hdecDai (by simpa [locals4] using htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceKickDecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai evmKick : EVM.State}
    {outSin outDai outKick : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpValSin vatDai AshValDai SumpValDai AshNew
      DumpVal SumpVal : UInt256}
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
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpValSin)
    (henough : SumpValSin.toNat ≤ flopDebt.toNat)
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
    (hdecKick : config.externalABI.decode? "kick" outKick = none) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flopPostDaiTailStmts .reverted := by
    simpa [locals4] using
      flopPostDaiTailDecodeRevert (evmDai := evmDai) (evmKick := evmKick)
        (outKick := outKick) (vatSin := vatSin) (freeSin := freeSin)
        (flopDebt := flopDebt) (vatDai := vatDai) (AshValDai := AshValDai)
        (SumpValDai := SumpValDai) (AshNew := AshNew) (DumpVal := DumpVal)
        (SumpVal := SumpVal) hvatDaiZero hAshLoadDai hSumpLoadDai hAshNew hfit
        hDumpLoadAsh hSumpLoadAsh hflopperCode hcallKick hdecKick
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    simpa [locals, evm0] using
      flopSourceBlockFromPostDai (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
        (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin)
        (AshVal := AshVal) (flopDebt := flopDebt) (SumpVal := SumpValSin)
        (vatDai := vatDai) hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk
        hAshLoad hdebt hdebtOk hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai
        hdecDai (by simpa [locals4] using htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai evmKick : EVM.State}
    {outSin outDai outKick : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpValSin vatDai AshValDai SumpValDai AshNew
      DumpVal SumpVal id : UInt256}
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
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpValSin)
    (henough : SumpValSin.toNat ≤ flopDebt.toNat)
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
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals6 := flopLocalsVatSinFreeSinDebtDaiAshNewId vatSin freeSin flopDebt vatDai AshNew id
    ExecTransitionBody config contract evm0 locals flopTransition.body
      (.returned { contract := contract, locals := locals6 } evmKick
        (some [.int (Int.ofNat id.toNat)])) := by
  intro locals evm0 locals6
  let locals4 := flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flopPostDaiTailStmts
        (.returned { contract := contract, locals := locals6 } evmKick
          (some [.int (Int.ofNat id.toNat)])) := by
    simpa [locals4, locals6] using
      flopPostDaiTailSuccess (evmDai := evmDai) (evmKick := evmKick)
        (outKick := outKick) (vatSin := vatSin) (freeSin := freeSin)
        (flopDebt := flopDebt) (vatDai := vatDai) (AshValDai := AshValDai)
        (SumpValDai := SumpValDai) (AshNew := AshNew) (DumpVal := DumpVal)
        (SumpVal := SumpVal) (id := id) hvatDaiZero hAshLoadDai hSumpLoadDai hAshNew
        hfit hDumpLoadAsh hSumpLoadAsh hflopperCode hcallKick hdecKick
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        (.returned { contract := contract, locals := locals6 } evmKick
          (some [.int (Int.ofNat id.toNat)])) := by
    simpa [locals, evm0] using
      flopSourceBlockFromPostDai (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
        (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin)
        (AshVal := AshVal) (flopDebt := flopDebt) (SumpVal := SumpValSin)
        (vatDai := vatDai) hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk
        hAshLoad hdebt hdebtOk hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai
        hdecDai (by simpa [locals4] using htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRet hblock

theorem RD.vowFlopToKickStart
    {cA gh bl σ σ₀ A I} {g sel target vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outDai : ByteArray} {k C : ℕ}
    (rd3832 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
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
    (hfit :
      (vowSlotWord ⟨6⟩ acc.2 I).toNat + (vowSlotWord ⟨9⟩ acc.2 I).toNat <
        UInt256.size) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
      ((vowSlotWord ⟨6⟩ acc.2 I + vowSlotWord ⟨9⟩ acc.2 I) ::
        ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outDai.write 0 (vatDaiCalldataMem I mem) 128 32)
      (UInt256.ofNat 6) outDai acc k' C' := by
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
  exact RD.vowFlopAshAddSuccess (vatDai := vatDai)
    (by simpa [hvatDai] using rd3873) hvatDaiZero hfit

theorem flopKickDecode_ok {o : ByteArray} (ho32 : 32 ≤ o.size) :
    config.externalABI.decode? "kick" o =
      some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)] := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_ok (returndata := o) ho32
  have hlt := fromByteArrayBigEndian_extract0_32_lt (returndata := o) ho32
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o =
        some (.int (Int.ofNat (fromByteArrayBigEndian (o.extract 0 32)))) := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o =
    some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)]
  unfold decodeReturn?
  rw [hdec']
  simp [UInt256.toNat_ofNat_of_lt hlt, Int.ofNat_eq_natCast]

theorem flopKickDecode_none_short {o : ByteArray} (hshort : o.size < 32) :
    config.externalABI.decode? "kick" o = none := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o) hshort
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o = none
  unfold decodeReturn?
  rw [hdec']
  rfl

theorem vowFlopKickNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpValSin AshValDai SumpValDai AshNew :
      UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai : EVM.State} {mem outSin outDai : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
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
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpValSin)
    (henough : SumpValSin.toNat ≤ flopDebt.toNat)
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
    (hAshNew : AshNew = AshValDai + SumpValDai)
    (hfit : AshValDai.toNat + SumpValDai.toNat < UInt256.size)
    (hflopperNoCode :
      (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (flopFlopperAddressOf
            (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew))).option
          0 (fun acc => acc.code.size))).toNat = 0)
    (hflopperNoCodeEvm :
      let σAsh := sstoreAccountMap I.codeOwner acc.2 ⟨6⟩ AshNew
      Reasoning.Theory.extCodeSizeWord σAsh
        (vowAddressReturnWord ⟨3⟩ σAsh I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let memDai := outDai.write 0 (vatDaiCalldataMem I mem) 128 32
  have hmemDai : memDai.size = 164 := by
    simpa [memDai] using vatDaiWrite_size I outDai 32 hmem (by omega) ho32
  have hread64Dai : memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memDai] using vatDaiWrite_read64 I outDai 32 hmem hread64 (by omega) ho32
  have hfitEvm :
      (vowSlotWord ⟨6⟩ acc.2 I).toNat + (vowSlotWord ⟨9⟩ acc.2 I).toNat <
        UInt256.size := by
    simpa [← hAshEvm, ← hSumpEvm] using hfit
  obtain ⟨k3959, C3959, rd3959Raw⟩ :=
    RD.vowFlopToKickStart rd3832 hmem hread64 ho32 hosz hvatDai hvatDaiZero hfitEvm
  have rd3959 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
      (AshNew :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      memDai (UInt256.ofNat 6) outDai acc k3959 C3959 := by
    simpa [memDai, hAshNew, hAshEvm, hSumpEvm] using rd3959Raw
  have hrev := RD.vowFlopKickNoCode rd3959 hperm hmemDai hread64Dai hflopperNoCodeEvm
  have hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)] := by
    simpa [hvatDai] using kissDaiDecode_ok (o := outDai) ho32
  have hbody := vowFlopSourceKickNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpVal := SumpValSin) (vatDai := vatDai)
    (AshValDai := AshValDai) (SumpValDai := SumpValDai) (AshNew := AshNew)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai hvatDaiZero
    hAshLoadDai hSumpLoadDai hAshNew hfit hflopperNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopKickCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpValSin AshValDai SumpValDai AshNew
      DumpVal SumpVal : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai evmKick : EVM.State}
    {mem outSin outDai outKick : ByteArray} {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd1498 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨0⟩ :: flopKickEndPtr :: flopKickSelectorWord ::
        target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem aw outKick acc k C)
    (houtKickSize : outKick.size < UInt256.size)
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
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpValSin)
    (henough : SumpValSin.toNat ≤ flopDebt.toNat)
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
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiZero : vatDai = ⟨0⟩)
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
        (false, evmKick, outKick) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlopKickCallFailure rd1498 houtKickSize (by simp)
  have hbody := vowFlopSourceKickCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (evmKick := evmKick)
    (outSin := outSin) (outDai := outDai) (outKick := outKick)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpValSin := SumpValSin) (vatDai := vatDai)
    (AshValDai := AshValDai) (SumpValDai := SumpValDai) (AshNew := AshNew)
    (DumpVal := DumpVal) (SumpVal := SumpVal)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai hvatDaiZero
    hAshLoadDai hSumpLoadDai hAshNew hfit hDumpLoadAsh hSumpLoadAsh hflopperCode
    hcallKick
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopKickDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel d0 d1 d2 vatDai : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpValSin AshValDai SumpValDai AshNew
      DumpVal SumpVal : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai evmKick : EVM.State}
    {mem outSin outDai outKick : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd1516 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outKick acc k C)
    (hshort : outKick.size < 32)
    (hosz : outKick.size < UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
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
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpValSin)
    (henough : SumpValSin.toNat ≤ flopDebt.toNat)
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
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiZero : vatDai = ⟨0⟩)
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
        (true, evmKick, outKick) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlopKickReturnDecodeShortReverts rd1516 hshort hosz hmload64
  have hdecKick : config.externalABI.decode? "kick" outKick = none :=
    flopKickDecode_none_short hshort
  have hbody := vowFlopSourceKickDecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (evmKick := evmKick)
    (outSin := outSin) (outDai := outDai) (outKick := outKick)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpValSin := SumpValSin) (vatDai := vatDai)
    (AshValDai := AshValDai) (SumpValDai := SumpValDai) (AshNew := AshNew)
    (DumpVal := DumpVal) (SumpVal := SumpVal)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai hvatDaiZero
    hAshLoadDai hSumpLoadDai hAshNew hfit hDumpLoadAsh hSumpLoadAsh hflopperCode
    hcallKick hdecKick
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopKickSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai id : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpValSin AshValDai SumpValDai AshNew
      DumpVal SumpVal : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai evmKick : EVM.State}
    {mem outSin outDai outKick : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd1498 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨1⟩ :: flopKickEndPtr :: flopKickSelectorWord ::
        target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outKick.write 0 (flopKickCalldataMem I DumpVal SumpVal mem) flopKickOutPtr.toNat
        (min flopKickOutSize (UInt256.ofNat outKick.size)).toNat)
      (UInt256.ofNat 8) outKick acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ outKick.size)
    (hosz : outKick.size < UInt256.size)
    (hid : id = UInt256.ofNat (fromByteArrayBigEndian (outKick.extract 0 32)))
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
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpValSin)
    (henough : SumpValSin.toNat ≤ flopDebt.toNat)
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
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiZero : vatDai = ⟨0⟩)
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
    (hcreated : acc.1 = evmKick.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmKick.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hret := RD.vowFlopKickSuccess rd1498 hmem hread64 ho32 hosz hid
  have hdecKick :
      config.externalABI.decode? "kick" outKick =
        some [.int (Int.ofNat id.toNat)] := by
    simpa [hid] using flopKickDecode_ok (o := outKick) ho32
  have hbody := vowFlopSourceSuccess (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (evmKick := evmKick)
    (outSin := outSin) (outDai := outDai) (outKick := outKick)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpValSin := SumpValSin) (vatDai := vatDai)
    (AshValDai := AshValDai) (SumpValDai := SumpValDai) (AshNew := AshNew)
    (DumpVal := DumpVal) (SumpVal := SumpVal) (id := id)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai hvatDaiZero
    hAshLoadDai hSumpLoadDai hAshNew hfit hDumpLoadAsh hSumpLoadAsh hflopperCode
    hcallKick hdecKick
  have henc :
      returnEquiv (UInt256.toByteArray id)
        (some [.int (Int.ofNat id.toNat)]) flopTransition.returnType := by
    rw [show flopTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding id)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated hAccountsFinal henc

end Benchmarks.Dss.Vow
