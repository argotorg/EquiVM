import Benchmarks.Dss.Vow.Flop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flop()` second `vat.dai(address(this))` call -/

abbrev flopLocalsVatSinFreeSinDebtDai
    (vatSin freeSin flopDebt vatDai : UInt256) : Store :=
  (flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt).insert "vatDai"
    (.int (Int.ofNat vatDai.toNat))

theorem flopLocalsVatSinFreeSinDebtDai_get_vatDai
    (vatSin freeSin flopDebt vatDai : UInt256) :
    (flopLocalsVatSinFreeSinDebtDai vatSin freeSin flopDebt vatDai).get? "vatDai" =
      some (.int (Int.ofNat vatDai.toNat)) := by
  rw [flopLocalsVatSinFreeSinDebtDai, store_get_self]

theorem vowFlopSourceDai1CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
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
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ I)) "dai" 0
        [.address I.codeOwner] (false, evmDai, outDai) false) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
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
          (perm := false)) .reverted := by
    exact ExecStmt.externalCallFailure hvatDai (by simp [evalExpr?, pure])
      hargsDai hcallDai
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
    exact ExecBlock.consRevert hcallDaiStmt
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceDai1NoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State}
    {outSin : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
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
    (hvatNoCodeDai :
      (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
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
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvatDai hvatNoCodeDai
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
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardDai)
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceDai1DecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
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
    (hdecDai : config.externalABI.decode? "dai" outDai = none) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
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
          (perm := false)) .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvatDai (by simp [evalExpr?, pure])
      hargsDai hcallDai hdecDai
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
    exact ExecBlock.consRevert hcallDaiStmt
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceDai1SurplusNotZero
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
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiNonzero : vatDai.toNat ≠ 0) :
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
        (.binary .eq (.var "vatDai") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hvatDaiVar, evalBinaryOp?, hvatDaiNonzero]
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
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqVatDai)
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem RD.vowFlopDai1PostCall
    {cA gh bl σ σ₀ A I} {g sel flopDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : (vowSlotWord ⟨9⟩ acc.2 I).toNat ≤ flopDebt.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outDai : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨1814410054⟩ ::
          kissDaiTargetWord acc.2 I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (outDai.write 0 (vatDaiCalldataMem I mem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
        (UInt256.ofNat 6) outDai (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := acc.2
          createdAccounts := acc.1 }
        (EVM.address (kissVatAddress acc.2 I)) "dai" 0 [.address I.codeOwner]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ'
            substate := A'
            createdAccounts := cA' },
          outDai) false
    ∧ outDai.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3831⟩ :=
    RD.vowFlopToDai1Staticcall rd henough hmem hread64 hcodeSize
  obtain ⟨cA', σ', z, outDai, A_in, callGas, k3832, C3832, hΘpack, rd3832raw, hosz⟩ :=
    RD.solcStaticcall rd3831 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmDaiIn := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := acc.2
    createdAccounts := acc.1 }
  refine ⟨cA', σ', z, outDai, A', k3832, C3832, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      native_decide
    exact haw ▸ rd3832raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord acc.2 I)
      (mem := vatDaiCalldataMem I mem) (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmDaiIn, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      (kissVatAddress_eq_daiTarget acc.2 I) (vatDaiEncode_eq I hmem) ?_
    simpa [evmDaiIn, initState] using hΘ

theorem RD.vowFlopDai1CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3832⟩) (okPc := ⟨3848⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowFlopDai1CallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3850⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨3832⟩) (okPc := ⟨3848⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowFlopDai1ReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3850⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨3850⟩) (okPc := ⟨3870⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowFlopDai1ReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3850⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
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
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3873⟩
      (retWord :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨3850⟩) (okPc := ⟨3870⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

abbrev vowSurplusNotZeroRawWord : UInt256 :=
  ⟨493458971516655262355748856637854565356164969071⟩

abbrev vowSurplusNotZeroStringWord : UInt256 :=
  UInt256.shiftLeft vowSurplusNotZeroRawWord ⟨96⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowFlopDai1SurplusNotZero
    {cA gh bl σ σ₀ A I} {g sel vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3873⟩
      (vatDai :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hvatDaiNonzero : vatDai ≠ ⟨0⟩)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd3874₀ := rd.iszero (by native_decide) (by evm_ov)
  have rd3874 := rd3874₀
  rw [isZero_eq_zero_of_ne hvatDaiNonzero] at rd3874
  have rd3877 := rd3874.push2 ⟨3945⟩ (by native_decide) (by evm_ov)
  have rd3878 := rd3877.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd3882 := evm_run rd3878 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd3886 := rd3882.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd3905 := evm_run rd3886 with [
    push1 ⟨229⟩,
    shl,
    dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨20⟩,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (solcErrorStringMem2 (⟨20⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd3926 := rd3905.pushConst vowSurplusNotZeroRawWord
    (width := 20) (op := .PUSH20) (by decide) (by native_decide) (by evm_ov)
  have rd3929₀ := evm_run rd3926 with [
    push1 ⟨96⟩,
    shl]
  have rd3929 := rd3929₀
  rw [show UInt256.shiftLeft vowSurplusNotZeroRawWord ⟨96⟩ =
      vowSurplusNotZeroStringWord from rfl] at rd3929
  exact evm_run rd3929 with [
    push1 ⟨68⟩,
    dup3,
    add,
    raw mstore 3
      (solcErrorStringMem3 (⟨20⟩ : UInt256) vowSurplusNotZeroStringWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨20⟩ : UInt256)
        vowSurplusNotZeroStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1,
    dup2,
    swap1,
    sub,
    push1 ⟨100⟩,
    add,
    swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem RD.vowFlopAshAddOverflow
    {cA gh bl σ σ₀ A I} {g sel vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3873⟩
      (vatDai :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hvatDaiZero : vatDai = ⟨0⟩)
    (hover :
      UInt256.size ≤
        (vowSlotWord ⟨6⟩ acc.2 I).toNat + (vowSlotWord ⟨9⟩ acc.2 I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
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
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (pc := ⟨5074⟩) (okPc := ⟨5090⟩) (a := AshVal) (b := SumpVal)
    (ret := ⟨3959⟩) (R := [⟨0⟩, ⟨357⟩, sel])
    (by simpa [AshVal, SumpVal] using rd5074)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [AshVal, SumpVal] using hover)
    (by simp)

theorem vowFlopDai1CallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai : EVM.State} {mem outSin outDai : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd3832 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem aw outDai acc k C)
    (houtDaiSize : outDai.size < UInt256.size)
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
        [.address I.codeOwner] (false, evmDai, outDai) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlopDai1CallFailure rd3832 houtDaiSize (by simp)
  have hbody := vowFlopSourceDai1CallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpVal := SumpVal)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopDai1NoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd3675 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
    (henough : (vowSlotWord ⟨9⟩ acc.2 I).toNat ≤ flopDebt.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) = ⟨0⟩)
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
    (hSumpEvm : SumpVal = vowSlotWord ⟨9⟩ acc.2 I)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatNoCodeDai :
      (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hEnoughSolm : SumpVal.toNat ≤ flopDebt.toNat := by
    simpa [hSumpEvm] using henough
  have hrev := RD.vowFlopDai1NoCode rd3675 henough hmem hread64 hcodeSize
  have hbody := vowFlopSourceDai1NoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) (vatSin := vatSin) (SinVal := SinVal)
    (freeSin := freeSin) (AshVal := AshVal) (flopDebt := flopDebt)
    (SumpVal := SumpVal)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad hEnoughSolm hvatLoadSin hvatNoCodeDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopDai1DecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
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
    (hshort : outDai.size < 32)
    (hosz : outDai.size < UInt256.size)
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
        [.address I.codeOwner] (true, evmDai, outDai) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat =
      outDai.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd3832' := rd3832
  rw [hmin] at rd3832'
  obtain ⟨_, _, rd3850⟩ :=
    RD.vowFlopDai1CallSuccessToDecode rd3832' (by simp)
  have hmemWrite : (outDai.write 0 (vatDaiCalldataMem I mem) 128 outDai.size).size =
      164 :=
    vatDaiWrite_size I outDai outDai.size hmem (by omega) (by omega)
  have hread64Write :
      (outDai.write 0 (vatDaiCalldataMem I mem) 128 outDai.size).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    vatDaiWrite_read64 I outDai outDai.size hmem hread64 (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outDai.write 0 (vatDaiCalldataMem I mem) 128 outDai.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 (vatDaiCalldataMem I mem) 128 outDai.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hrev := RD.vowFlopDai1ReturnDecodeShortReverts rd3850 hshort hosz hmload64
  have hdecDai : config.externalABI.decode? "dai" outDai = none :=
    kissDaiDecode_none_short hshort
  have hbody := vowFlopSourceDai1DecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpVal := SumpVal)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopDai1SurplusNotZeroBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai : UInt256}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
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
    (hvatDaiNonzero : vatDai.toNat ≠ 0)
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
        [.address I.codeOwner] (true, evmDai, outDai) false) :
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
  have hvatDaiNonzeroWord : vatDai ≠ ⟨0⟩ := by
    intro hzero
    apply hvatDaiNonzero
    rw [hzero]
    rfl
  have hrev := RD.vowFlopDai1SurplusNotZero (vatDai := vatDai)
    (by simpa [hvatDai] using rd3873)
    hvatDaiNonzeroWord hmemWrite hread64Write
  have hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)] := by
    simpa [hvatDai] using kissDaiDecode_ok (o := outDai) ho32
  have hbody := vowFlopSourceDai1SurplusNotZero (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin := vatSin) (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal)
    (flopDebt := flopDebt) (SumpVal := SumpVal) (vatDai := vatDai)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad henough hvatLoadSin hvatCodeDai hcallDai hdecDai hvatDaiNonzero
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow
