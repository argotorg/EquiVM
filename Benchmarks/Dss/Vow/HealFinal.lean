import Benchmarks.Dss.Vow.HealSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

abbrev healLocalsDone
    (I : ExecutionEnv) (vatDai vatSin freeSin healDebt : UInt256) : Store :=
  (healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt).insert
    "_healRet" (collapseReturns [])

theorem vowHealSourceHealNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin : EVM.State}
    {outDai outSin : ByteArray}
    {vatDai vatSin SinVal freeSin AshVal healDebt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : healDebt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtEnough : (healRad I).toNat ≤ healDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatNoCodeHeal :
      (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat =
          0) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  let locals2 := healLocalsVatDaiVatSin I vatDai vatSin
  let locals3 := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin
  let locals4 := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    simpa [locals1, locals2, healLocalsVatDaiVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvatSin (by simp [evalExpr?, pure]) hargsSin
        hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSin I vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (healLocalsVatDaiVatSin_get_vatSin I vatDai vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals2, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals2, locals3, healLocalsVatDaiVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals3] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (healLocalsVatDaiVatSinFreeSin_get_freeSin I vatDai vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals3, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin,
          healLocalsVatDai, healLocals])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals3 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals3 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "healDebt")
        (.ok { contract := contract, locals := locals4 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := freeSin) (y := AshVal)
      (diff := healDebt) hdebt hdebtOk
    simpa [locals3, locals4, healLocalsVatDaiVatSinFreeSinHealDebt,
      resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals3 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "healDebt")
        (args := [.var "freeSin", .storage AshRef])
        (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ freeSin AshVal healDebt })
        (value := some [.int (Int.ofNat healDebt.toNat)]) hargsDebt (by rfl) hbindDebt hbody)
  have hrad :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "rad") (value := healRad I)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_rad I vatDai vatSin freeSin healDebt)
  have hhealDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "healDebt") =
        .ok (.int (Int.ofNat healDebt.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "healDebt") (value := healDebt)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_healDebt I vatDai vatSin freeSin healDebt)
  have hreqDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin
        (.binary .le (.var "rad") (.var "healDebt")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hhealDebt hdebtEnough
  have hvatHeal :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals4, kissVatAddress, vowAddressReturnWord, hvatLoadSin] using
      evalExpr_kissVatStorage (evm := evmSin) (locals := locals4)
        (by simp [locals4, healLocalsVatDaiVatSinFreeSinHealDebt,
          healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hguardHeal :
      evalExpr? config { contract := contract, locals := locals4 } evmSin
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvatHeal hvatNoCodeHeal
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    refine ExecBlock.consNormal hdebtStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDebt) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardHeal)
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealHealNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatDai vatSin freeSin healDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin : EVM.State} {mem outDai outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd4997 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4997⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) outSin acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeEvm :
      Reasoning.Theory.uniswapExtCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) =
        ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ acc.2 I)
    (hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ acc.2 I)
    (hdebt : healDebt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ acc.2 I))
    (hdebtOk : (vowSlotWord ⟨6⟩ acc.2 I).toNat ≤ freeSin.toNat)
    (hdebtEnough : (healRad I).toNat ≤ healDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatNoCodeHeal :
      (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealHealNoCode rd4997 hmem hread64 hcodeSizeEvm
  have hbody := vowHealSourceHealNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (outDai := outDai) (outSin := outSin)
    (vatDai := vatDai) (vatSin := vatSin) (SinVal := vowSlotWord ⟨5⟩ acc.2 I)
    (freeSin := freeSin) (AshVal := vowSlotWord ⟨6⟩ acc.2 I) (healDebt := healDebt)
    hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai hvatCodeSin hcallSin
    hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk hdebtEnough hvatLoadSin
    hvatNoCodeHeal
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealSourceHealCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin evmHeal : EVM.State}
    {outDai outSin outHeal : ByteArray}
    {vatDai vatSin SinVal freeSin AshVal healDebt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : healDebt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtEnough : (healRad I).toNat ≤ healDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ I)) "heal" 0
        [.int (Int.ofNat (healRad I).toNat)] (false, evmHeal, outHeal) true) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  let locals2 := healLocalsVatDaiVatSin I vatDai vatSin
  let locals3 := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin
  let locals4 := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    simpa [locals1, locals2, healLocalsVatDaiVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvatSin (by simp [evalExpr?, pure]) hargsSin
        hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSin I vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (healLocalsVatDaiVatSin_get_vatSin I vatDai vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals2, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals2, locals3, healLocalsVatDaiVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals3] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (healLocalsVatDaiVatSinFreeSin_get_freeSin I vatDai vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals3, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin,
          healLocalsVatDai, healLocals])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals3 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals3 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "healDebt")
        (.ok { contract := contract, locals := locals4 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := freeSin) (y := AshVal)
      (diff := healDebt) hdebt hdebtOk
    simpa [locals3, locals4, healLocalsVatDaiVatSinFreeSinHealDebt,
      resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals3 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "healDebt")
        (args := [.var "freeSin", .storage AshRef])
        (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ freeSin AshVal healDebt })
        (value := some [.int (Int.ofNat healDebt.toNat)]) hargsDebt (by rfl) hbindDebt hbody)
  have hrad :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "rad") (value := healRad I)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_rad I vatDai vatSin freeSin healDebt)
  have hhealDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "healDebt") =
        .ok (.int (Int.ofNat healDebt.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "healDebt") (value := healDebt)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_healDebt I vatDai vatSin freeSin healDebt)
  have hreqDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin
        (.binary .le (.var "rad") (.var "healDebt")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hhealDebt hdebtEnough
  have hvatHeal :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals4, kissVatAddress, vowAddressReturnWord, hvatLoadSin] using
      evalExpr_kissVatStorage (evm := evmSin) (locals := locals4)
        (by simp [locals4, healLocalsVatDaiVatSinFreeSinHealDebt,
          healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hguardHeal :
      evalExpr? config { contract := contract, locals := locals4 } evmSin
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatHeal hvatCodeHeal
  have hargsHeal :
      evalExprs? config { contract := contract, locals := locals4 } evmSin [.var "rad"] =
        .ok [.int (Int.ofNat (healRad I).toNat)] := by
    simpa [locals4] using
      evalExprs_kissRad (evm := evmSin) (I := I)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_rad I vatDai vatSin freeSin healDebt)
  have hcallHealStmt :
      ExecStmt config { contract := contract, locals := locals4 } evmSin
        (.externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hvatHeal (by simp [evalExpr?, pure]) hargsHeal hcallHeal
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    refine ExecBlock.consNormal hdebtStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDebt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardHeal) ?_
    exact ExecBlock.consRevert hcallHealStmt
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin evmHeal : EVM.State}
    {outDai outSin outHeal : ByteArray}
    {vatDai vatSin SinVal freeSin AshVal healDebt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : healDebt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtEnough : (healRad I).toNat ≤ healDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ I)) "heal" 0
        [.int (Int.ofNat (healRad I).toNat)] (true, evmHeal, outHeal) true)
    (hdecHeal : config.externalABI.decode? "heal" outHeal = some []) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body
      (.returned
        { contract := contract, locals := healLocalsDone I vatDai vatSin freeSin healDebt }
        evmHeal none) := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  let locals2 := healLocalsVatDaiVatSin I vatDai vatSin
  let locals3 := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin
  let locals4 := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    simpa [locals1, locals2, healLocalsVatDaiVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvatSin (by simp [evalExpr?, pure]) hargsSin
        hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSin I vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (healLocalsVatDaiVatSin_get_vatSin I vatDai vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals2, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals2, locals3, healLocalsVatDaiVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals3] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (healLocalsVatDaiVatSinFreeSin_get_freeSin I vatDai vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals3, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin,
          healLocalsVatDai, healLocals])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals3 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals3 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "healDebt")
        (.ok { contract := contract, locals := locals4 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := freeSin) (y := AshVal)
      (diff := healDebt) hdebt hdebtOk
    simpa [locals3, locals4, healLocalsVatDaiVatSinFreeSinHealDebt,
      resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals3 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "healDebt")
        (args := [.var "freeSin", .storage AshRef])
        (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ freeSin AshVal healDebt })
        (value := some [.int (Int.ofNat healDebt.toNat)]) hargsDebt (by rfl) hbindDebt hbody)
  have hrad :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "rad") (value := healRad I)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_rad I vatDai vatSin freeSin healDebt)
  have hhealDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "healDebt") =
        .ok (.int (Int.ofNat healDebt.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "healDebt") (value := healDebt)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_healDebt I vatDai vatSin freeSin healDebt)
  have hreqDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin
        (.binary .le (.var "rad") (.var "healDebt")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hhealDebt hdebtEnough
  have hvatHeal :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals4, kissVatAddress, vowAddressReturnWord, hvatLoadSin] using
      evalExpr_kissVatStorage (evm := evmSin) (locals := locals4)
        (by simp [locals4, healLocalsVatDaiVatSinFreeSinHealDebt,
          healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hguardHeal :
      evalExpr? config { contract := contract, locals := locals4 } evmSin
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatHeal hvatCodeHeal
  have hargsHeal :
      evalExprs? config { contract := contract, locals := locals4 } evmSin [.var "rad"] =
        .ok [.int (Int.ofNat (healRad I).toNat)] := by
    simpa [locals4] using
      evalExprs_kissRad (evm := evmSin) (I := I)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_rad I vatDai vatSin freeSin healDebt)
  have hcallHealStmt :
      ExecStmt config { contract := contract, locals := locals4 } evmSin
        (.externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet")
        (.ok
          { contract := contract, locals := healLocalsDone I vatDai vatSin freeSin healDebt }
          evmHeal) := by
    simpa [locals4, healLocalsDone, collapseReturns] using
      ExecStmt.externalCallSuccess hvatHeal (by simp [evalExpr?, pure]) hargsHeal hcallHeal
        hdecHeal
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        (.ok
          { contract := contract, locals := healLocalsDone I vatDai vatSin freeSin healDebt }
          evmHeal) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    refine ExecBlock.consNormal hdebtStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqDebt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardHeal) ?_
    exact ExecBlock.consNormal hcallHealStmt ExecBlock.nil
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockOK hblock

theorem vowHealHealCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai vatSin freeSin healDebt : UInt256}
    {preAcc acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin evmHeal : EVM.State} {mem outDai outSin outHeal rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd1919 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨0⟩ :: kissHealEndPtr :: kissHealSelector :: target ::
        healRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ preAcc.2 I)
    (hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ preAcc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ preAcc.2 I).toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ preAcc.2 I)
    (hdebt : healDebt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ preAcc.2 I))
    (hdebtOk : (vowSlotWord ⟨6⟩ preAcc.2 I).toNat ≤ freeSin.toNat)
    (hdebtEnough : (healRad I).toNat ≤ healDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ_solm I)) "heal" 0
        [.int (Int.ofNat (healRad I).toNat)] (false, evmHeal, outHeal) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowKissHealCallFailure (by simpa [kissRad] using rd1919) hrdataSize
  have hbody := vowHealSourceHealCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (evmHeal := evmHeal)
    (outDai := outDai) (outSin := outSin) (outHeal := outHeal)
    (vatDai := vatDai) (vatSin := vatSin) (SinVal := vowSlotWord ⟨5⟩ preAcc.2 I)
    (freeSin := freeSin) (AshVal := vowSlotWord ⟨6⟩ preAcc.2 I) (healDebt := healDebt)
    hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai hvatCodeSin hcallSin
    hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk hdebtEnough hvatLoadSin
    hvatCodeHeal hcallHeal
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealHealSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai vatSin freeSin healDebt : UInt256}
    {preAcc acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin evmHeal : EVM.State} {mem outDai outSin outHeal rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd1919 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨1⟩ :: kissHealEndPtr :: kissHealSelector :: target ::
        healRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ preAcc.2 I)
    (hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ preAcc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ preAcc.2 I).toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ preAcc.2 I)
    (hdebt : healDebt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ preAcc.2 I))
    (hdebtOk : (vowSlotWord ⟨6⟩ preAcc.2 I).toNat ≤ freeSin.toNat)
    (hdebtEnough : (healRad I).toNat ≤ healDebt.toNat)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ_solm I)) "heal" 0
        [.int (Int.ofNat (healRad I).toNat)] (true, evmHeal, outHeal) true)
    (hdecHeal : config.externalABI.decode? "heal" outHeal = some [])
    (hcreated : acc.1 = evmHeal.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmHeal.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hret := RD.vowKissHealCallSuccess (by simpa [kissRad] using rd1919)
  have hbody := vowHealSourceSuccess (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (evmHeal := evmHeal)
    (outDai := outDai) (outSin := outSin) (outHeal := outHeal)
    (vatDai := vatDai) (vatSin := vatSin) (SinVal := vowSlotWord ⟨5⟩ preAcc.2 I)
    (freeSin := freeSin) (AshVal := vowSlotWord ⟨6⟩ preAcc.2 I) (healDebt := healDebt)
    hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai hvatCodeSin hcallSin
    hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk hdebtEnough hvatLoadSin
    hvatCodeHeal hcallHeal hdecHeal
  have henc : returnEquiv ByteArray.empty none healTransition.returnType := by
    rw [show healTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated hAccountsFinal henc

end Benchmarks.Dss.Vow
