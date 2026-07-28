import Benchmarks.Dss.Vow.FlapBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` first `vat.dai(address(this))` source/refinement glue -/

def flapBeforeDaiStmts : List Stmt :=
  nonpayable ++
  checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin0"
    (perm := false) ++
  [ .internalCall "add" [.var "vatSin0", .storage bumpRef] "surplus0",
    .internalCall "add" [.var "surplus0", .storage humpRef] "surplusNeed" ]

def flapDai0AndTailStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
    (perm := false) ++
  flapTailStmts

theorem flapBeforeDaiSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State}
    {outSin : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed : UInt256}
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
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals3 := flapLocalsVatSin0Surplus0Need vatSin0 surplus0 surplusNeed
    ExecBlock config { contract := contract, locals := locals } evm0 flapBeforeDaiStmts
      (.ok { contract := contract, locals := locals3 } evmSin) := by
  intro locals evm0 locals3
  let locals1 := flapLocalsVatSin0 vatSin0
  let locals2 := flapLocalsVatSin0Surplus0 vatSin0 surplus0
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
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin0"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmSin) := by
    simpa [locals, locals1, flapLocalsVatSin0, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsSin hcallSin hdecSin
  have hvatSin0Var :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.var "vatSin0") =
        .ok (.int (Int.ofNat vatSin0.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmSin) (locals := flapLocalsVatSin0 vatSin0)
        (name := "vatSin0") (value := vatSin0) (flapLocalsVatSin0_get_vatSin0 vatSin0)
  have hbump :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.storage bumpRef) =
        .ok (.int (Int.ofNat BumpVal.toNat)) := by
    simpa [locals1, hBumpLoad] using
      evalExpr_flapBumpStorage (evm := evmSin) (locals := locals1)
        (by simp [locals1, flapLocalsVatSin0])
  have hargsSurplus0 :
      evalExprs? config { contract := contract, locals := locals1 } evmSin
        [.var "vatSin0", .storage bumpRef] =
          .ok [.int (Int.ofNat vatSin0.toNat), .int (Int.ofNat BumpVal.toNat)] := by
    simp [evalExprs?, hvatSin0Var, hbump, EvalResult.bind, bind, pure]
  have hbindSurplus0 :
      bindParams? addFunction.params
          [.int (Int.ofNat vatSin0.toNat), .int (Int.ofNat BumpVal.toNat)] =
        some (uintBinaryLocals vatSin0 BumpVal) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hsurplus0Stmt :
      ExecStmt config { contract := contract, locals := locals1 } evmSin
        (.internalCall "add" [.var "vatSin0", .storage bumpRef] "surplus0")
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    have hbody := execAddFunctionReturn (evm := evmSin) (x := vatSin0) (y := BumpVal)
      (sum := surplus0) hsurplus0 hsurplus0Fit
    simpa [locals1, locals2, flapLocalsVatSin0Surplus0, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals1 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "add") (retVar := "surplus0")
        (args := [.var "vatSin0", .storage bumpRef])
        (argVals := [.int (Int.ofNat vatSin0.toNat), .int (Int.ofNat BumpVal.toNat)])
        (callee := addFunction) (locals := uintBinaryLocals vatSin0 BumpVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin0 BumpVal surplus0 })
        (value := some [.int (Int.ofNat surplus0.toNat)])
        hargsSurplus0 (by rfl) hbindSurplus0 hbody)
  have hsurplus0Var :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "surplus0") =
        .ok (.int (Int.ofNat surplus0.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flapLocalsVatSin0Surplus0 vatSin0 surplus0)
        (name := "surplus0") (value := surplus0)
        (flapLocalsVatSin0Surplus0_get_surplus0 vatSin0 surplus0)
  have hhump :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage humpRef) =
        .ok (.int (Int.ofNat HumpVal.toNat)) := by
    simpa [locals2, hHumpLoad] using
      evalExpr_flapHumpStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hargsSurplusNeed :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "surplus0", .storage humpRef] =
          .ok [.int (Int.ofNat surplus0.toNat), .int (Int.ofNat HumpVal.toNat)] := by
    simp [evalExprs?, hsurplus0Var, hhump, EvalResult.bind, bind, pure]
  have hbindSurplusNeed :
      bindParams? addFunction.params
          [.int (Int.ofNat surplus0.toNat), .int (Int.ofNat HumpVal.toNat)] =
        some (uintBinaryLocals surplus0 HumpVal) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hsurplusNeedStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "add" [.var "surplus0", .storage humpRef] "surplusNeed")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execAddFunctionReturn (evm := evmSin) (x := surplus0) (y := HumpVal)
      (sum := surplusNeed) hsurplusNeed hsurplusNeedFit
    simpa [locals2, locals3, flapLocalsVatSin0Surplus0Need, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "add") (retVar := "surplusNeed")
        (args := [.var "surplus0", .storage humpRef])
        (argVals := [.int (Int.ofNat surplus0.toNat), .int (Int.ofNat HumpVal.toNat)])
        (callee := addFunction) (locals := uintBinaryLocals surplus0 HumpVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ surplus0 HumpVal surplusNeed })
        (value := some [.int (Int.ofNat surplusNeed.toNat)])
        hargsSurplusNeed (by rfl) hbindSurplusNeed hbody)
  simp only [flapBeforeDaiStmts, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  refine ExecBlock.consNormal hcallSinStmt ?_
  refine ExecBlock.consNormal hsurplus0Stmt ?_
  exact ExecBlock.consNormal hsurplusNeedStmt ExecBlock.nil

theorem flapSourceDai0NoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State}
    {outSin : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed : UInt256}
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
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatNoCodeDai :
      (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  let locals3 := flapLocalsVatSin0Surplus0Need vatSin0 surplus0 surplusNeed
  have hbefore :
      ExecBlock config { contract := contract, locals := locals } evm0 flapBeforeDaiStmts
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    simpa [locals, evm0, locals3] using
      flapBeforeDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (outSin := outSin) (vatSin0 := vatSin0) (BumpVal := BumpVal)
        (surplus0 := surplus0) (HumpVal := HumpVal) (surplusNeed := surplusNeed)
        hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit
        hHumpLoad hsurplusNeed hsurplusNeedFit
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals3, kissVatAddress, vowAddressReturnWord, hvatLoadSin] using
      evalExpr_kissVatStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0,
          flapLocalsVatSin0])
  have hguardDai :
      evalExpr? config { contract := contract, locals := locals3 } evmSin
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvatDai hvatNoCodeDai
  have htail :
      ExecBlock config { contract := contract, locals := locals3 } evmSin
        flapDai0AndTailStmts .reverted := by
    simp only [flapDai0AndTailStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardDai)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat :=.execBlock_append hbefore htail
    simpa [flapTransition, flapBeforeDaiStmts, flapDai0AndTailStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable, checkedExternalCallStmts,
      locals, evm0] using hcat
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flapSourceDai0CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed : UInt256}
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
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin (EVM.address (kissVatAddress σ I)) "dai" 0
        [.address I.codeOwner] (false, evmDai, outDai) false) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  let locals3 := flapLocalsVatSin0Surplus0Need vatSin0 surplus0 surplusNeed
  have hbefore :
      ExecBlock config { contract := contract, locals := locals } evm0 flapBeforeDaiStmts
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    simpa [locals, evm0, locals3] using
      flapBeforeDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (outSin := outSin) (vatSin0 := vatSin0) (BumpVal := BumpVal)
        (surplus0 := surplus0) (HumpVal := HumpVal) (surplusNeed := surplusNeed)
        hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit
        hHumpLoad hsurplusNeed hsurplusNeedFit
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals3, kissVatAddress, vowAddressReturnWord, hvatLoadSin] using
      evalExpr_kissVatStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0,
          flapLocalsVatSin0])
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
  have htail :
      ExecBlock config { contract := contract, locals := locals3 } evmSin
        flapDai0AndTailStmts .reverted := by
    simp only [flapDai0AndTailStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDai) ?_
    exact ExecBlock.consRevert hcallDaiStmt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat :=.execBlock_append hbefore htail
    simpa [flapTransition, flapBeforeDaiStmts, flapDai0AndTailStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable, checkedExternalCallStmts,
      locals, evm0] using hcat
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flapSourceDai0DecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed : UInt256}
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
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
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
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  let locals3 := flapLocalsVatSin0Surplus0Need vatSin0 surplus0 surplusNeed
  have hbefore :
      ExecBlock config { contract := contract, locals := locals } evm0 flapBeforeDaiStmts
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    simpa [locals, evm0, locals3] using
      flapBeforeDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (outSin := outSin) (vatSin0 := vatSin0) (BumpVal := BumpVal)
        (surplus0 := surplus0) (HumpVal := HumpVal) (surplusNeed := surplusNeed)
        hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit
        hHumpLoad hsurplusNeed hsurplusNeedFit
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals3, kissVatAddress, vowAddressReturnWord, hvatLoadSin] using
      evalExpr_kissVatStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0,
          flapLocalsVatSin0])
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
  have htail :
      ExecBlock config { contract := contract, locals := locals3 } evmSin
        flapDai0AndTailStmts .reverted := by
    simp only [flapDai0AndTailStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDai) ?_
    exact ExecBlock.consRevert hcallDaiStmt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat :=.execBlock_append hbefore htail
    simpa [flapTransition, flapBeforeDaiStmts, flapDai0AndTailStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable, checkedExternalCallStmts,
      locals, evm0] using hcat
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem vowFlapDai0NoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin0 BumpVal surplus0 HumpVal
      surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd993 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨993⟩
      (surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
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
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
    (hvatLoadSin :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatNoCodeDai :
      (UInt256.ofNat
        ((evmSin.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapDai0NoCode rd993 hmem hread64 hcodeSize
  have hbody := flapSourceDai0NoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) (vatSin0 := vatSin0)
    (BumpVal := BumpVal) (surplus0 := surplus0) (HumpVal := HumpVal)
    (surplusNeed := surplusNeed)
    hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit hHumpLoad
    hsurplusNeed hsurplusNeedFit hvatLoadSin hvatNoCodeDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapDai0CallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatSin0 BumpVal surplus0 HumpVal
      surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai : EVM.State} {mem outSin outDai : ByteArray} {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1072 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1072⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: surplusNeed :: ⟨0⟩ ::
        ⟨357⟩ :: sel :: [])
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
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
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
  have hrev := RD.vowFlapDai0CallFailure rd1072 houtDaiSize (by simp)
  have hbody := flapSourceDai0CallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
    (HumpVal := HumpVal) (surplusNeed := surplusNeed)
    hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit hHumpLoad
    hsurplusNeed hsurplusNeedFit hvatLoadSin hvatCodeDai hcallDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapDai0DecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatSin0 BumpVal surplus0 HumpVal
      surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai : EVM.State} {mem outSin outDai : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1072 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1072⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: surplusNeed :: ⟨0⟩ ::
        ⟨357⟩ :: sel :: [])
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
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
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
  have rd1072' := rd1072
  rw [hmin] at rd1072'
  obtain ⟨_, _, rd1090⟩ :=
    RD.vowFlapDai0CallSuccessToDecode rd1072' (by simp)
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
  have hrev := RD.vowFlapDai0ReturnDecodeShortReverts rd1090 hshort hosz hmload64
  have hdecDai : config.externalABI.decode? "dai" outDai = none :=
    kissDaiDecode_none_short hshort
  have hbody := flapSourceDai0DecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
    (HumpVal := HumpVal) (surplusNeed := surplusNeed)
    hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit hHumpLoad
    hsurplusNeed hsurplusNeedFit hvatLoadSin hvatCodeDai hcallDai hdecDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow
