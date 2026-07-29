import Benchmarks.Dss.Vow.FlapDaiBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` second `vat.sin(address(this))` body-core glue -/

theorem flapTailSin1NoCode
    {σ I} {evmDai : EVM.State}
    {vatSin0 surplus0 surplusNeed vatDai : UInt256}
    (henough : surplusNeed.toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatNoCodeSin1 :
      (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
      .reverted := by
  intro locals4
  have hvatDaiVar :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.var "vatDai") =
        .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai)
        (name := "vatDai") (value := vatDai)
        (flapLocalsVatSin0Surplus0NeedDai_get_vatDai
          vatSin0 surplus0 surplusNeed vatDai)
  have hsurplusNeedVar :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.var "surplusNeed") =
          .ok (.int (Int.ofNat surplusNeed.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai)
        (name := "surplusNeed") (value := surplusNeed)
        (flapLocalsVatSin0Surplus0NeedDai_get_surplusNeed
          vatSin0 surplus0 surplusNeed vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .ge (.var "vatDai") (.var "surplusNeed")) = .ok (.bool true) :=
    evalExpr_ge_uint256_true hvatDaiVar hsurplusNeedVar henough
  have hvatSin1 :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals4, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals4)
        (by simp [locals4, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hguardSin1 :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_kissVatCodeGuard_false hvatSin1 hvatNoCodeSin1
  simp only [flapTailStmts, flapPostDaiToKickStmts, flapKickAndReturnStmts,
    checkedExternalCallStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardSin1)

theorem flapTailSin1CallFailure
    {σ I} {evmDai evmSin : EVM.State} {outSin : ByteArray}
    {vatSin0 surplus0 surplusNeed vatDai : UInt256}
    (hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner)
    (henough : surplusNeed.toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin1 :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin1 :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (false, evmSin, outSin) false) :
    let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
      .reverted := by
  intro locals4
  have hvatDaiVar :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.var "vatDai") =
        .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai)
        (name := "vatDai") (value := vatDai)
        (flapLocalsVatSin0Surplus0NeedDai_get_vatDai
          vatSin0 surplus0 surplusNeed vatDai)
  have hsurplusNeedVar :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.var "surplusNeed") =
          .ok (.int (Int.ofNat surplusNeed.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai)
        (name := "surplusNeed") (value := surplusNeed)
        (flapLocalsVatSin0Surplus0NeedDai_get_surplusNeed
          vatSin0 surplus0 surplusNeed vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .ge (.var "vatDai") (.var "surplusNeed")) = .ok (.bool true) :=
    evalExpr_ge_uint256_true hvatDaiVar hsurplusNeedVar henough
  have hvatSin1 :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals4, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals4)
        (by simp [locals4, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hguardSin1 :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvatSin1 hvatCodeSin1
  have hargsSin1 :
      evalExprs? config { contract := contract, locals := locals4 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [hownerDai] using evalExprs_kissThis evmDai locals4
  have hcallSin1Stmt :
      ExecStmt config { contract := contract, locals := locals4 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin1"
          (perm := false)) .reverted := by
    exact ExecStmt.externalCallFailure hvatSin1 (by simp [evalExpr?, pure])
      hargsSin1 hcallSin1
  simp only [flapTailStmts, flapPostDaiToKickStmts, flapKickAndReturnStmts,
    checkedExternalCallStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin1) ?_
  exact ExecBlock.consRevert hcallSin1Stmt

theorem flapTailSin1DecodeRevert
    {σ I} {evmDai evmSin : EVM.State} {outSin : ByteArray}
    {vatSin0 surplus0 surplusNeed vatDai : UInt256}
    (hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner)
    (henough : surplusNeed.toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin1 :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin1 :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin1 : config.externalABI.decode? "sin" outSin = none) :
    let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
    ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
      .reverted := by
  intro locals4
  have hvatDaiVar :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.var "vatDai") =
        .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai)
        (name := "vatDai") (value := vatDai)
        (flapLocalsVatSin0Surplus0NeedDai_get_vatDai
          vatSin0 surplus0 surplusNeed vatDai)
  have hsurplusNeedVar :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.var "surplusNeed") =
          .ok (.int (Int.ofNat surplusNeed.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmDai)
        (locals := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai)
        (name := "surplusNeed") (value := surplusNeed)
        (flapLocalsVatSin0Surplus0NeedDai_get_surplusNeed
          vatSin0 surplus0 surplusNeed vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .ge (.var "vatDai") (.var "surplusNeed")) = .ok (.bool true) :=
    evalExpr_ge_uint256_true hvatDaiVar hsurplusNeedVar henough
  have hvatSin1 :
      evalExpr? config { contract := contract, locals := locals4 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals4, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals4)
        (by simp [locals4, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hguardSin1 :
      evalExpr? config { contract := contract, locals := locals4 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_kissVatCodeGuard_true hvatSin1 hvatCodeSin1
  have hargsSin1 :
      evalExprs? config { contract := contract, locals := locals4 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [hownerDai] using evalExprs_kissThis evmDai locals4
  have hcallSin1Stmt :
      ExecStmt config { contract := contract, locals := locals4 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin1"
          (perm := false)) .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvatSin1 (by simp [evalExpr?, pure])
      hargsSin1 hcallSin1 hdecSin1
  simp only [flapTailStmts, flapPostDaiToKickStmts, flapKickAndReturnStmts,
    checkedExternalCallStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin1) ?_
  exact ExecBlock.consRevert hcallSin1Stmt

theorem vowFlapSin1NoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin0 BumpVal surplus0 HumpVal
      surplusNeed vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin0 evmDai : EVM.State} {mem outSin0 outDai : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1190 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1190⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outDai acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin0 :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin0, outSin0) false)
    (hdecSin0 :
      config.externalABI.decode? "sin" outSin0 =
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
    (hvatLoadSin0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSin0.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin0 (EVM.address (kissVatAddress σ_solm I)) "dai" 0
        [.address I.codeOwner] (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (henough : surplusNeed.toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatNoCodeSin1 :
      (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapSin1NoCode rd1190 hmem hread64 hcodeSize
  let locals := (∅ : Store)
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
  have hprefix :
      ExecBlock config { contract := contract, locals := locals } evm0 flapPrefixToDaiStmts
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals, evm0, locals4] using
      flapPrefixToDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin0)
        (evmDai := evmDai) (outSin := outSin0) (outDai := outDai)
        (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
        (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
        hwv hvatCode0 hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hsurplus0Fit
        hHumpLoad0 hsurplusNeed hsurplusNeedFit hvatLoadSin0 hvatCodeDai hcallDai
        hdecDai
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
        .reverted := by
    simpa [locals4] using
      flapTailSin1NoCode (σ := σ_solm) (I := I) (evmDai := evmDai)
        (vatSin0 := vatSin0) (surplus0 := surplus0) (surplusNeed := surplusNeed)
        (vatDai := vatDai) henough hvatLoadDai hvatNoCodeSin1
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat := execBlock_append hprefix htail
    simpa [flapTransition, flapPrefixToDaiStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable, checkedExternalCallStmts,
      locals, evm0] using hcat
  have hbody :
      ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
    simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapSin1CallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatSin0 BumpVal surplus0 HumpVal
      surplusNeed vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin0 evmDai evmSin1 : EVM.State} {mem outSin0 outDai outSin1 : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector :: target :: ⟨1325⟩ ::
        ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem aw outSin1 acc k C)
    (houtSinSize : outSin1.size < UInt256.size)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin0 :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin0, outSin0) false)
    (hdecSin0 :
      config.externalABI.decode? "sin" outSin0 =
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
    (hvatLoadSin0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSin0.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin0 (EVM.address (kissVatAddress σ_solm I)) "dai" 0
        [.address I.codeOwner] (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner)
    (henough : surplusNeed.toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin1 :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin1 :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (false, evmSin1, outSin1) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapSin1CallFailure rd1277 houtSinSize (by simp)
  let locals := (∅ : Store)
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
  have hprefix :
      ExecBlock config { contract := contract, locals := locals } evm0 flapPrefixToDaiStmts
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals, evm0, locals4] using
      flapPrefixToDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin0)
        (evmDai := evmDai) (outSin := outSin0) (outDai := outDai)
        (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
        (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
        hwv hvatCode0 hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hsurplus0Fit
        hHumpLoad0 hsurplusNeed hsurplusNeedFit hvatLoadSin0 hvatCodeDai hcallDai
        hdecDai
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
        .reverted := by
    simpa [locals4] using
      flapTailSin1CallFailure (σ := σ_solm) (I := I) (evmDai := evmDai)
        (evmSin := evmSin1) (outSin := outSin1)
        (vatSin0 := vatSin0) (surplus0 := surplus0) (surplusNeed := surplusNeed)
        (vatDai := vatDai) hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat := execBlock_append hprefix htail
    simpa [flapTransition, flapPrefixToDaiStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable, checkedExternalCallStmts,
      locals, evm0] using hcat
  have hbody :
      ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
    simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapSin1DecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatSin0 BumpVal surplus0 HumpVal
      surplusNeed vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin0 evmDai evmSin1 : EVM.State} {mem outSin0 outDai outSin1 : ByteArray}
    {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: target :: ⟨1325⟩ ::
        ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin1.write 0 (healSinCalldataMem I mem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin1.size)).toNat)
      (UInt256.ofNat 6) outSin1 acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : outSin1.size < 32)
    (hosz : outSin1.size < UInt256.size)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin0 :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin0, outSin0) false)
    (hdecSin0 :
      config.externalABI.decode? "sin" outSin0 =
        some [.int (Int.ofNat vatSin0.toNat)])
    (hBumpLoad0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hsurplus0 : surplus0 = vatSin0 + BumpVal)
    (hsurplus0Fit : vatSin0.toNat + BumpVal.toNat < UInt256.size)
    (hHumpLoad0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨11⟩ = HumpVal)
    (hsurplusNeed : surplusNeed = surplus0 + HumpVal)
    (hsurplusNeedFit : surplus0.toNat + HumpVal.toNat < UInt256.size)
    (hvatLoadSin0 :
      Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSin0.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin0 (EVM.address (kissVatAddress σ_solm I)) "dai" 0
        [.address I.codeOwner] (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hownerDai : evmDai.executionEnv.codeOwner = I.codeOwner)
    (henough : surplusNeed.toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin1 :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin1 :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin1, outSin1) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin1.size)).toNat =
      outSin1.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd1277' := rd1277
  rw [hmin] at rd1277'
  obtain ⟨_, _, rd1295⟩ :=
    RD.vowFlapSin1CallSuccessToDecode rd1277' (by simp)
  have hmemWrite : (outSin1.write 0 (healSinCalldataMem I mem) 128 outSin1.size).size =
      164 :=
    healSinWrite_size I mem outSin1 outSin1.size hmem (by omega) (by omega)
  have hread64Write :
      (outSin1.write 0 (healSinCalldataMem I mem) 128 outSin1.size).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    healSinWrite_read64 I mem outSin1 outSin1.size hmem hread64 (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outSin1.write 0 (healSinCalldataMem I mem) 128 outSin1.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin1.write 0 (healSinCalldataMem I mem) 128 outSin1.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hrev := RD.vowFlapSin1ReturnDecodeShortReverts rd1295 hshort hosz hmload64
  have hdecSin1 : config.externalABI.decode? "sin" outSin1 = none :=
    vatSinDecode_none_short hshort
  let locals := (∅ : Store)
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
  have hprefix :
      ExecBlock config { contract := contract, locals := locals } evm0 flapPrefixToDaiStmts
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals, evm0, locals4] using
      flapPrefixToDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin0)
        (evmDai := evmDai) (outSin := outSin0) (outDai := outDai)
        (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
        (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
        hwv hvatCode0 hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hsurplus0Fit
        hHumpLoad0 hsurplusNeed hsurplusNeedFit hvatLoadSin0 hvatCodeDai hcallDai
        hdecDai
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
        .reverted := by
    simpa [locals4] using
      flapTailSin1DecodeRevert (σ := σ_solm) (I := I) (evmDai := evmDai)
        (evmSin := evmSin1) (outSin := outSin1)
        (vatSin0 := vatSin0) (surplus0 := surplus0) (surplusNeed := surplusNeed)
        (vatDai := vatDai) hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1
        hdecSin1
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat := execBlock_append hprefix htail
    simpa [flapTransition, flapPrefixToDaiStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable, checkedExternalCallStmts,
      locals, evm0] using hcat
  have hbody :
      ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
    simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow
