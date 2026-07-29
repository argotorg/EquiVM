import Benchmarks.Dss.Vow.FlapSubBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` final `flapper.kick` body-core glue -/

theorem flapPostDaiBeforeKickSuccess
    {σ I} {evmDai evmSin : EVM.State} {outSin : ByteArray}
    {vatSin0 surplus0 surplusNeed vatDai vatSin1 SinVal freeSin AshVal debt : UInt256}
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
    (hdecSin1 :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin1.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin1 SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin1.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : debt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtZero : debt = ⟨0⟩) :
    let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
    let locals7 := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
      vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt
    ExecBlock config { contract := contract, locals := locals4 } evmDai
      flapPostDaiToKickStmts (.ok { contract := contract, locals := locals7 } evmSin) := by
  intro locals4 locals7
  let locals5 := flapLocalsVatSin0Surplus0NeedDaiSin1 vatSin0 surplus0 surplusNeed
    vatDai vatSin1
  let locals6 := flapLocalsVatSin0Surplus0NeedDaiSin1Free vatSin0 surplus0 surplusNeed
    vatDai vatSin1 freeSin
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
          (perm := false))
        (.ok { contract := contract, locals := locals5 } evmSin) := by
    simpa [locals4, locals5, flapLocalsVatSin0Surplus0NeedDaiSin1, collapseReturns] using
      ExecStmt.externalCallSuccess hvatSin1 (by simp [evalExpr?, pure])
        hargsSin1 hcallSin1 hdecSin1
  have hvatSin1Var :
      evalExpr? config { contract := contract, locals := locals5 } evmSin (.var "vatSin1") =
        .ok (.int (Int.ofNat vatSin1.toNat)) := by
    simpa [locals5] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flapLocalsVatSin0Surplus0NeedDaiSin1
          vatSin0 surplus0 surplusNeed vatDai vatSin1)
        (name := "vatSin1") (value := vatSin1)
        (flapLocalsVatSin0Surplus0NeedDaiSin1_get_vatSin1
          vatSin0 surplus0 surplusNeed vatDai vatSin1)
  have hSin :
      evalExpr? config { contract := contract, locals := locals5 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals5, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals5)
        (by simp [locals5, flapLocalsVatSin0Surplus0NeedDaiSin1,
          flapLocalsVatSin0Surplus0NeedDai, flapLocalsVatSin0Surplus0Need,
          flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals5 } evmSin
        [.var "vatSin1", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin1.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSin1Var, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin1.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin1 SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals5 } evmSin
        (.internalCall "sub" [.var "vatSin1", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals6 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin1) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals5, locals6, flapLocalsVatSin0Surplus0NeedDaiSin1Free,
      resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals5 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin1", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin1.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin1 SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin1 SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)])
        hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals6 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals6] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flapLocalsVatSin0Surplus0NeedDaiSin1Free
          vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin)
        (name := "freeSin") (value := freeSin)
        (flapLocalsVatSin0Surplus0NeedDaiSin1Free_get_freeSin
          vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals6 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals6, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals6)
        (by simp [locals6, flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals6 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals6 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "debt")
        (.ok { contract := contract, locals := locals7 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := freeSin) (y := AshVal)
      (diff := debt) hdebt hdebtOk
    simpa [locals6, locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
      resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals6 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "debt")
        (args := [.var "freeSin", .storage AshRef])
        (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ freeSin AshVal debt })
        (value := some [.int (Int.ofNat debt.toNat)])
        hargsDebt (by rfl) hbindDebt hbody)
  have hdebtVar :
      evalExpr? config { contract := contract, locals := locals7 } evmSin (.var "debt") =
        .ok (.int (Int.ofNat debt.toNat)) := by
    simpa [locals7] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
          vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt)
        (name := "debt") (value := debt)
        (flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt_get_debt
          vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt)
  have hreqDebt :
      evalExpr? config { contract := contract, locals := locals7 } evmSin
        (.binary .eq (.var "debt") (.intLit 0)) = .ok (.bool true) := by
    have hzeroNat : debt.toNat = 0 := by
      rw [hdebtZero]
      rfl
    simp [evalExpr?, EvalResult.bind, bind, hdebtVar, evalBinaryOp?, hzeroNat]
  simp only [flapPostDaiToKickStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin1) ?_
  refine ExecBlock.consNormal hcallSin1Stmt ?_
  refine ExecBlock.consNormal hfreeStmt ?_
  refine ExecBlock.consNormal hdebtStmt ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreqDebt) ExecBlock.nil

theorem vowFlapKickNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin0 BumpVal surplus0 HumpVal
      surplusNeed vatDai vatSin1 freeSin debt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin0 evmDai evmSin1 : EVM.State} {mem outSin0 outDai outSin1 : ByteArray}
    {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1403 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1403⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin1 acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hflapperNoCodeEvm :
      Reasoning.Theory.extCodeSizeWord acc.2
        (vowAddressReturnWord ⟨2⟩ acc.2 I) = ⟨0⟩)
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
        [.address I.codeOwner] (true, evmSin1, outSin1) false)
    (hdecSin1 :
      config.externalABI.decode? "sin" outSin1 =
        some [.int (Int.ofNat vatSin1.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ acc.2 I)
    (hfree : freeSin = UInt256.sub vatSin1 (vowSlotWord ⟨5⟩ acc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin1.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ acc.2 I)
    (hdebt : debt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ acc.2 I))
    (hdebtOk : (vowSlotWord ⟨6⟩ acc.2 I).toNat ≤ freeSin.toNat)
    (hdebtZero : debt = ⟨0⟩)
    (hflapperNoCode :
      (UInt256.ofNat
        ((evmSin1.lookupAccount (flapFlapperAddressOf evmSin1)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapKickNoCode rd1403 hmem hread64 hflapperNoCodeEvm
  let locals := (∅ : Store)
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
  let locals7 := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
    vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt
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
  have hpost :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flapPostDaiToKickStmts (.ok { contract := contract, locals := locals7 } evmSin1) := by
    simpa [locals4, locals7] using
      flapPostDaiBeforeKickSuccess (σ := σ_solm) (I := I) (evmDai := evmDai)
        (evmSin := evmSin1) (outSin := outSin1)
        (vatSin0 := vatSin0) (surplus0 := surplus0) (surplusNeed := surplusNeed)
        (vatDai := vatDai) (vatSin1 := vatSin1)
        (SinVal := vowSlotWord ⟨5⟩ acc.2 I) (freeSin := freeSin)
        (AshVal := vowSlotWord ⟨6⟩ acc.2 I) (debt := debt)
        hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad
        hfree hfreeOk hAshLoad hdebt hdebtOk hdebtZero
  have hkick :
      ExecBlock config { contract := contract, locals := locals7 } evmSin1
        flapKickAndReturnStmts .reverted := by
    simpa [locals7] using
      flapKickThenNoCode (evm := evmSin1)
        (vatSin0 := vatSin0) (surplus0 := surplus0) (surplusNeed := surplusNeed)
        (vatDai := vatDai) (vatSin1 := vatSin1) (freeSin := freeSin) (debt := debt)
        hflapperNoCode
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
        .reverted := by
    have hcat := execBlock_append hpost hkick
    simpa [flapTailStmts] using hcat
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

theorem flapSourceKickRevert
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmSin0 evmDai evmSin1 : EVM.State} {outSin0 outDai outSin1 : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed vatDai vatSin1 SinVal freeSin AshVal
      debt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin0 :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
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
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSin0.lookupAccount (kissVatAddress σ I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config evmSin0 (EVM.address (kissVatAddress σ I)) "dai" 0
        [.address I.codeOwner] (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
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
        [.address I.codeOwner] (true, evmSin1, outSin1) false)
    (hdecSin1 :
      config.externalABI.decode? "sin" outSin1 =
        some [.int (Int.ofNat vatSin1.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin1 SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin1.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : debt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtZero : debt = ⟨0⟩)
    (hkick :
      let locals7 := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
        vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt
      ExecBlock config { contract := contract, locals := locals7 } evmSin1
        flapKickAndReturnStmts .reverted) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (∅ : Store)
      flapTransition.body .reverted := by
  let locals := (∅ : Store)
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
  let locals7 := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
    vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt
  have hprefix :
      ExecBlock config { contract := contract, locals := locals } evm0 flapPrefixToDaiStmts
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals, evm0, locals4] using
      flapPrefixToDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin0)
        (evmDai := evmDai) (outSin := outSin0) (outDai := outDai)
        (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
        (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
        hwv hvatCode0 hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hsurplus0Fit
        hHumpLoad0 hsurplusNeed hsurplusNeedFit hvatLoadSin0 hvatCodeDai hcallDai
        hdecDai
  have hpost :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flapPostDaiToKickStmts (.ok { contract := contract, locals := locals7 } evmSin1) := by
    simpa [locals4, locals7] using
      flapPostDaiBeforeKickSuccess (σ := σ) (I := I) (evmDai := evmDai)
        (evmSin := evmSin1) (outSin := outSin1)
        (vatSin0 := vatSin0) (surplus0 := surplus0) (surplusNeed := surplusNeed)
        (vatDai := vatDai) (vatSin1 := vatSin1)
        (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal) (debt := debt)
        hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad
        hfree hfreeOk hAshLoad hdebt hdebtOk hdebtZero
  have hkick' :
      ExecBlock config { contract := contract, locals := locals7 } evmSin1
        flapKickAndReturnStmts .reverted := by
    simpa [locals7] using hkick
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
        .reverted := by
    have hcat := execBlock_append hpost hkick'
    simpa [flapTailStmts] using hcat
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat := execBlock_append hprefix htail
    simpa [flapTransition, flapPrefixToDaiStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable, checkedExternalCallStmts,
      locals, evm0] using hcat
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem vowFlapKickCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatSin0 BumpVal surplus0 HumpVal
      surplusNeed vatDai vatSin1 SinVal freeSin AshVal debt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin0 evmDai evmSin1 evmKick : EVM.State}
    {mem outSin0 outDai outSin1 outKick : ByteArray} {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1498 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨0⟩ :: flapKickEndPtr :: flapKickSelectorWord ::
        target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem aw outKick acc k C)
    (houtKickSize : outKick.size < UInt256.size)
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
        [.address I.codeOwner] (true, evmSin1, outSin1) false)
    (hdecSin1 :
      config.externalABI.decode? "sin" outSin1 =
        some [.int (Int.ofNat vatSin1.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin1 SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin1.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : debt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtZero : debt = ⟨0⟩)
    (hBumpLoad1 :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmSin1.lookupAccount (flapFlapperAddressOf evmSin1)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config evmSin1 (EVM.address (flapFlapperAddressOf evmSin1))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (false, evmKick, outKick) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapKickCallFailure rd1498 houtKickSize (by simp)
  have hkick :
      let locals7 := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
        vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt
      ExecBlock config { contract := contract, locals := locals7 } evmSin1
        flapKickAndReturnStmts .reverted := by
    dsimp
    exact flapKickThenCallFailure (evm := evmSin1) (evmKick := evmKick)
      (outKick := outKick) (vatSin0 := vatSin0) (surplus0 := surplus0)
      (surplusNeed := surplusNeed) (vatDai := vatDai) (vatSin1 := vatSin1)
      (freeSin := freeSin) (debt := debt) (BumpVal := BumpVal)
      hBumpLoad1 hflapperCode hcallKick
  have hbody := flapSourceKickRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
    (outSin0 := outSin0) (outDai := outDai) (outSin1 := outSin1)
    (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
    (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
    (vatSin1 := vatSin1) (SinVal := SinVal)
    (freeSin := freeSin) (AshVal := AshVal) (debt := debt)
    hwv hvatCode0 hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hsurplus0Fit hHumpLoad0
    hsurplusNeed hsurplusNeedFit hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai
    henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad hfree hfreeOk
    hAshLoad hdebt hdebtOk hdebtZero hkick
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapKickDecode_ok {o : ByteArray} (ho32 : 32 ≤ o.size) :
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

theorem flapKickDecode_none_short {o : ByteArray} (hshort : o.size < 32) :
    config.externalABI.decode? "kick" o = none := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o) hshort
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o = none
  unfold decodeReturn?
  rw [hdec']
  rfl

theorem vowFlapKickDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel d0 d1 d2 vatSin0 BumpVal surplus0
      HumpVal surplusNeed vatDai vatSin1 SinVal freeSin AshVal debt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin0 evmDai evmSin1 evmKick : EVM.State}
    {mem outSin0 outDai outSin1 outKick : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1516 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 7) outKick acc k C)
    (hshort : outKick.size < 32)
    (hosz : outKick.size < UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
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
        [.address I.codeOwner] (true, evmSin1, outSin1) false)
    (hdecSin1 :
      config.externalABI.decode? "sin" outSin1 =
        some [.int (Int.ofNat vatSin1.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin1 SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin1.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : debt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtZero : debt = ⟨0⟩)
    (hBumpLoad1 :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmSin1.lookupAccount (flapFlapperAddressOf evmSin1)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config evmSin1 (EVM.address (flapFlapperAddressOf evmSin1))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (true, evmKick, outKick) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapKickReturnDecodeShortReverts rd1516 hshort hosz hmload64
  have hdecKick : config.externalABI.decode? "kick" outKick = none :=
    flapKickDecode_none_short hshort
  have hkick :
      let locals7 := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
        vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt
      ExecBlock config { contract := contract, locals := locals7 } evmSin1
        flapKickAndReturnStmts .reverted := by
    dsimp
    exact flapKickThenDecodeRevert (evm := evmSin1) (evmKick := evmKick)
      (outKick := outKick) (vatSin0 := vatSin0) (surplus0 := surplus0)
      (surplusNeed := surplusNeed) (vatDai := vatDai) (vatSin1 := vatSin1)
      (freeSin := freeSin) (debt := debt) (BumpVal := BumpVal)
      hBumpLoad1 hflapperCode hcallKick hdecKick
  have hbody := flapSourceKickRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
    (outSin0 := outSin0) (outDai := outDai) (outSin1 := outSin1)
    (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
    (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
    (vatSin1 := vatSin1) (SinVal := SinVal)
    (freeSin := freeSin) (AshVal := AshVal) (debt := debt)
    hwv hvatCode0 hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hsurplus0Fit hHumpLoad0
    hsurplusNeed hsurplusNeedFit hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai
    henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad hfree hfreeOk
    hAshLoad hdebt hdebtOk hdebtZero hkick
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapKickSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatSin0 BumpVal surplus0 HumpVal
      surplusNeed vatDai vatSin1 SinVal freeSin AshVal debt id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin0 evmDai evmSin1 evmKick : EVM.State}
    {mem outSin0 outDai outSin1 outKick : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1498 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨1⟩ :: flapKickEndPtr :: flapKickSelectorWord ::
        target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outKick.write 0 (flapKickCalldataMem BumpVal mem) flapKickOutPtr.toNat
        (min flapKickOutSize (UInt256.ofNat outKick.size)).toNat)
      (UInt256.ofNat 7) outKick acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ outKick.size)
    (hosz : outKick.size < UInt256.size)
    (hid : id = UInt256.ofNat (fromByteArrayBigEndian (outKick.extract 0 32)))
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
        [.address I.codeOwner] (true, evmSin1, outSin1) false)
    (hdecSin1 :
      config.externalABI.decode? "sin" outSin1 =
        some [.int (Int.ofNat vatSin1.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin1 SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin1.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : debt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hdebtZero : debt = ⟨0⟩)
    (hBumpLoad1 :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmSin1.lookupAccount (flapFlapperAddressOf evmSin1)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config evmSin1 (EVM.address (flapFlapperAddressOf evmSin1))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (true, evmKick, outKick) true)
    (hcreated : acc.1 = evmKick.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmKick.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hret := RD.vowFlapKickSuccess rd1498 hmem hread64 ho32 hosz hid
  have hdecKick :
      config.externalABI.decode? "kick" outKick =
        some [.int (Int.ofNat id.toNat)] := by
    simpa [hid] using flapKickDecode_ok (o := outKick) ho32
  have hbody := flapSourceBlockSuccess (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
    (evmKick := evmKick) (outSin0 := outSin0) (outDai := outDai)
    (outSin1 := outSin1) (outKick := outKick)
    (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
    (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
    (vatSin1 := vatSin1) (SinVal := SinVal)
    (freeSin := freeSin) (AshVal := AshVal) (debt := debt)
    (id := id)
    hwv hvatCode0 hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hsurplus0Fit hHumpLoad0
    hsurplusNeed hsurplusNeedFit hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai
    henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad hfree hfreeOk
    hAshLoad hdebt hdebtOk hdebtZero hBumpLoad1 hflapperCode hcallKick hdecKick
  have henc :
      returnEquiv (UInt256.toByteArray id)
        (some [.int (Int.ofNat id.toNat)]) flapTransition.returnType := by
    rw [show flapTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding id)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated hAccountsFinal henc

end Benchmarks.Dss.Vow
