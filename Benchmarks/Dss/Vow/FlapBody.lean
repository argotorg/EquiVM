import Benchmarks.Dss.Vow.FlapKick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` source-body scaffolding -/

abbrev flapLocalsVatSin0 (vatSin0 : UInt256) : Store :=
  (∅ : Store).insert "vatSin0" (.int (Int.ofNat vatSin0.toNat))

theorem flapLocalsVatSin0_get_vatSin0 (vatSin0 : UInt256) :
    (flapLocalsVatSin0 vatSin0).get? "vatSin0" =
      some (.int (Int.ofNat vatSin0.toNat)) := by
  rw [flapLocalsVatSin0, store_get_self]

abbrev flapLocalsVatSin0Surplus0 (vatSin0 surplus0 : UInt256) : Store :=
  (flapLocalsVatSin0 vatSin0).insert "surplus0" (.int (Int.ofNat surplus0.toNat))

theorem flapLocalsVatSin0Surplus0_get_surplus0 (vatSin0 surplus0 : UInt256) :
    (flapLocalsVatSin0Surplus0 vatSin0 surplus0).get? "surplus0" =
      some (.int (Int.ofNat surplus0.toNat)) := by
  rw [flapLocalsVatSin0Surplus0, store_get_self]

abbrev flapLocalsVatSin0Surplus0Need
    (vatSin0 surplus0 surplusNeed : UInt256) : Store :=
  (flapLocalsVatSin0Surplus0 vatSin0 surplus0).insert "surplusNeed"
    (.int (Int.ofNat surplusNeed.toNat))

theorem flapLocalsVatSin0Surplus0Need_get_surplusNeed
    (vatSin0 surplus0 surplusNeed : UInt256) :
    (flapLocalsVatSin0Surplus0Need vatSin0 surplus0 surplusNeed).get? "surplusNeed" =
      some (.int (Int.ofNat surplusNeed.toNat)) := by
  rw [flapLocalsVatSin0Surplus0Need, store_get_self]

abbrev flapLocalsVatSin0Surplus0NeedDai
    (vatSin0 surplus0 surplusNeed vatDai : UInt256) : Store :=
  (flapLocalsVatSin0Surplus0Need vatSin0 surplus0 surplusNeed).insert "vatDai"
    (.int (Int.ofNat vatDai.toNat))

theorem flapLocalsVatSin0Surplus0NeedDai_get_vatDai
    (vatSin0 surplus0 surplusNeed vatDai : UInt256) :
    (flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai).get?
      "vatDai" = some (.int (Int.ofNat vatDai.toNat)) := by
  rw [flapLocalsVatSin0Surplus0NeedDai, store_get_self]

theorem flapLocalsVatSin0Surplus0NeedDai_get_surplusNeed
    (vatSin0 surplus0 surplusNeed vatDai : UInt256) :
    (flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai).get?
      "surplusNeed" = some (.int (Int.ofNat surplusNeed.toNat)) := by
  rw [flapLocalsVatSin0Surplus0NeedDai, store_get_ne _ _ (by decide),
    flapLocalsVatSin0Surplus0Need_get_surplusNeed]

abbrev flapLocalsVatSin0Surplus0NeedDaiSin1
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 : UInt256) : Store :=
  (flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai).insert
    "vatSin1" (.int (Int.ofNat vatSin1.toNat))

theorem flapLocalsVatSin0Surplus0NeedDaiSin1_get_vatSin1
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 : UInt256) :
    (flapLocalsVatSin0Surplus0NeedDaiSin1 vatSin0 surplus0 surplusNeed vatDai
      vatSin1).get? "vatSin1" = some (.int (Int.ofNat vatSin1.toNat)) := by
  rw [flapLocalsVatSin0Surplus0NeedDaiSin1, store_get_self]

abbrev flapLocalsVatSin0Surplus0NeedDaiSin1Free
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin : UInt256) : Store :=
  (flapLocalsVatSin0Surplus0NeedDaiSin1 vatSin0 surplus0 surplusNeed vatDai
    vatSin1).insert "freeSin" (.int (Int.ofNat freeSin.toNat))

theorem flapLocalsVatSin0Surplus0NeedDaiSin1Free_get_freeSin
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin : UInt256) :
    (flapLocalsVatSin0Surplus0NeedDaiSin1Free vatSin0 surplus0 surplusNeed vatDai
      vatSin1 freeSin).get? "freeSin" = some (.int (Int.ofNat freeSin.toNat)) := by
  rw [flapLocalsVatSin0Surplus0NeedDaiSin1Free, store_get_self]

abbrev flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt : UInt256) : Store :=
  (flapLocalsVatSin0Surplus0NeedDaiSin1Free vatSin0 surplus0 surplusNeed vatDai
    vatSin1 freeSin).insert "debt" (.int (Int.ofNat debt.toNat))

theorem flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt_get_debt
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt : UInt256) :
    (flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt vatSin0 surplus0 surplusNeed
      vatDai vatSin1 freeSin debt).get? "debt" =
      some (.int (Int.ofNat debt.toNat)) := by
  rw [flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt, store_get_self]

abbrev flapLocalsDone
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id : UInt256) : Store :=
  (flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt vatSin0 surplus0 surplusNeed
    vatDai vatSin1 freeSin debt).insert "id" (.int (Int.ofNat id.toNat))

theorem flapLocalsDone_get_id
    (vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id : UInt256) :
    (flapLocalsDone vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id).get?
      "id" = some (.int (Int.ofNat id.toNat)) := by
  rw [flapLocalsDone, store_get_self]

def flapPrefixToDaiStmts : List Stmt :=
  nonpayable ++
  checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin0"
    (perm := false) ++
  [ .internalCall "add" [.var "vatSin0", .storage bumpRef] "surplus0",
    .internalCall "add" [.var "surplus0", .storage humpRef] "surplusNeed" ] ++
  checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
    (perm := false)

def flapPostDaiToKickStmts : List Stmt :=
  [ .require (.binary .ge (.var "vatDai") (.var "surplusNeed")) ] ++
  checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin1"
    (perm := false) ++
  [ .internalCall "sub" [.var "vatSin1", .storage SinRef] "freeSin",
    .internalCall "sub" [.var "freeSin", .storage AshRef] "debt",
    .require (.binary .eq (.var "debt") (.intLit 0)) ]

def flapKickAndReturnStmts : List Stmt :=
  checkedExternalCallStmts (.storage flapperRef) "kick" (.intLit 0)
    [.storage bumpRef, .intLit 0] "id" ++
  [ .return [.var "id"] ]

def flapTailStmts : List Stmt :=
  flapPostDaiToKickStmts ++ flapKickAndReturnStmts

def flapFlapperAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      solcAddrMask).toNat

theorem evalExpr_flapFlapperStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "flapper" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage flapperRef) =
      .ok (.address (flapFlapperAddressOf evm)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "flapper", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_address_offset0 evm ⟨2⟩)
  · exact hbase
  · simp [flapperRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

abbrev flapBumpEvaledRef : EvaledStorageRef :=
  { base := "bump", steps := [] }

theorem evalExpr_flapBumpStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "bump" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage bumpRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := flapBumpEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨10⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨10⟩)
  · exact hbase
  · simp [flapBumpEvaledRef, bumpRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, flapBumpEvaledRef]

abbrev flapHumpEvaledRef : EvaledStorageRef :=
  { base := "hump", steps := [] }

theorem evalExpr_flapHumpStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "hump" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage humpRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := flapHumpEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨11⟩)
  · exact hbase
  · simp [flapHumpEvaledRef, humpRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, flapHumpEvaledRef]

theorem flapEvalExpr_extCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem flapEvalExpr_extCodeGuard_false {evm : EVM.State} {locals : Store}
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

theorem flapStorageLoad_codeOwner_eq_vowSlotWord (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      vowSlotWord slot evm.accountMap I := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, vowSlotWord,
    solcSlotWord, howner]

theorem flapFlapperAddressOf_eq_vowAddressReturnWord (evm : EVM.State)
    (I : ExecutionEnv) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    flapFlapperAddressOf evm =
      AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ evm.accountMap I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [flapFlapperAddressOf, vowAddressReturnWord,
    flapStorageLoad_codeOwner_eq_vowSlotWord evm I ⟨2⟩ howner]

theorem flapFlapperCode_pos_of_codeSize_ne (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (vowAddressReturnWord ⟨2⟩ evm.accountMap I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := vowAddressReturnWord ⟨2⟩ evm.accountMap I)
      (addr := flapFlapperAddressOf evm)
      (flapFlapperAddressOf_eq_vowAddressReturnWord evm I howner) hne

theorem flapFlapperCode_zero_of_codeSize_zero (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (vowAddressReturnWord ⟨2⟩ evm.accountMap I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := vowAddressReturnWord ⟨2⟩ evm.accountMap I)
      (addr := flapFlapperAddressOf evm)
      (flapFlapperAddressOf_eq_vowAddressReturnWord evm I howner) hzero

theorem flapPrefixToDaiSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed vatDai : UInt256}
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
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)]) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
    ExecBlock config { contract := contract, locals := locals } evm0 flapPrefixToDaiStmts
      (.ok { contract := contract, locals := locals4 } evmDai) := by
  intro locals evm0 locals4
  let locals1 := flapLocalsVatSin0 vatSin0
  let locals2 := flapLocalsVatSin0Surplus0 vatSin0 surplus0
  let locals3 := flapLocalsVatSin0Surplus0Need vatSin0 surplus0 surplusNeed
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
          (perm := false))
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals3, locals4, flapLocalsVatSin0Surplus0NeedDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvatDai (by simp [evalExpr?, pure])
        hargsDai hcallDai hdecDai
  simp only [flapPrefixToDaiStmts, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  refine ExecBlock.consNormal hcallSinStmt ?_
  refine ExecBlock.consNormal hsurplus0Stmt ?_
  refine ExecBlock.consNormal hsurplusNeedStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDai) ?_
  exact ExecBlock.consNormal hcallDaiStmt ExecBlock.nil

theorem flapSourceSurplus0AddOverflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State} {outSin : ByteArray}
    {vatSin0 BumpVal : UInt256}
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
    (hover : UInt256.size ≤ vatSin0.toNat + BumpVal.toNat) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  let locals1 := flapLocalsVatSin0 vatSin0
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
  have hargsAdd :
      evalExprs? config { contract := contract, locals := locals1 } evmSin
        [.var "vatSin0", .storage bumpRef] =
          .ok [.int (Int.ofNat vatSin0.toNat), .int (Int.ofNat BumpVal.toNat)] := by
    simp [evalExprs?, hvatSin0Var, hbump, EvalResult.bind, bind, pure]
  have hbindAdd :
      bindParams? addFunction.params
          [.int (Int.ofNat vatSin0.toNat), .int (Int.ofNat BumpVal.toNat)] =
        some (uintBinaryLocals vatSin0 BumpVal) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmSin
        (.internalCall "add" [.var "vatSin0", .storage bumpRef] "surplus0") .reverted := by
    have hbody := execAddFunctionRevert (evm := evmSin) (x := vatSin0) (y := BumpVal) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals1 })
      (evm := evmSin) (name := "add") (retVar := "surplus0")
      (args := [.var "vatSin0", .storage bumpRef])
      (argVals := [.int (Int.ofNat vatSin0.toNat), .int (Int.ofNat BumpVal.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals vatSin0 BumpVal)
      hargsAdd (by rfl) hbindAdd hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    exact ExecBlock.consRevert haddStmt
  simpa [ExecTransitionBody, evm0, locals, flapTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem flapSourceSurplusNeedAddOverflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State} {outSin : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal : UInt256}
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
    (hover : UInt256.size ≤ surplus0.toNat + HumpVal.toNat) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
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
  have hargsAdd :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "surplus0", .storage humpRef] =
          .ok [.int (Int.ofNat surplus0.toNat), .int (Int.ofNat HumpVal.toNat)] := by
    simp [evalExprs?, hsurplus0Var, hhump, EvalResult.bind, bind, pure]
  have hbindAdd :
      bindParams? addFunction.params
          [.int (Int.ofNat surplus0.toNat), .int (Int.ofNat HumpVal.toNat)] =
        some (uintBinaryLocals surplus0 HumpVal) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "add" [.var "surplus0", .storage humpRef] "surplusNeed") .reverted := by
    have hbody := execAddFunctionRevert (evm := evmSin) (x := surplus0) (y := HumpVal) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals2 })
      (evm := evmSin) (name := "add") (retVar := "surplusNeed")
      (args := [.var "surplus0", .storage humpRef])
      (argVals := [.int (Int.ofNat surplus0.toNat), .int (Int.ofNat HumpVal.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals surplus0 HumpVal)
      hargsAdd (by rfl) hbindAdd hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hsurplus0Stmt ?_
    exact ExecBlock.consRevert haddStmt
  simpa [ExecTransitionBody, evm0, locals, flapTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem flapSourceInsufficientSurplus
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin evmDai : EVM.State}
    {outSin outDai : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed vatDai : UInt256}
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
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hinsuff : vatDai.toNat < surplusNeed.toNat) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
  have hprefix :
      ExecBlock config { contract := contract, locals := locals } evm0 flapPrefixToDaiStmts
        (.ok { contract := contract, locals := locals4 } evmDai) := by
    simpa [locals, evm0, locals4] using
      flapPrefixToDaiSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (evmSin := evmSin)
        (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
        (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
        (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
        hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit
        hHumpLoad hsurplusNeed hsurplusNeedFit hvatLoadSin hvatCodeDai hcallDai hdecDai
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
        (.binary .ge (.var "vatDai") (.var "surplusNeed")) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hvatDaiVar, hsurplusNeedVar, evalBinaryOp?]
    exact_mod_cast hinsuff
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
        .reverted := by
    simp only [flapTailStmts, flapPostDaiToKickStmts, checkedExternalCallStmts,
      List.cons_append, List.nil_append]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqSurplus)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    have hcat := Reasoning.Refinement.execBlock_append hprefix htail
    simpa [flapTransition, flapPrefixToDaiStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable,
      checkedExternalCallStmts, locals, evm0] using hcat
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flapKickThenNoCode
    {evm : EVM.State}
    {vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt : UInt256}
    (hflapperNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    let locals7 :=
      flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt vatSin0 surplus0 surplusNeed
        vatDai vatSin1 freeSin debt
    ExecBlock config { contract := contract, locals := locals7 } evm
      flapKickAndReturnStmts .reverted := by
  intro locals7
  have hflapper :
      evalExpr? config { contract := contract, locals := locals7 } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
      flapLocalsVatSin0Surplus0NeedDaiSin1Free,
      flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
      flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0] using
      evalExpr_flapFlapperStorage (evm := evm) (locals := locals7)
        (by simp [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
          flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hguard :
    evalExpr? config { contract := contract, locals := locals7 } evm
        (.binary .gt (.extCodeSize (.storage flapperRef)) (.intLit 0)) =
          .ok (.bool false) :=
    flapEvalExpr_extCodeGuard_false hflapper hflapperNoCode
  simp only [flapKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem flapKickThenCallFailure
    {evm evmKick : EVM.State} {outKick : ByteArray}
    {vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt BumpVal : UInt256}
    (hBumpLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config evm (EVM.address (flapFlapperAddressOf evm))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (false, evmKick, outKick) true) :
    let locals7 :=
      flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt vatSin0 surplus0 surplusNeed
        vatDai vatSin1 freeSin debt
    ExecBlock config { contract := contract, locals := locals7 } evm
      flapKickAndReturnStmts .reverted := by
  intro locals7
  have hflapper :
      evalExpr? config { contract := contract, locals := locals7 } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
      flapLocalsVatSin0Surplus0NeedDaiSin1Free,
      flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
      flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0] using
      evalExpr_flapFlapperStorage (evm := evm) (locals := locals7)
        (by simp [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
          flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hguard :
    evalExpr? config { contract := contract, locals := locals7 } evm
        (.binary .gt (.extCodeSize (.storage flapperRef)) (.intLit 0)) =
          .ok (.bool true) :=
    flapEvalExpr_extCodeGuard_true hflapper hflapperCode
  have hbump :
      evalExpr? config { contract := contract, locals := locals7 } evm (.storage bumpRef) =
        .ok (.int (Int.ofNat BumpVal.toNat)) := by
    simpa [hBumpLoad] using
      evalExpr_flapBumpStorage (evm := evm) (locals := locals7)
        (by simp [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
          flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hzero :
      evalExpr? config { contract := contract, locals := locals7 } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hargs :
      evalExprs? config { contract := contract, locals := locals7 } evm
        [.storage bumpRef, .intLit 0] =
          .ok [.int (Int.ofNat BumpVal.toNat), .int 0] := by
    simp [evalExprs?, hbump, hzero, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals7 } evm
        (.externalCall (.storage flapperRef) "kick" (.intLit 0)
          [.storage bumpRef, .intLit 0] "id")
        .reverted := by
    exact ExecStmt.externalCallFailure hflapper (by simp [evalExpr?, pure]) hargs hcallKick
  simp only [flapKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consRevert hcallStmt

theorem flapKickThenDecodeRevert
    {evm evmKick : EVM.State} {outKick : ByteArray}
    {vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt BumpVal : UInt256}
    (hBumpLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config evm (EVM.address (flapFlapperAddressOf evm))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (true, evmKick, outKick) true)
    (hdecKick : config.externalABI.decode? "kick" outKick = none) :
    let locals7 :=
      flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt vatSin0 surplus0 surplusNeed
        vatDai vatSin1 freeSin debt
    ExecBlock config { contract := contract, locals := locals7 } evm
      flapKickAndReturnStmts .reverted := by
  intro locals7
  have hflapper :
      evalExpr? config { contract := contract, locals := locals7 } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
      flapLocalsVatSin0Surplus0NeedDaiSin1Free,
      flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
      flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0] using
      evalExpr_flapFlapperStorage (evm := evm) (locals := locals7)
        (by simp [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
          flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hguard :
    evalExpr? config { contract := contract, locals := locals7 } evm
        (.binary .gt (.extCodeSize (.storage flapperRef)) (.intLit 0)) =
          .ok (.bool true) :=
    flapEvalExpr_extCodeGuard_true hflapper hflapperCode
  have hbump :
      evalExpr? config { contract := contract, locals := locals7 } evm (.storage bumpRef) =
        .ok (.int (Int.ofNat BumpVal.toNat)) := by
    simpa [hBumpLoad] using
      evalExpr_flapBumpStorage (evm := evm) (locals := locals7)
        (by simp [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
          flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hzero :
      evalExpr? config { contract := contract, locals := locals7 } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hargs :
      evalExprs? config { contract := contract, locals := locals7 } evm
        [.storage bumpRef, .intLit 0] =
          .ok [.int (Int.ofNat BumpVal.toNat), .int 0] := by
    simp [evalExprs?, hbump, hzero, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals7 } evm
        (.externalCall (.storage flapperRef) "kick" (.intLit 0)
          [.storage bumpRef, .intLit 0] "id")
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hflapper (by simp [evalExpr?, pure])
      hargs hcallKick hdecKick
  simp only [flapKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consRevert hcallStmt

theorem flapKickThenSuccess
    {evm evmKick : EVM.State} {outKick : ByteArray}
    {vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt BumpVal id : UInt256}
    (hBumpLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (flapFlapperAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config evm (EVM.address (flapFlapperAddressOf evm))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (true, evmKick, outKick) true)
    (hdecKick :
      config.externalABI.decode? "kick" outKick =
        some [.int (Int.ofNat id.toNat)]) :
    let locals7 :=
      flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt vatSin0 surplus0 surplusNeed
        vatDai vatSin1 freeSin debt
    let locals8 := flapLocalsDone vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id
    ExecBlock config { contract := contract, locals := locals7 } evm
      flapKickAndReturnStmts
      (.returned { contract := contract, locals := locals8 } evmKick
        (some [.int (Int.ofNat id.toNat)])) := by
  intro locals7 locals8
  have hflapper :
      evalExpr? config { contract := contract, locals := locals7 } evm (.storage flapperRef) =
        .ok (.address (flapFlapperAddressOf evm)) := by
    simpa [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
      flapLocalsVatSin0Surplus0NeedDaiSin1Free,
      flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
      flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0] using
      evalExpr_flapFlapperStorage (evm := evm) (locals := locals7)
        (by simp [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
          flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hguard :
    evalExpr? config { contract := contract, locals := locals7 } evm
        (.binary .gt (.extCodeSize (.storage flapperRef)) (.intLit 0)) =
          .ok (.bool true) :=
    flapEvalExpr_extCodeGuard_true hflapper hflapperCode
  have hbump :
      evalExpr? config { contract := contract, locals := locals7 } evm (.storage bumpRef) =
        .ok (.int (Int.ofNat BumpVal.toNat)) := by
    simpa [hBumpLoad] using
      evalExpr_flapBumpStorage (evm := evm) (locals := locals7)
        (by simp [locals7, flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt,
          flapLocalsVatSin0Surplus0NeedDaiSin1Free,
          flapLocalsVatSin0Surplus0NeedDaiSin1, flapLocalsVatSin0Surplus0NeedDai,
          flapLocalsVatSin0Surplus0Need, flapLocalsVatSin0Surplus0, flapLocalsVatSin0])
  have hzero :
      evalExpr? config { contract := contract, locals := locals7 } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hargs :
      evalExprs? config { contract := contract, locals := locals7 } evm
        [.storage bumpRef, .intLit 0] =
          .ok [.int (Int.ofNat BumpVal.toNat), .int 0] := by
    simp [evalExprs?, hbump, hzero, EvalResult.bind, bind, pure]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals7 } evm
        (.externalCall (.storage flapperRef) "kick" (.intLit 0)
          [.storage bumpRef, .intLit 0] "id")
        (.ok { contract := contract, locals := locals8 } evmKick) := by
    simpa [locals8, flapLocalsDone, collapseReturns] using
      ExecStmt.externalCallSuccess hflapper (by simp [evalExpr?, pure])
        hargs hcallKick hdecKick
  have hid :
      evalExpr? config { contract := contract, locals := locals8 } evmKick (.var "id") =
        .ok (.int (Int.ofNat id.toNat)) := by
    simpa [locals8] using
      evalExpr_varUInt256 (evm := evmKick)
        (locals := flapLocalsDone vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id)
        (name := "id") (value := id)
        (flapLocalsDone_get_id vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id)
  simp only [flapKickAndReturnStmts, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  refine ExecBlock.consNormal hcallStmt ?_
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hid))

theorem flapPostDaiToKickSuccess
    {σ I} {evmDai evmSin evmKick : EVM.State} {outSin outKick : ByteArray}
    {vatSin0 surplus0 surplusNeed vatDai vatSin1 SinVal freeSin AshVal debt BumpVal id :
      UInt256}
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
    (hdebtZero : debt = ⟨0⟩)
    (hBumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨10⟩ = BumpVal)
    (hflapperCode :
      0 < (UInt256.ofNat
        ((evmSin.lookupAccount (flapFlapperAddressOf evmSin)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallKick :
      typedCallViaEVM config evmSin (EVM.address (flapFlapperAddressOf evmSin))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (true, evmKick, outKick) true)
    (hdecKick :
      config.externalABI.decode? "kick" outKick =
        some [.int (Int.ofNat id.toNat)]) :
    let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
    let locals8 := flapLocalsDone vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id
    ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
      (.returned { contract := contract, locals := locals8 } evmKick
        (some [.int (Int.ofNat id.toNat)])) := by
  intro locals4 locals8
  let locals5 := flapLocalsVatSin0Surplus0NeedDaiSin1 vatSin0 surplus0 surplusNeed
    vatDai vatSin1
  let locals6 := flapLocalsVatSin0Surplus0NeedDaiSin1Free vatSin0 surplus0 surplusNeed
    vatDai vatSin1 freeSin
  let locals7 := flapLocalsVatSin0Surplus0NeedDaiSin1FreeDebt vatSin0 surplus0 surplusNeed
    vatDai vatSin1 freeSin debt
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
  have hpost :
      ExecBlock config { contract := contract, locals := locals4 } evmDai
        flapPostDaiToKickStmts (.ok { contract := contract, locals := locals7 } evmSin) := by
    simp only [flapPostDaiToKickStmts, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin1) ?_
    refine ExecBlock.consNormal hcallSin1Stmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    refine ExecBlock.consNormal hdebtStmt ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hreqDebt) ExecBlock.nil
  have hkick :
      ExecBlock config { contract := contract, locals := locals7 } evmSin
        flapKickAndReturnStmts
        (.returned { contract := contract, locals := locals8 } evmKick
          (some [.int (Int.ofNat id.toNat)])) := by
    simpa [locals7, locals8] using
      flapKickThenSuccess (evm := evmSin) (evmKick := evmKick) (outKick := outKick)
        (vatSin0 := vatSin0) (surplus0 := surplus0) (surplusNeed := surplusNeed)
        (vatDai := vatDai) (vatSin1 := vatSin1) (freeSin := freeSin) (debt := debt)
        (BumpVal := BumpVal) (id := id)
        hBumpLoad hflapperCode hcallKick hdecKick
  have htail := Reasoning.Refinement.execBlock_append hpost hkick
  simpa [flapTailStmts] using htail

theorem flapSourceBlockSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmSin0 evmDai evmSin1 evmKick : EVM.State}
    {outSin0 outDai outSin1 outKick : ByteArray}
    {vatSin0 BumpVal surplus0 HumpVal surplusNeed vatDai vatSin1 SinVal freeSin AshVal
      debt id : UInt256}
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
    (hSinLoad1 :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin1 SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin1.toNat)
    (hAshLoad1 :
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
    (hdecKick :
      config.externalABI.decode? "kick" outKick =
        some [.int (Int.ofNat id.toNat)]) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let locals8 := flapLocalsDone vatSin0 surplus0 surplusNeed vatDai vatSin1 freeSin debt id
    ExecTransitionBody config contract evm0 locals flapTransition.body
      (.returned { contract := contract, locals := locals8 } evmKick
        (some [.int (Int.ofNat id.toNat)])) := by
  intro locals evm0 locals8
  let locals4 := flapLocalsVatSin0Surplus0NeedDai vatSin0 surplus0 surplusNeed vatDai
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
  have htail :
      ExecBlock config { contract := contract, locals := locals4 } evmDai flapTailStmts
        (.returned { contract := contract, locals := locals8 } evmKick
          (some [.int (Int.ofNat id.toNat)])) := by
    simpa [locals4, locals8] using
      flapPostDaiToKickSuccess (σ := σ) (I := I) (evmDai := evmDai)
        (evmSin := evmSin1) (evmKick := evmKick) (outSin := outSin1)
        (outKick := outKick) (vatSin0 := vatSin0) (surplus0 := surplus0)
        (surplusNeed := surplusNeed) (vatDai := vatDai) (vatSin1 := vatSin1)
        (SinVal := SinVal) (freeSin := freeSin) (AshVal := AshVal) (debt := debt)
        (BumpVal := BumpVal) (id := id) hownerDai henough hvatLoadDai hvatCodeSin1
        hcallSin1 hdecSin1 hSinLoad1 hfree hfreeOk hAshLoad1 hdebt hdebtOk hdebtZero
        hBumpLoad1 hflapperCode hcallKick hdecKick
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        (.returned { contract := contract, locals := locals8 } evmKick
          (some [.int (Int.ofNat id.toNat)])) := by
    have hcat := Reasoning.Refinement.execBlock_append hprefix htail
    simpa [flapTransition, flapPrefixToDaiStmts, flapTailStmts,
      flapPostDaiToKickStmts, flapKickAndReturnStmts, nonpayable,
      checkedExternalCallStmts, locals, evm0] using hcat
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRet hblock

theorem vowFlapSurplus0AddOverflowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin0 BumpVal : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd978 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨978⟩
      (vatSin0 :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
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
    (hBumpEvm : BumpVal = vowSlotWord ⟨10⟩ acc.2 I)
    (hover : UInt256.size ≤ vatSin0.toNat + BumpVal.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hoverEvm :
      UInt256.size ≤ vatSin0.toNat + (vowSlotWord ⟨10⟩ acc.2 I).toNat := by
    simpa [← hBumpEvm] using hover
  have hrev := RD.vowFlapSurplus0AddOverflow (vatSin := vatSin0) rd978 hoverEvm
  have hbody := flapSourceSurplus0AddOverflow (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) (vatSin0 := vatSin0) (BumpVal := BumpVal)
    hwv hvatCode hcallSin hdecSin hBumpLoad hover
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapSurplusNeedAddOverflowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin0 BumpVal surplus0 HumpVal : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd985 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨985⟩
      (surplus0 :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
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
    (hHumpEvm : HumpVal = vowSlotWord ⟨11⟩ acc.2 I)
    (hover : UInt256.size ≤ surplus0.toNat + HumpVal.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hoverEvm :
      UInt256.size ≤ surplus0.toNat + (vowSlotWord ⟨11⟩ acc.2 I).toNat := by
    simpa [← hHumpEvm] using hover
  have hrev := RD.vowFlapSurplusNeedAddOverflow rd985 hoverEvm
  have hbody := flapSourceSurplusNeedAddOverflow (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) (vatSin0 := vatSin0)
    (BumpVal := BumpVal) (surplus0 := surplus0) (HumpVal := HumpVal)
    hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit hHumpLoad hover
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapDai0InsufficientSurplusBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin0 BumpVal surplus0 HumpVal surplusNeed
      vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin evmDai : EVM.State} {mem outSin outDai : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd1113 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1113⟩
      (vatDai :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outDai acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
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
        [.address I.codeOwner] (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hinsuff : vatDai.toNat < surplusNeed.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapDai0InsufficientSurplus rd1113 hinsuff hmem hread64
  have hbody := flapSourceInsufficientSurplus (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (evmDai := evmDai) (outSin := outSin) (outDai := outDai)
    (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
    (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
    hwv hvatCode hcallSin hdecSin hBumpLoad hsurplus0 hsurplus0Fit hHumpLoad
    hsurplusNeed hsurplusNeedFit hvatLoadSin hvatCodeDai hcallDai hdecDai hinsuff
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow
