import Benchmarks.Dss.GemJoin.ConstructorBase

/-!
# MakerDAO/Sky DSS GemJoin constructor Solm source semantics
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

private theorem evm_address_account (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  change a.val % EVM.addressModulus = a.val
  exact Nat.mod_eq_of_lt a.isLt

abbrev gemJoinCtorAfterInitStores (evm : EVM.State) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) : EVM.State :=
  gemJoinCtorAfterGemState
    (gemJoinCtorAfterIlkState
      (gemJoinCtorAfterVatState
        (gemJoinCtorAfterLiveState
          (gemJoinCtorAfterWardsState evm))
        vat)
      ilk)
    gem

theorem evalExpr_gemJoinCtorLocalVat {evm : EVM.State} (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    evalExpr? config { contract := contract, locals := gemJoinCtorLocals vat ilk gem } evm
      (.var "vat_") = .ok (.address vat) := by
  simp only [evalExpr?]
  rw [show (gemJoinCtorLocals vat ilk gem).get? "vat_" = some (.address vat) by
    unfold gemJoinCtorLocals
    simp [Std.HashMap.getElem_insert]]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_gemJoinCtorLocalIlk {evm : EVM.State} (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    evalExpr? config { contract := contract, locals := gemJoinCtorLocals vat ilk gem } evm
      (.var "ilk_") = .ok (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) := by
  simp only [evalExpr?]
  rw [show (gemJoinCtorLocals vat ilk gem).get? "ilk_" =
      some (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) by
    unfold gemJoinCtorLocals
    simp [Std.HashMap.getElem_insert]]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_gemJoinCtorLocalGem {evm : EVM.State} (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    evalExpr? config { contract := contract, locals := gemJoinCtorLocals vat ilk gem } evm
      (.var "gem_") = .ok (.address gem) := by
  simp only [evalExpr?]
  rw [show (gemJoinCtorLocals vat ilk gem).get? "gem_" = some (.address gem) by
    unfold gemJoinCtorLocals
    rw [store_get_self]]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_gemJoinCtorDecimalsRet {evm : EVM.State} (vat : AccountAddress)
    (ilk dec : UInt256) (gem : AccountAddress) :
    evalExpr? config
      { contract := contract,
        locals := (gemJoinCtorLocals vat ilk gem).insert "decimalsRet"
          (.int (Int.ofNat dec.toNat)) } evm
      (.var "decimalsRet") = .ok (.int (Int.ofNat dec.toNat)) := by
  simp [evalExpr?, EvalResult.ofOption]

theorem assign_gemJoinCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := gemJoinCtorAfterWardsState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some evm' := by
    simpa [evm', gemJoinCtorAfterWardsState] using
      storageLocStore_uint256 evm (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

private theorem assign_gemJoinCtorAddressStorage (evm : EVM.State) (locals : Store)
    (ref : StorageRef) (er : EvaledStorageRef) (slot : UInt256) (addrValue : AccountAddress)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (EVM.word addrValue.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ref (.address addrValue) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address addrValue : Value) =
        .address (AccountAddress.ofNat (EVM.word addrValue.val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  have hstore :
      storageLocStore evm (addrLoc slot)
          (.address (AccountAddress.ofNat (EVM.word addrValue.val).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm slot (EVM.word addrValue.val)
        (word_val_addr_canonical addrValue)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc slot)
    (hbase := hbase)
    (her := her)
    (hty := hty)
    (hloc := hloc)
    (hscalar := by trivial)
    (hstore := hstore)

private theorem assign_gemJoinCtorUint256Storage (evm : EVM.State) (locals : Store)
    (ref : StorageRef) (er : EvaledStorageRef) (slot value : UInt256)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some uint256St)
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ref (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := er)
      (loc := wordLoc slot)
      (hbase := hbase)
      (her := her)
      (hty := hty)
      (hloc := hloc)
  simpa [evm'] using storageLocStore_uint256 evm slot value

private theorem valueToWord_ctorIlk (ilk : UInt256) :
    valueToWord (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) = some ilk := by
  have hlen : (EVM.Word.toBytesBE ilk).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size ilk
  have hword : EVM.Word.ofNat (fromBytesBigEndian (EVM.Word.toBytesBE ilk)) = ilk := by
    apply u256_inj
    have hfrom : fromBytesBigEndian (EVM.Word.toBytesBE ilk) = ilk.toNat := by
      have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray ilk)
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        h.trans (fromByteArrayBigEndian_toByteArray ilk)
    rw [EVM.Word.ofNat, hfrom]
    exact Nat.mod_eq_of_lt ilk.val.isLt
  simp [valueToWord, bytes32Width, hlen, hword]

private theorem assign_gemJoinCtorBytes32Storage (evm : EVM.State) (locals : Store)
    (ref : StorageRef) (er : EvaledStorageRef) (slot word : UInt256)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some bytes32St)
    (hloc : config.storage.layout er = fun _ => some (bytes32Loc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ref (.fixedBytes bytes32Width (EVM.Word.toBytesBE word)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar_value
      (ty := bytes32St)
      (loc := bytes32Loc slot)
      (hbase := hbase)
      (her := her)
      (hty := hty)
      (hloc := hloc)
      (hscalar := by trivial)
  simpa [bytes32Loc, Reasoning.Theory.bytes32Loc, bytes32Width, evm'] using
    Reasoning.Theory.storageLocStore_bytes32 evm slot word
      (.fixedBytes bytes32Width (EVM.Word.toBytesBE word)) (valueToWord_ctorIlk word)

theorem assign_gemJoinCtorLiveStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "live" = none) :
    let evm' := gemJoinCtorAfterLiveState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [gemJoinCtorAfterLiveState] using
    assign_gemJoinCtorUint256Storage evm locals liveRef { base := "live", steps := [] } ⟨5⟩
      ⟨1⟩
      (by simpa [liveRef] using hbase)
      (by simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_gemJoinCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := gemJoinCtorAfterVatState evm vat
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_gemJoinCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨1⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_gemJoinCtorIlkStorage (evm : EVM.State) (locals : Store)
    (ilk : UInt256) (hbase : locals.get? "ilk" = none) :
    let evm' := gemJoinCtorAfterIlkState evm ilk
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ilkRef (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_gemJoinCtorBytes32Storage evm locals ilkRef { base := "ilk", steps := [] } ⟨2⟩ ilk
    (by simpa [ilkRef] using hbase)
    (by simp [ilkRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_gemJoinCtorGemStorage (evm : EVM.State) (locals : Store)
    (gem : AccountAddress) (hbase : locals.get? "gem" = none) :
    let evm' := gemJoinCtorAfterGemState evm gem
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage gemRef (.address gem) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_gemJoinCtorAddressStorage evm locals gemRef { base := "gem", steps := [] } ⟨3⟩ gem
    (by simpa [gemRef] using hbase)
    (by simp [gemRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_gemJoinCtorDecStorage (evm : EVM.State) (locals : Store)
    (dec : UInt256) (hbase : locals.get? "dec" = none) :
    let evm' := gemJoinCtorAfterDecState evm dec
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage decRef (.int (Int.ofNat dec.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [gemJoinCtorAfterDecState] using
    assign_gemJoinCtorUint256Storage evm locals decRef { base := "dec", steps := [] } ⟨4⟩
      dec
      (by simpa [decRef] using hbase)
      (by simp [decRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem evalExpr_gemJoinCtorGemCodeGuard_true (evm : EVM.State)
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hcode :
      0 < (EVM.Word.ofNat
        ((evm.lookupAccount (EVM.address gem)).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := gemJoinCtorLocals vat ilk gem } evm
      (.binary .gt (.extCodeSize (.var "gem_")) (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?]
  rw [show (gemJoinCtorLocals vat ilk gem).get? "gem_" = some (.address gem) by
    unfold gemJoinCtorLocals
    rw [store_get_self]]
  unfold EvalResult.ofOption
  simp only [EvalResult.bind, bind, pure, evalBinaryOp?]
  change EvalResult.ok
      (Value.bool (decide (Int.ofNat
        (EVM.Word.ofNat
          (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat >
            0))) =
    EvalResult.ok (Value.bool true)
  have hcode' :
      0 < (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat := by
    simpa [evm_address_account gem] using hcode
  have hgt : Int.ofNat
      (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat >
        0 := by
    simpa [gt_iff_lt] using Int.natCast_pos.mpr hcode'
  rw [show decide (Int.ofNat
      (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat >
        0) = true from decide_eq_true hgt]

theorem evalExpr_gemJoinCtorGemCodeGuard_false (evm : EVM.State)
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hcode :
      ¬ 0 < (EVM.Word.ofNat
        ((evm.lookupAccount (EVM.address gem)).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := gemJoinCtorLocals vat ilk gem } evm
      (.binary .gt (.extCodeSize (.var "gem_")) (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?]
  rw [show (gemJoinCtorLocals vat ilk gem).get? "gem_" = some (.address gem) by
    unfold gemJoinCtorLocals
    rw [store_get_self]]
  unfold EvalResult.ofOption
  simp only [EvalResult.bind, bind, pure, evalBinaryOp?]
  change EvalResult.ok
      (Value.bool (decide (Int.ofNat
        (EVM.Word.ofNat
          (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat >
            0))) =
    EvalResult.ok (Value.bool false)
  have hcode' :
      ¬ 0 < (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat := by
    simpa [evm_address_account gem] using hcode
  have hnot : ¬ Int.ofNat
      (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat >
        0 := by
    intro hgt
    apply hcode'
    exact Int.natCast_pos.mp (by simpa [gt_iff_lt] using hgt)
  rw [show decide (Int.ofNat
      (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size) (State.lookupAccount evm gem))).toNat >
        0) = false from decide_eq_false hnot]

theorem evalExprs_gemJoinCtorDecimalsArgs (evm : EVM.State) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    evalExprs? config { contract := contract, locals := gemJoinCtorLocals vat ilk gem } evm [] =
      .ok [] := by
  rfl

theorem gemJoinCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    {evmDecimals : EVM.State} {outDecimals : ByteArray} {dec : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      0 < UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))))
    (hcallDecimals :
      typedCallViaEVM config
        (gemJoinCtorAfterInitStores
          (initState createdAccounts genesisBlockHeader blocks σ σ₀
            (Sat256.ofUInt256 g) A I)
          vat ilk gem)
        (EVM.address gem) "decimals" 0 [] (true, evmDecimals, outDecimals) false)
    (hdecDecimals : config.externalABI.decode? "decimals" outDecimals =
      some [.int (Int.ofNat dec.toNat)]) :
    let locals := gemJoinCtorLocals vat ilk gem
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := gemJoinCtorAfterWardsState evm0
    let evm2 := gemJoinCtorAfterLiveState evm1
    let evm3 := gemJoinCtorAfterVatState evm2 vat
    let evm4 := gemJoinCtorAfterIlkState evm3 ilk
    let evm5 := gemJoinCtorAfterGemState evm4 gem
    let localsAfterDecimals := locals.insert "decimalsRet" (.int (Int.ofNat dec.toNat))
    let evm6 := gemJoinCtorAfterDecState evmDecimals dec
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := localsAfterDecimals } evm6) := by
  intro locals evm0 evm1 evm2 evm3 evm4 evm5 localsAfterDecimals evm6
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, gemJoinCtorAfterWardsState] using
      assign_gemJoinCtorWardsCaller evm0 (locals := locals) (by simp [locals, gemJoinCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, gemJoinCtorAfterLiveState] using
      assign_gemJoinCtorLiveStorage evm1 locals (by simp [locals, gemJoinCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3, gemJoinCtorAfterVatState] using
      assign_gemJoinCtorVatStorage evm2 locals vat (by simp [locals, gemJoinCtorLocals])
  have hassignIlk :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage ilkRef (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4, gemJoinCtorAfterIlkState] using
      assign_gemJoinCtorIlkStorage evm3 locals ilk (by simp [locals, gemJoinCtorLocals])
  have hassignGem :
      assignStorageRef? config { contract := contract, locals := locals } evm4
        .storage gemRef (.address gem) =
          .ok ({ contract := contract, locals := locals }, evm5) := by
    simpa [evm5, gemJoinCtorAfterGemState] using
      assign_gemJoinCtorGemStorage evm4 locals gem (by simp [locals, gemJoinCtorLocals])
  have hgem :
      evalExpr? config { contract := contract, locals := locals } evm5 (.var "gem_") =
        .ok (.address gem) := by
    simpa [locals] using evalExpr_gemJoinCtorLocalGem (evm := evm5) vat ilk gem
  have hgemGuard :
      evalExpr? config { contract := contract, locals := locals } evm5
        (.binary .gt (.extCodeSize (.var "gem_")) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm5] using
      evalExpr_gemJoinCtorGemCodeGuard_true evm5 vat ilk gem hgemCode
  have hdecimalArgs :
      evalExprs? config { contract := contract, locals := locals } evm5 [] = .ok [] := by
    exact evalExprs_gemJoinCtorDecimalsArgs evm5 vat ilk gem
  have hdecimalStmt :
      ExecStmt config { contract := contract, locals := locals } evm5
        (.externalCall (.var "gem_") "decimals" (.intLit 0) [] "decimalsRet" (perm := false))
        (.ok { contract := contract, locals := localsAfterDecimals } evmDecimals) := by
    simpa [localsAfterDecimals, collapseReturns] using
      ExecStmt.externalCallSuccess hgem (by simp [evalExpr?, pure]) hdecimalArgs
        hcallDecimals hdecDecimals
  have hassignDec :
      assignStorageRef? config { contract := contract, locals := localsAfterDecimals } evmDecimals
        .storage decRef (.int (Int.ofNat dec.toNat)) =
          .ok ({ contract := contract, locals := localsAfterDecimals }, evm6) := by
    simpa [localsAfterDecimals, evm6, gemJoinCtorAfterDecState] using
      assign_gemJoinCtorDecStorage evmDecimals localsAfterDecimals dec
        (by simp [localsAfterDecimals, locals, gemJoinCtorLocals])
  simp only [constructorDecl, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by rw [evalExpr?]; rfl) hassignLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalVat (evm := evm2) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignIlk) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalIlk (evm := evm3) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignGem) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalGem (evm := evm4) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  refine ExecBlock.consNormal hdecimalStmt ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (by
        simpa [localsAfterDecimals] using
          evalExpr_gemJoinCtorDecimalsRet (evm := evmDecimals) vat ilk dec gem)
      hassignDec)
    ExecBlock.nil

theorem gemJoinCtorBodyNoCodeReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))) = 0) :
    let locals := gemJoinCtorLocals vat ilk gem
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := gemJoinCtorAfterWardsState evm0
    let evm2 := gemJoinCtorAfterLiveState evm1
    let evm3 := gemJoinCtorAfterVatState evm2 vat
    let evm4 := gemJoinCtorAfterIlkState evm3 ilk
    let evm5 := gemJoinCtorAfterGemState evm4 gem
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      .reverted := by
  intro locals evm0 evm1 evm2 evm3 evm4 evm5
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, gemJoinCtorAfterWardsState] using
      assign_gemJoinCtorWardsCaller evm0 (locals := locals) (by simp [locals, gemJoinCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, gemJoinCtorAfterLiveState] using
      assign_gemJoinCtorLiveStorage evm1 locals (by simp [locals, gemJoinCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3, gemJoinCtorAfterVatState] using
      assign_gemJoinCtorVatStorage evm2 locals vat (by simp [locals, gemJoinCtorLocals])
  have hassignIlk :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage ilkRef (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4, gemJoinCtorAfterIlkState] using
      assign_gemJoinCtorIlkStorage evm3 locals ilk (by simp [locals, gemJoinCtorLocals])
  have hassignGem :
      assignStorageRef? config { contract := contract, locals := locals } evm4
        .storage gemRef (.address gem) =
          .ok ({ contract := contract, locals := locals }, evm5) := by
    simpa [evm5, gemJoinCtorAfterGemState] using
      assign_gemJoinCtorGemStorage evm4 locals gem (by simp [locals, gemJoinCtorLocals])
  have hgemGuard :
      evalExpr? config { contract := contract, locals := locals } evm5
        (.binary .gt (.extCodeSize (.var "gem_")) (.intLit 0)) = .ok (.bool false) := by
    have hno :
        ¬ 0 < UInt256.toNat (EVM.Word.ofNat
          (Option.option 0 (fun acc => acc.code.size)
            (State.lookupAccount evm5 (EVM.address gem)))) := by
      intro hpos
      have hzero :
          UInt256.toNat (EVM.Word.ofNat
            (Option.option 0 (fun acc => acc.code.size)
              (State.lookupAccount evm5 (EVM.address gem)))) = 0 := by
        simpa [evm5, evm4, evm3, evm2, evm1, evm0, gemJoinCtorAfterInitStores] using hgemCode
      omega
    simpa [locals, evm5] using
      evalExpr_gemJoinCtorGemCodeGuard_false evm5 vat ilk gem hno
  simp only [constructorDecl, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by rw [evalExpr?]; rfl) hassignLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalVat (evm := evm2) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignIlk) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalIlk (evm := evm3) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignGem) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalGem (evm := evm4) vat ilk gem
  exact ExecBlock.consRevert (ExecStmt.requireFalse hgemGuard)

theorem gemJoinCtorBodyDecimalsFailureReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    {evmDecimals : EVM.State} {outDecimals : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      0 < UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))))
    (hcallDecimals :
      typedCallViaEVM config
        (gemJoinCtorAfterInitStores
          (initState createdAccounts genesisBlockHeader blocks σ σ₀
            (Sat256.ofUInt256 g) A I)
          vat ilk gem)
        (EVM.address gem) "decimals" 0 [] (false, evmDecimals, outDecimals) false) :
    let locals := gemJoinCtorLocals vat ilk gem
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := gemJoinCtorAfterWardsState evm0
    let evm2 := gemJoinCtorAfterLiveState evm1
    let evm3 := gemJoinCtorAfterVatState evm2 vat
    let evm4 := gemJoinCtorAfterIlkState evm3 ilk
    let evm5 := gemJoinCtorAfterGemState evm4 gem
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      .reverted := by
  intro locals evm0 evm1 evm2 evm3 evm4 evm5
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, gemJoinCtorAfterWardsState] using
      assign_gemJoinCtorWardsCaller evm0 (locals := locals) (by simp [locals, gemJoinCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, gemJoinCtorAfterLiveState] using
      assign_gemJoinCtorLiveStorage evm1 locals (by simp [locals, gemJoinCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3, gemJoinCtorAfterVatState] using
      assign_gemJoinCtorVatStorage evm2 locals vat (by simp [locals, gemJoinCtorLocals])
  have hassignIlk :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage ilkRef (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4, gemJoinCtorAfterIlkState] using
      assign_gemJoinCtorIlkStorage evm3 locals ilk (by simp [locals, gemJoinCtorLocals])
  have hassignGem :
      assignStorageRef? config { contract := contract, locals := locals } evm4
        .storage gemRef (.address gem) =
          .ok ({ contract := contract, locals := locals }, evm5) := by
    simpa [evm5, gemJoinCtorAfterGemState] using
      assign_gemJoinCtorGemStorage evm4 locals gem (by simp [locals, gemJoinCtorLocals])
  have hgem :
      evalExpr? config { contract := contract, locals := locals } evm5 (.var "gem_") =
        .ok (.address gem) := by
    simpa [locals] using evalExpr_gemJoinCtorLocalGem (evm := evm5) vat ilk gem
  have hgemGuard :
      evalExpr? config { contract := contract, locals := locals } evm5
        (.binary .gt (.extCodeSize (.var "gem_")) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm5] using
      evalExpr_gemJoinCtorGemCodeGuard_true evm5 vat ilk gem hgemCode
  have hdecimalArgs :
      evalExprs? config { contract := contract, locals := locals } evm5 [] = .ok [] :=
    evalExprs_gemJoinCtorDecimalsArgs evm5 vat ilk gem
  simp only [constructorDecl, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by rw [evalExpr?]; rfl) hassignLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalVat (evm := evm2) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignIlk) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalIlk (evm := evm3) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignGem) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalGem (evm := evm4) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure hgem (by simp [evalExpr?, pure]) hdecimalArgs
      hcallDecimals)

theorem gemJoinCtorBodyDecimalsDecodeReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    {evmDecimals : EVM.State} {outDecimals : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      0 < UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))))
    (hcallDecimals :
      typedCallViaEVM config
        (gemJoinCtorAfterInitStores
          (initState createdAccounts genesisBlockHeader blocks σ σ₀
            (Sat256.ofUInt256 g) A I)
          vat ilk gem)
        (EVM.address gem) "decimals" 0 [] (true, evmDecimals, outDecimals) false)
    (hdecDecimals : config.externalABI.decode? "decimals" outDecimals = none) :
    let locals := gemJoinCtorLocals vat ilk gem
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := gemJoinCtorAfterWardsState evm0
    let evm2 := gemJoinCtorAfterLiveState evm1
    let evm3 := gemJoinCtorAfterVatState evm2 vat
    let evm4 := gemJoinCtorAfterIlkState evm3 ilk
    let evm5 := gemJoinCtorAfterGemState evm4 gem
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      .reverted := by
  intro locals evm0 evm1 evm2 evm3 evm4 evm5
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, gemJoinCtorAfterWardsState] using
      assign_gemJoinCtorWardsCaller evm0 (locals := locals) (by simp [locals, gemJoinCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, gemJoinCtorAfterLiveState] using
      assign_gemJoinCtorLiveStorage evm1 locals (by simp [locals, gemJoinCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3, gemJoinCtorAfterVatState] using
      assign_gemJoinCtorVatStorage evm2 locals vat (by simp [locals, gemJoinCtorLocals])
  have hassignIlk :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage ilkRef (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk)) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4, gemJoinCtorAfterIlkState] using
      assign_gemJoinCtorIlkStorage evm3 locals ilk (by simp [locals, gemJoinCtorLocals])
  have hassignGem :
      assignStorageRef? config { contract := contract, locals := locals } evm4
        .storage gemRef (.address gem) =
          .ok ({ contract := contract, locals := locals }, evm5) := by
    simpa [evm5, gemJoinCtorAfterGemState] using
      assign_gemJoinCtorGemStorage evm4 locals gem (by simp [locals, gemJoinCtorLocals])
  have hgem :
      evalExpr? config { contract := contract, locals := locals } evm5 (.var "gem_") =
        .ok (.address gem) := by
    simpa [locals] using evalExpr_gemJoinCtorLocalGem (evm := evm5) vat ilk gem
  have hgemGuard :
      evalExpr? config { contract := contract, locals := locals } evm5
        (.binary .gt (.extCodeSize (.var "gem_")) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm5] using
      evalExpr_gemJoinCtorGemCodeGuard_true evm5 vat ilk gem hgemCode
  have hdecimalArgs :
      evalExprs? config { contract := contract, locals := locals } evm5 [] = .ok [] :=
    evalExprs_gemJoinCtorDecimalsArgs evm5 vat ilk gem
  simp only [constructorDecl, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by rw [evalExpr?]; rfl) hassignLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalVat (evm := evm2) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignIlk) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalIlk (evm := evm3) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignGem) ?_
  · simpa [locals] using evalExpr_gemJoinCtorLocalGem (evm := evm4) vat ilk gem
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert hgem (by simp [evalExpr?, pure]) hdecimalArgs
      hcallDecimals hdecDecimals)

theorem gemJoinSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    {evmDecimals : EVM.State} {outDecimals : ByteArray} {dec : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      0 < UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))))
    (hcallDecimals :
      typedCallViaEVM config
        (gemJoinCtorAfterInitStores
          (initState createdAccounts genesisBlockHeader blocks σ σ₀
            (Sat256.ofUInt256 g) A I)
          vat ilk gem)
        (EVM.address gem) "decimals" 0 [] (true, evmDecimals, outDecimals) false)
    (hdecDecimals : config.externalABI.decode? "decimals" outDecimals =
      some [.int (Int.ofNat dec.toNat)]) :
    let locals := gemJoinCtorLocals vat ilk gem
    let localsAfterDecimals := locals.insert "decimalsRet" (.int (Int.ofNat dec.toNat))
    let evm6 := gemJoinCtorAfterDecState evmDecimals dec
    solmCtorExec config contract
      [.address vat, .fixedBytes bytes32Width (EVM.Word.toBytesBE ilk), .address gem]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract, locals := localsAfterDecimals } evm6 none) := by
  intro locals localsAfterDecimals evm6
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := locals) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact ExecFuncBody.execBlockOK
      (by
        simpa [locals, localsAfterDecimals, evm6] using
          gemJoinCtorBodySuccess
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            vat ilk gem hwv hgemCode hcallDecimals hdecDecimals)

theorem gemJoinSolmCtorExecReverts_noCode
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))) = 0) :
    solmCtorExec config contract
      [.address vat, .fixedBytes bytes32Width (EVM.Word.toBytesBE ilk), .address gem]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := gemJoinCtorLocals vat ilk gem) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact ExecFuncBody.execBlockRevert
      (by
        simpa using
          gemJoinCtorBodyNoCodeReverts
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            vat ilk gem hwv hgemCode)

theorem gemJoinSolmCtorExecReverts_decimalsFailure
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    {evmDecimals : EVM.State} {outDecimals : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      0 < UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))))
    (hcallDecimals :
      typedCallViaEVM config
        (gemJoinCtorAfterInitStores
          (initState createdAccounts genesisBlockHeader blocks σ σ₀
            (Sat256.ofUInt256 g) A I)
          vat ilk gem)
        (EVM.address gem) "decimals" 0 [] (false, evmDecimals, outDecimals) false) :
    solmCtorExec config contract
      [.address vat, .fixedBytes bytes32Width (EVM.Word.toBytesBE ilk), .address gem]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := gemJoinCtorLocals vat ilk gem) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact ExecFuncBody.execBlockRevert
      (by
        simpa using
          gemJoinCtorBodyDecimalsFailureReverts
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            vat ilk gem hwv hgemCode hcallDecimals)

theorem gemJoinSolmCtorExecReverts_decimalsDecode
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    {evmDecimals : EVM.State} {outDecimals : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hgemCode :
      0 < UInt256.toNat (EVM.Word.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          (State.lookupAccount
            (gemJoinCtorAfterInitStores
              (initState createdAccounts genesisBlockHeader blocks σ σ₀
                (Sat256.ofUInt256 g) A I)
              vat ilk gem)
            (EVM.address gem)))))
    (hcallDecimals :
      typedCallViaEVM config
        (gemJoinCtorAfterInitStores
          (initState createdAccounts genesisBlockHeader blocks σ σ₀
            (Sat256.ofUInt256 g) A I)
          vat ilk gem)
        (EVM.address gem) "decimals" 0 [] (true, evmDecimals, outDecimals) false)
    (hdecDecimals : config.externalABI.decode? "decimals" outDecimals = none) :
    solmCtorExec config contract
      [.address vat, .fixedBytes bytes32Width (EVM.Word.toBytesBE ilk), .address gem]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := gemJoinCtorLocals vat ilk gem) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact ExecFuncBody.execBlockRevert
      (by
        simpa using
          gemJoinCtorBodyDecimalsDecodeReverts
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            vat ilk gem hwv hgemCode hcallDecimals hdecDecimals)

theorem gemJoinSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract
      [.address vat, .fixedBytes bytes32Width (EVM.Word.toBytesBE ilk), .address gem]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := gemJoinCtorLocals vat ilk gem)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := gemJoinCtorLocals vat ilk gem) hwv

end Benchmarks.Dss.GemJoin
