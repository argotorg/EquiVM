import Benchmarks.Dss.Jug.FileDuty

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Jug

/-! ## `init(bytes32)` -/

abbrev initLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (.fixedBytes bytes32Width (fileDutyIlkBytes I))

abbrev initOne : UInt256 :=
  ⟨1000000000000000000000000000⟩

abbrev initTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

theorem jugDecode_init_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
      (transitionSignature initTransition).paramTypes I.calldata =
        some (initLocals I) := by
  simpa [config, initTransition, initLocals, fileDutyIlkBytes, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36)

theorem jugDecode_init_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
      (transitionSignature initTransition).paramTypes I.calldata = none := by
  simpa [config, initTransition, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk")
      hsz4 hshort)

theorem initLocals_get_ilk (I : ExecutionEnv) :
    (initLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
  rw [initLocals, store_get_self]

theorem initLocals_get_wards (I : ExecutionEnv) :
    (initLocals I).get? "wards" = none := by
  rw [initLocals, store_get_ne _ _ (by decide)]
  simp

theorem initLocals_get_ilks (I : ExecutionEnv) :
    (initLocals I).get? "ilks" = none := by
  rw [initLocals, store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_initStorageDuty (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := initLocals I } evm
      (.storage (ilksF (.var "ilk") "duty")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := initLocals I }) (evm := evm)
    (slot := ilksF (.var "ilk") "duty") (er := fileDutyDutyEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (fileDutyDutySlotFor I))
    (value := .int (Int.ofNat
      (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat))
    (initLocals_get_ilks I)
    (by
      have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
      simp [fileDutyDutyEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, initLocals_get_ilk I, EvalResult.ofOption,
        EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (fileDutyDutySlotFor I))

theorem evalExpr_initDutyEqZero_true {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := initLocals I } evm
      (.binary .eq (.storage (ilksF (.var "ilk") "duty")) (.intLit 0)) =
        .ok (.bool true) := by
  have hd := evalExpr_initStorageDuty evm I hsz36
  have hval :
      (Value.int (Int.ofNat
          (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat) ==
        Value.int 0) = true := by
    rw [hduty]
    rfl
  simp only [evalExpr?, hd, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem evalExpr_initDutyEqZero_false {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := initLocals I } evm
      (.binary .eq (.storage (ilksF (.var "ilk") "duty")) (.intLit 0)) =
        .ok (.bool false) := by
  have hd := evalExpr_initStorageDuty evm I hsz36
  have hval :
      (Value.int (Int.ofNat
          (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat) ==
        Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hduty (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  simp only [evalExpr?, hd, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem evalExpr_initTimestamp (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := initLocals evm.executionEnv } evm
      (.env .timestamp) =
        .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) := by
  simp [evalExpr?, envValue, pure]

theorem assign_initDutyStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileDutyDutySlotFor I)
      initOne
    assignStorageRef? config { contract := contract, locals := initLocals I } evm
      .storage (ilksF (.var "ilk") "duty") (.int (Int.ofNat initOne.toNat)) =
        .ok ({ contract := contract, locals := initLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := fileDutyDutyEvaledRef I)
      (loc := wordLoc (fileDutyDutySlotFor I))
      (hbase := initLocals_get_ilks I)
      (her := by
        have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
          simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
        simp [fileDutyDutyEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          ← Std.HashMap.get?_eq_getElem?, initLocals_get_ilk I, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (hty := by
        simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm'] using jugStorageLocStore_uint256 evm (fileDutyDutySlotFor I) initOne

theorem assign_initRhoStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileDutyRhoSlotFor I)
      (initTimestampWord I)
    assignStorageRef? config { contract := contract, locals := initLocals I } evm
      .storage (ilksF (.var "ilk") "rho")
        (.int (Int.ofNat (initTimestampWord I).toNat)) =
        .ok ({ contract := contract, locals := initLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := fileDutyRhoEvaledRef I)
      (loc := wordLoc (fileDutyRhoSlotFor I))
      (hbase := initLocals_get_ilks I)
      (her := by
        have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
          simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
        simp [fileDutyRhoEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          ← Std.HashMap.get?_eq_getElem?, initLocals_get_ilk I, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (hty := by
        simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm', initTimestampWord] using
    jugStorageLocStore_uint256 evm (fileDutyRhoSlotFor I) (initTimestampWord I)

theorem jugInitSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) σ I = ⟨0⟩) :
    let locals := initLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileDutyDutySlotFor I) initOne
    let evm2 := Solm.EVM.storageStore evm1 I.codeOwner (fileDutyRhoSlotFor I)
      (initTimestampWord I)
    ExecTransitionBody config contract evm0 locals initTransition.body
      (.returned { contract := contract, locals := locals } evm2 none) := by
  intro locals evm0 evm1 evm2
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using initLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hdutyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (ilksF (.var "ilk") "duty")) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_initDutyEqZero_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hduty))
  have hone :
      evalExpr? config { contract := contract, locals := locals } evm0 (.intLit one) =
        .ok (.int (Int.ofNat initOne.toNat)) := by
    have htoNat : initOne.toNat = 1000000000000000000000000000 := by
      change (UInt256.ofNat 1000000000000000000000000000).toNat =
        1000000000000000000000000000
      exact ulit_toNat' _ (by native_decide)
    simp [evalExpr?, one, initOne, pure, htoNat]
  have hassignDuty :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "duty") (.int (Int.ofNat initOne.toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_initDutyStorage evm0 I hsz36
  have htimestamp :
      evalExpr? config { contract := contract, locals := locals } evm1 (.env .timestamp) =
        .ok (.int (Int.ofNat (initTimestampWord I).toNat)) := by
    have henv : evm1.executionEnv = I := by
      simp [evm1, evm0, initState, storageStore_executionEnv]
    simp [evalExpr?, envValue, initTimestampWord, henv, pure]
  have hassignRho :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage (ilksF (.var "ilk") "rho")
          (.int (Int.ofNat (initTimestampWord I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    have howner : evm1.executionEnv.codeOwner = I.codeOwner := by
      have henv : evm1.executionEnv = I := by
        simp [evm1, evm0, initState, storageStore_executionEnv]
      simpa [henv]
    simpa [locals, evm2, howner] using assign_initRhoStorage evm1 I hsz36
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 initTransition.body
        (.ok { contract := contract, locals := locals } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hdutyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hone hassignDuty) ?_
    exact ExecBlock.consNormal (ExecStmt.assign htimestamp hassignRho) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1, evm2] using ExecFuncBody.execBlockOK hblock

theorem jugInitSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := initLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simpa [locals] using initLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [initTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.require (.binary .eq (.storage (ilksF (.var "ilk") "duty")) (.intLit 0)),
        .assign .storage (ilksF (.var "ilk") "duty") (.intLit one),
        .assign .storage (ilksF (.var "ilk") "rho") (.env .timestamp)])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem jugInitSourceBodyAlreadyInit {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) σ I ≠ ⟨0⟩) :
    let locals := initLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using initLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hdutyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (ilksF (.var "ilk") "duty")) (.intLit 0)) =
          .ok (.bool false) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_initDutyEqZero_false (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using hduty))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 initTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hdutyGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugReachInitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 7)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨299⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0x3b663195⟩ :=
    jugSelWord_eq_of_beq I hsz 0x3b 0x66 0x31 0x95 ⟨0x3b663195⟩
      (by native_decide) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc 3))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact jugReachLowBody 3 (by omega) ⟨299⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.jugInitDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨321⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = jugBytecode)
    (hroutine : (D_J code 0).contains ⟨1032⟩ = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1032⟩
      (calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd322 := h.jumpdest (by native_decide) (by evm_ov)
  have rd323 := rd322.pop (by native_decide) (by evm_ov)
  have rd324 := rd323.calldataload (by native_decide) (by evm_ov)
  have rd327 := rd324.push2 ⟨1032⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd327.jump (by native_decide) hroutine (by evm_ov)⟩

theorem jugInitX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨299⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1032⟩
        [fileDutyIlkWord I, ⟨226⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := jugBytecode) (sel := sel) (entry := ⟨299⟩) (ret := ⟨226⟩)
    (decoded := ⟨321⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.jugInitDecodeToRoutine
    (code := jugBytecode) (ret := ⟨226⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileDutyIlkWord] using hroutine⟩

set_option maxHeartbeats 1000000 in
theorem jugInitX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨1032⟩
      [fileDutyIlkWord I, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨1121⟩
      [fileDutyIlkWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1038pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1039 := rd1038pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1043pre := evm_run rd1039 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1044 := rd1043pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1047pre := evm_run rd1044 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1048 := rd1047pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1049, C1049, rd1049raw⟩ := rd1048.sload (by native_decide) (by evm_ov)
  have rd1049 : RD jugBytecode I g s0 ⟨1049⟩
      (relyAuthWord σ I :: fileDutyIlkWord I :: ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1049 C1049 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1049raw
  have rd1052pre := evm_run rd1049 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1052pre
  have rd1055 := rd1052pre.pushConst (⟨1121⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1055.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem jugInitX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨1032⟩
      [fileDutyIlkWord I, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1038pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1039 := rd1038pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1043pre := evm_run rd1039 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1044 := rd1043pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1047pre := evm_run rd1044 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1048 := rd1047pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1049, C1049, rd1049raw⟩ := rd1048.sload (by native_decide) (by evm_ov)
  have rd1049 : RD jugBytecode I g s0 ⟨1049⟩
      (relyAuthWord σ I :: fileDutyIlkWord I :: ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1049 C1049 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1049raw
  have rd1052pre := evm_run rd1049 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1052pre
  have rd1055 := rd1052pre.pushConst (⟨1121⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1056 := rd1055.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1056⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x129d59cbdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4a75672f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd1056
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugInitX_dutyZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) σ I = ⟨0⟩)
    (h : RD jugBytecode I g s0 ⟨1121⟩
      [fileDutyIlkWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨1210⟩
      [fileDutyDutySlotFor I, fileDutyIlkWord I, ⟨226⟩, sel]
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((fileDutyIlkHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    simpa [fileDutyIlkHashMem] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileDutyIlkWord I)
        (relyAuthHashMem_size I)
  have rd1122 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1124 := rd1122.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1125 := rd1124.dup2 (by native_decide) (by evm_ov)
  have rd1126pre := rd1125.dup2 (by native_decide) (by evm_ov)
  have rd1127 := rd1126pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1131pre := evm_run rd1127 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1132 := rd1131pre.mstore 0 (fileDutyIlkHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1135pre := evm_run rd1132 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1136 := rd1135pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd1137 := rd1136.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k1138, C1138, rd1138raw⟩ := rd1137.sload (by native_decide) (by evm_ov)
  have rd1138 : RD jugBytecode I g s0 ⟨1138⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ I :: solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) ::
        fileDutyIlkWord I :: ⟨226⟩ :: [sel])
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1138 C1138 := by
    simpa [jugSlotWord, fileDutyDutySlotFor_eq hsz36] using rd1138raw
  have rd1139 := rd1138.iszero (by native_decide) (by evm_ov)
  rw [hduty, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1139
  have rd1142 := rd1139.pushConst (⟨1210⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1210 := rd1142.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, by simpa [fileDutyDutySlotFor_eq hsz36] using rd1210⟩

theorem jugInitX_alreadyInit {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) σ I ≠ ⟨0⟩)
    (h : RD jugBytecode I g s0 ⟨1121⟩
      [fileDutyIlkWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((fileDutyIlkHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    simpa [fileDutyIlkHashMem] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileDutyIlkWord I)
        (relyAuthHashMem_size I)
  have rd1122 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1124 := rd1122.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1125 := rd1124.dup2 (by native_decide) (by evm_ov)
  have rd1126pre := rd1125.dup2 (by native_decide) (by evm_ov)
  have rd1127 := rd1126pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1131pre := evm_run rd1127 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1132 := rd1131pre.mstore 0 (fileDutyIlkHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1135pre := evm_run rd1132 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1136 := rd1135pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd1137 := rd1136.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k1138, C1138, rd1138raw⟩ := rd1137.sload (by native_decide) (by evm_ov)
  have rd1138 : RD jugBytecode I g s0 ⟨1138⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ I :: solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) ::
        fileDutyIlkWord I :: ⟨226⟩ :: [sel])
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1138 C1138 := by
    simpa [jugSlotWord, fileDutyDutySlotFor_eq hsz36] using rd1138raw
  have rd1139 := rd1138.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (jugSlotWord (fileDutyDutySlotFor I) σ I) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne hduty
  rw [hzero] at rd1139
  have rd1142 := rd1139.pushConst (⟨1210⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1143 := rd1142.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1143⟩)
    (len := ⟨20⟩)
    (rawWord := ⟨0x129d59cbda5b1acb585b1c9958591e4b5a5b9a5d⟩)
    (shift := ⟨98⟩)
    (word := ⟨0x4a75672f696c6b2d616c72656164792d696e6974000000000000000000000000⟩)
    (op := .PUSH20)
    (width := 20)
    rd1143
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (fileDutyIlkHashMem_size I)
    (fileDutyIlkHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugInitX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD jugBytecode I g s0 ⟨1210⟩
      [fileDutyDutySlotFor I, fileDutyIlkWord I, ⟨226⟩, sel]
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret jugBytecode g s0
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (fileDutyDutySlotFor I) initOne)
        (fileDutyRhoSlotFor I) (initTimestampWord I))
      ByteArray.empty := by
  have rd1211 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1224 := rd1211.pushConst initOne
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd1225 := rd1224.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1226⟩ := rd1225.sstore hperm (by native_decide) (by evm_ov)
  have rd1227 := RD.timestamp rd1226 (by native_decide) (by evm_ov)
  have rd1229 := rd1227.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1230 := rd1229.swap1 (by native_decide) (by evm_ov)
  have rd1231 := rd1230.swap2 (by native_decide) (by evm_ov)
  have rd1232 := rd1231.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1233⟩ := rd1232.sstore hperm (by native_decide) (by evm_ov)
  have rd1234 := rd1233.pop (by native_decide) (by evm_ov)
  have rd226 := rd1234.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd227 := rd226.jumpdest (by native_decide) (by evm_ov)
  simpa [fileDutyRhoSlotFor, initTimestampWord] using RD.stop rd227 (by native_decide) (by evm_ov)

theorem jugInitX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨299⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := jugBytecode) (sel := sel) (entry := ⟨299⟩) (ret := ⟨226⟩)
    (decoded := ⟨321⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem jugInitBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
        (transitionSignature initTransition).paramTypes I.calldata = some (initLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨299⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let dutySlot := fileDutyDutySlotFor I
  let rhoSlot := fileDutyRhoSlotFor I
  let locals := initLocals I
  let timestamp := initTimestampWord I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner dutySlot initOne
  let evm2 := Solm.EVM.storageStore evm1 I.codeOwner rhoSlot timestamp
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hdutyWord : jugSlotWord dutySlot σ_evm I = jugSlotWord dutySlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner dutySlot ⟨0⟩
  have hdutySolm : jugSlotWord dutySlot σ_solm I = ⟨0⟩ := by
    rw [← hdutyWord]
    exact hduty
  have hbody :
      ExecTransitionBody config contract evm0 locals initTransition.body
        (.returned { contract := contract, locals := locals } evm2 none) := by
    simpa [evm0, evm1, evm2, locals, dutySlot, rhoSlot, timestamp] using
      (jugInitSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hauthSolm hdutySolm)
  obtain ⟨_, _, hdecoded⟩ := jugInitX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  obtain ⟨_, _, hauthz⟩ := jugInitX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hdutyZero⟩ := jugInitX_dutyZero (I := I) hsz36 hduty hauthz
  have hret := jugInitX_storeAuthorized hperm hdutyZero
  have hAccounts1 :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm dutySlot initOne)
        (Solm.EVM.storageStore evm0 I.codeOwner dutySlot initOne).accountMap := by
    simpa [evm0, initState, storageStore_accountMap, dutySlot] using
      accountMapEquiv_sstoreAccountMap I.codeOwner dutySlot initOne hAccounts
  have hAccounts2 :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm dutySlot initOne) rhoSlot timestamp)
        evm2.accountMap := by
    simpa [evm2, evm1, evm0, initState, storageStore_accountMap, dutySlot, rhoSlot,
      timestamp] using
      accountMapEquiv_sstoreAccountMap I.codeOwner rhoSlot timestamp hAccounts1
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm2, evm1, evm0, initState, storageStore_createdAccounts])
    hAccounts2
    (by
      simpa [initTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem jugInitBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
        (transitionSignature initTransition).paramTypes I.calldata = some (initLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨299⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := initLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugInitSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := jugInitX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  exact (jugInitX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugInitBodyCoreAlreadyInit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hduty : jugSlotWord (fileDutyDutySlotFor I) σ_evm I ≠ ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
        (transitionSignature initTransition).paramTypes I.calldata = some (initLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨299⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := initLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ_evm I =
      jugSlotWord (fileDutyDutySlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyDutySlotFor I) ⟨0⟩
  have hdutySolm : jugSlotWord (fileDutyDutySlotFor I) σ_solm I ≠ ⟨0⟩ := by
    intro hbad
    exact hduty (by rw [hdutyWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugInitSourceBodyAlreadyInit (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hauthSolm hdutySolm)
  obtain ⟨_, _, hdecoded⟩ := jugInitX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  obtain ⟨_, _, hauthz⟩ := jugInitX_authorized (I := I) hauth hdecoded
  exact (jugInitX_alreadyInit (I := I) hsz36 hduty hauthz)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugInitBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨299⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (jugInitX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (jugDecode_init_none_short hsz4 hshort)

theorem jugInitBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 7) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some initTransition :=
    jugDispatchInit hsel
  have hreach := jugReachInitBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hduty : jugSlotWord (fileDutyDutySlotFor I) σ_evm I = ⟨0⟩
      · exact jugInitBodyCoreOk hcode hsize hperm hwv hsz36 hauth hduty hdispatch
          (jugDecode_init_ok hsz36) hreach hAccounts
      · exact jugInitBodyCoreAlreadyInit hcode hsize hwv hsz36 hauth hduty hdispatch
          (jugDecode_init_ok hsz36) hreach hAccounts
    · exact jugInitBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (jugDecode_init_ok hsz36) hreach hAccounts
  · exact jugInitBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Jug
