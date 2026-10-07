import Benchmarks.Dss.Jug.Rely
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Jug

/-! ## `file(bytes32,uint256)` -/

abbrev fileBaseWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileBaseData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileBaseBytes : List UInt8 :=
  [98, 97, 115, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileBaseLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileBaseWhat I))).insert
    "data" (.int (Int.ofNat (fileBaseData I).toNat))

theorem fileBaseWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileBaseWhat I).length = 32 := by
  simp [fileBaseWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileBaseWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileBaseWhat I) = calldataWord I.calldata 4 := by
  simpa [fileBaseWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileBaseWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileBaseWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileBaseWhatWord_eq (I := I) hsz36).symm

theorem fileBaseWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileBaseWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileBaseWhat I)
    (fileBaseWhat_length (I := I) hsz36)
  rw [fileBaseWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileBaseWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileBaseWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileBaseWhat_eq_of_word_eq hsz36 hword hbsLen)


theorem jugDecode_fileBase_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileBaseTransition.params.map Param.name)
      (transitionSignature fileBaseTransition).paramTypes I.calldata =
        some (fileBaseLocals I) := by
  simpa [config, fileBaseTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileBaseLocals, fileBaseWhat, fileBaseData, abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem jugDecode_fileBase_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileBaseTransition.params.map Param.name)
      (transitionSignature fileBaseTransition).paramTypes I.calldata = none := by
  simpa [config, fileBaseTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem fileBaseLocals_get_what (I : ExecutionEnv) :
    (fileBaseLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileBaseWhat I)) := by
  rw [fileBaseLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileBaseLocals_get_data (I : ExecutionEnv) :
    (fileBaseLocals I).get? "data" =
      some (.int (Int.ofNat (fileBaseData I).toNat)) := by
  rw [fileBaseLocals, store_get_self]

theorem fileBaseLocals_get_wards (I : ExecutionEnv) :
    (fileBaseLocals I).get? "wards" = none := by
  rw [fileBaseLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileBaseLocals_get_base (I : ExecutionEnv) :
    (fileBaseLocals I).get? "base" = none := by
  rw [fileBaseLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileBaseData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileBaseData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileBaseData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileBaseData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileBaseWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileBaseWhat I)))
    (hwhat : fileBaseWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileBaseWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileBaseWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileBaseWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileBaseWhat I)))
    (hwhat : fileBaseWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileBaseWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileBaseWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileBaseStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ (fileBaseData I)
    assignStorageRef? config { contract := contract, locals := fileBaseLocals I } evm
      .storage baseRef (.int (Int.ofNat (fileBaseData I).toNat)) =
        .ok ({ contract := contract, locals := fileBaseLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar (hbackend := rfl)
      (ty := uint256St)
      (er := ({ base := "base", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨4⟩) (hleaf := by first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
      (hbase := fileBaseLocals_get_base I)
      (her := by simp [baseRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [evm'] using storageLocStore_uint256 evm ⟨4⟩ (fileBaseData I)

theorem jugFileBaseSourceBodySplit {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileBaseWhat I = fileBaseBytes) :
    let locals := fileBaseLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩ (fileBaseData I)
    ExecTransitionBody config contract evm0 locals fileBaseTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) ∧
    (I.perm = false →
      ExecTransitionBody config contract evm0 locals fileBaseTransition.body .staticViolation) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileBaseLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") baseParamLit) = .ok (.bool true) := by
    simpa [baseParamLit, fileBaseBytes] using
      (evalExpr_fileBaseWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileBaseBytes) (by simpa [locals] using fileBaseLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileBaseData I).toNat)) := by
    exact evalExpr_fileBaseData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileBaseLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage baseRef (.int (Int.ofNat (fileBaseData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileBaseStorage evm0 I
  have hbody : ∀ r, ExecStmt config { contract := contract, locals := locals } evm0
      (.assign .storage baseRef (.var "data")) r →
      ExecBlock config { contract := contract, locals := locals } evm0
        fileBaseTransition.body r := by
    intro r h
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact execBlock_singleton (ExecStmt.iteTrue hcond
      (execBlock_singleton h))
  refine ⟨?_, fun hpf => ?_⟩
  · simpa [ExecTransitionBody, locals, evm0, evm1] using
      ExecFuncBody.execBlockOK (hbody _ (ExecStmt.assign hdata hassign))
  · simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockStatic
      (hbody _ (ExecStmt.assignStatic hdata hassign (by simp [evm0, initState]; exact hpf)))

theorem jugFileBaseSourceBody {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileBaseWhat I = fileBaseBytes) :
    let locals := fileBaseLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩ (fileBaseData I)
    ExecTransitionBody config contract evm0 locals fileBaseTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) :=
  (jugFileBaseSourceBodySplit (σ₀ := σ₀) (A := A) (g := g) hwv hauth hwhat).1

theorem jugFileBaseSourceBodyStatic {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileBaseWhat I = fileBaseBytes)
    (hperm : I.perm = false) :
    let locals := fileBaseLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileBaseTransition.body
      .staticViolation :=
  (jugFileBaseSourceBodySplit (σ₀ := σ₀) (A := A) (g := g) hwv hauth hwhat).2 hperm

theorem jugFileBaseSourceBodyAuthReverts {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileBaseLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileBaseTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simpa [locals] using fileBaseLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileBaseTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.ite (.binary .eq (.var "what") baseParamLit)
        [.assign .storage baseRef (.var "data")] [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem jugFileBaseSourceBodyUnrecognized {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileBaseWhat I ≠ fileBaseBytes) :
    let locals := fileBaseLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileBaseTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileBaseLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") baseParamLit) = .ok (.bool false) := by
    simpa [baseParamLit, fileBaseBytes] using
      (evalExpr_fileBaseWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileBaseBytes) (by simpa [locals] using fileBaseLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileBaseTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugReachFileBaseBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 3)) :
    ∃ k C, RD jugBytecode I g (initState σ σ₀ g A I)
        ⟨228⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : jugSelWord I = ⟨0x29ae8114⟩ :=
    jugSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc 1))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact jugReachLowBody 1 (by omega) ⟨228⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.jugFileBaseDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 ⟨250⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = jugBytecode)
    (hroutine : (D_J code 0).contains ⟨903⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨903⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd251 := h.jumpdest (by native_decide) (by evm_ov)
  have rd252 := rd251.pop (by native_decide) (by evm_ov)
  have rd253 := rd252.dup1 (by native_decide) (by evm_ov)
  have rd254 := rd253.calldataload (by native_decide) (by evm_ov)
  have rd255 := rd254.swap1 (by native_decide) (by evm_ov)
  have rd257 := rd255.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd258 := rd257.add (by native_decide) (by evm_ov)
  have rd259 := rd258.calldataload (by native_decide) (by evm_ov)
  have rd262 := rd259.push2 ⟨903⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd262.jump (by native_decide) hroutine (by evm_ov)⟩

theorem jugFileBaseX_decoded {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState σ σ₀ g A I) ⟨228⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD jugBytecode I g (initState σ σ₀ g A I) ⟨903⟩
        [fileBaseData I, calldataWord I.calldata 4, ⟨226⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := jugBytecode) (sel := sel) (entry := ⟨228⟩) (ret := ⟨226⟩)
    (decoded := ⟨250⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.jugFileBaseDecodeToRoutine
    (code := jugBytecode) (ret := ⟨226⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileBaseData] using hroutine⟩

set_option maxHeartbeats 1000000 in
theorem jugFileBaseX_authorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨903⟩
      [fileBaseData I, calldataWord I.calldata 4, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨992⟩
      [fileBaseData I, calldataWord I.calldata 4, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd909pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd910 := rd909pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd914pre := evm_run rd910 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd915 := rd914pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd918pre := evm_run rd915 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd919 := rd918pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k920, C920, rd920raw⟩ := rd919.sload (by native_decide) (by evm_ov)
  have rd920 : RD jugBytecode I g s0 ⟨920⟩
      (relyAuthWord σ I :: fileBaseData I :: calldataWord I.calldata 4 :: ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k920 C920 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd920raw
  have rd923pre := evm_run rd920 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd923pre
  have rd926 := rd923pre.pushConst (⟨992⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd926.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem jugFileBaseX_unauthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨903⟩
      [fileBaseData I, calldataWord I.calldata 4, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev jugBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd909pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd910 := rd909pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd914pre := evm_run rd910 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd915 := rd914pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd918pre := evm_run rd915 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd919 := rd918pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k920, C920, rd920raw⟩ := rd919.sload (by native_decide) (by evm_ov)
  have rd920 : RD jugBytecode I g s0 ⟨920⟩
      (relyAuthWord σ I :: fileBaseData I :: calldataWord I.calldata 4 :: ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k920 C920 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd920raw
  have rd923pre := evm_run rd920 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd923pre
  have rd926 := rd923pre.pushConst (⟨992⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd927 := rd926.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨927⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x129d59cbdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4a75672f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd927
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

abbrev jugFileUnrecognizedRawWord : UInt256 :=
  ⟨0x4a75672f66696c652d756e7265636f676e697a65642d706172616d0000000000⟩

theorem RD.jugFileUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD jugBytecode ee g s0 ⟨821⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev jugBytecode g s0 := by
  have rdMload := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst jugFileUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ jugFileUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ jugFileUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem jugFileBaseX_storeAuthorizedSplit {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileBaseBytes)
    (h : RD jugBytecode I g s0 ⟨992⟩
      [fileBaseData I, calldataWord I.calldata 4, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
    RDret jugBytecode g s0
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ (fileBaseData I))
      ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic jugBytecode g s0) := by
  have rd993 := h.jumpdest (by native_decide) (by evm_ov)
  have rd994 := rd993.dup2 (by native_decide) (by evm_ov)
  have rd999 := rd994.pushConst (⟨0x62617365⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1001 := rd999.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd1002 := rd1001.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x62617365⟩ : UInt256) ⟨224⟩ =
      ABI.bytesToWord fileBaseBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd1002
  have rd1003 := rd1002.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd1003
  have rd1004 := rd1003.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1004
  have rd1007 := rd1004.pushConst (⟨821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1008 := rd1007.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1010 := rd1008.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd1011 := rd1010.dup2 (by native_decide) (by evm_ov)
  have rd1012 := rd1011.swap1 (by native_decide) (by evm_ov)
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd1012.sstoreStatic (by simpa using hperm) (by native_decide) (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd1013raw⟩ := rd1012.sstore hperm (by native_decide) (by evm_ov)
  have rd1014 := rd1013raw.jumpdest (by native_decide) (by evm_ov)
  have rd1015 := rd1014.pop (by native_decide) (by evm_ov)
  have rd1016 := rd1015.pop (by native_decide) (by evm_ov)
  have rd226 := rd1016.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd227 := rd226.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd227 (by native_decide) (by evm_ov)

theorem jugFileBaseX_storeAuthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileBaseBytes)
    (h : RD jugBytecode I g s0 ⟨992⟩
      [fileBaseData I, calldataWord I.calldata 4, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret jugBytecode g s0
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ (fileBaseData I))
      ByteArray.empty :=
  permSplit_true hperm (jugFileBaseX_storeAuthorizedSplit hmatch h)

theorem jugFileBaseX_unrecognized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBaseBytes)
    (h : RD jugBytecode I g s0 ⟨992⟩
      [fileBaseData I, calldataWord I.calldata 4, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev jugBytecode g s0 := by
  have rd993 := h.jumpdest (by native_decide) (by evm_ov)
  have rd994 := rd993.dup2 (by native_decide) (by evm_ov)
  have rd999 := rd994.pushConst (⟨0x62617365⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1001 := rd999.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd1002 := rd1001.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x62617365⟩ : UInt256) ⟨224⟩ =
      ABI.bytesToWord fileBaseBytes := by
    native_decide
  rw [hconst] at rd1002
  have rd1003 := rd1002.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileBaseBytes) (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd1003
  have rd1004 := rd1003.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1004
  have rd1007 := rd1004.pushConst (⟨821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd821 := rd1007.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.jugFileUnrecognizedRevert rd821
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugFileBaseX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState σ σ₀ g A I) ⟨228⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev jugBytecode g (initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := jugBytecode) (sel := sel) (entry := ⟨228⟩) (ret := ⟨226⟩)
    (decoded := ⟨250⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem jugFileBaseBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileBaseWhat I = fileBaseBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileBaseTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileBaseTransition.params.map Param.name)
        (transitionSignature fileBaseTransition).paramTypes I.calldata = some (fileBaseLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨228⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let data := fileBaseData I
  let locals := fileBaseLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩ data
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileBaseTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, data] using
      (jugFileBaseSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := jugFileBaseX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := jugFileBaseX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileBaseBytes :=
    fileBaseWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := jugFileBaseX_storeAuthorized hperm hmatch hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_accountMap, data])
    (by
      simpa [fileBaseTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem jugFileBaseBodyCoreStatic
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = false) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileBaseWhat I = fileBaseBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileBaseTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileBaseTransition.params.map Param.name)
        (transitionSignature fileBaseTransition).paramTypes I.calldata = some (fileBaseLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨228⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨_, _, hdecoded⟩ := jugFileBaseX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := jugFileBaseX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileBaseBytes :=
    fileBaseWhatWord_eq_of_bytes_eq (by omega) hwhat
  exact (permSplit_false hperm (jugFileBaseX_storeAuthorizedSplit hmatch hswitch))
    |>.reEquivStaticHalt hcode hdispatch hdecode
      (jugFileBaseSourceBodyStatic (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hauth hwhat hperm)

theorem jugFileBaseBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileBaseTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileBaseTransition.params.map Param.name)
        (transitionSignature fileBaseTransition).paramTypes I.calldata = some (fileBaseLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨228⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let locals := fileBaseLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ I ≠ ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileBaseTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugFileBaseSourceBodyAuthReverts (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := jugFileBaseX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  exact (jugFileBaseX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugFileBaseBodyCoreUnrecognized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileBaseWhat I ≠ fileBaseBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileBaseTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileBaseTransition.params.map Param.name)
        (transitionSignature fileBaseTransition).paramTypes I.calldata = some (fileBaseLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨228⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let locals := fileBaseLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileBaseTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugFileBaseSourceBodyUnrecognized (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := jugFileBaseX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := jugFileBaseX_authorized (I := I) hauth hdecoded
  have hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBaseBytes :=
    fileBaseWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (jugFileBaseX_unrecognized hneq hswitch)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugFileBaseBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileBaseTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨228⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact (jugFileBaseX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (jugDecode_fileBase_none_short hsz4 hshort)

theorem jugFileBaseBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileBaseTransition :=
    jugDispatchFileBase hsel
  have hreach := jugReachFileBaseBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · by_cases hwhat : fileBaseWhat I = fileBaseBytes
      · exact jugFileBaseBodyCoreOk hcode hsize hperm hwv hsz68 hauth hwhat hdispatch
          (jugDecode_fileBase_ok hsz68) hreach
      · exact jugFileBaseBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hwhat hdispatch
          (jugDecode_fileBase_ok hsz68) hreach
    · exact jugFileBaseBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (jugDecode_fileBase_ok hsz68) hreach
  · exact jugFileBaseBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

/-- `file(bytes32,uint256)` (`base`) with any call permission; a static call halts at the `base`
    `SSTORE`. -/
theorem jugFileBaseBodyAnyPerm {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  by_cases hperm : I.perm = true
  · exact jugFileBaseBody hcode hsize hperm hwv hsel
  replace hperm : I.perm = false := by simpa using hperm
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileBaseTransition :=
    jugDispatchFileBase hsel
  have hreach := jugReachFileBaseBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · by_cases hwhat : fileBaseWhat I = fileBaseBytes
      · exact jugFileBaseBodyCoreStatic hcode hsize hperm hwv hsz68 hauth hwhat hdispatch
          (jugDecode_fileBase_ok hsz68) hreach
      · exact jugFileBaseBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hwhat hdispatch
          (jugDecode_fileBase_ok hsz68) hreach
    · exact jugFileBaseBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (jugDecode_fileBase_ok hsz68) hreach
  · exact jugFileBaseBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Jug
