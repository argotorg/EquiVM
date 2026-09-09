import Benchmarks.Dss.Vat.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vat

/-! ## `init(bytes32)` -/

abbrev initIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev initIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev initIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev initStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (initIlkValue I)

def initRateSlot (I : ExecutionEnv) : UInt256 :=
  ilksBase (initIlkKey I) + ⟨1⟩

abbrev initRateEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (initIlkKey I), .field "rate"] }

abbrev initRayWord : UInt256 :=
  ⟨1000000000000000000000000000⟩

theorem initStore_index_ilk (I : ExecutionEnv) :
    (initStore I)["ilk"] = initIlkValue I := by
  unfold initStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem initStore_get_ilk (I : ExecutionEnv) :
    (initStore I).get? "ilk" = some (initIlkValue I) := by
  unfold initStore
  rw [store_get_self]

theorem initStore_get_wards (I : ExecutionEnv) :
    (initStore I).get? "wards" = none := by
  unfold initStore
  rw [store_get_ne _ _ (by decide)]
  simp

theorem initStore_get_ilks (I : ExecutionEnv) :
    (initStore I).get? "ilks" = none := by
  unfold initStore
  rw [store_get_ne _ _ (by decide)]
  simp

theorem initIlkBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem initIlkKeyWord_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (initIlkKey I) = initIlkWord I := by
  unfold initIlkKey initIlkWord calldataWord
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (List.take 32 (List.drop 4 I.calldata.toList)).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      uInt256OfByteArray (I.calldata.readBytes 4 32) :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [keyValueToWord, bytes32Width, ABI.bytesToWord, fromByteArrayBigEndian,
    byteArray_toList_eq, show 32 ≤ I.calldata.size - 4 by omega] at hword ⊢
  exact hword

theorem initRateSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    initRateSlot I = solcMappingSlot ⟨2⟩ (initIlkWord I) + ⟨1⟩ := by
  unfold initRateSlot ilksBase mapSlot solcMappingSlot
  rw [initIlkKeyWord_eq I hsz36]

theorem evalExpr_initStorageRate (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := initStore I } evm
      (.storage (ilksF (.var "ilk") "rate")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (initRateSlot I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := initStore I }) (evm := evm)
    (slot := ilksF (.var "ilk") "rate") (er := initRateEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (initRateSlot I))
    (value := .int (Int.ofNat
      (vatSlotWord (initRateSlot I) evm.accountMap evm.executionEnv).toNat))
    (initStore_get_ilks I)
    (by
      have hkeyLen : ((I.calldata.toList.drop 4).take 32).length =
          ↑bytes32Width + 1 := initIlkBytes_length hsz36
      simp [initRateEvaledRef, initIlkKey, initIlkValue, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [initIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by simpa [vatSlotWord] using vatStorageLocLoad_uint256 evm (initRateSlot I))

theorem evalExpr_initRateEqZero_true {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hrate : vatSlotWord (initRateSlot I) evm.accountMap evm.executionEnv = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := initStore I } evm
      (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0)) =
        .ok (.bool true) := by
  have hr := evalExpr_initStorageRate evm I hsz36
  have hval :
      (Value.int (Int.ofNat
          (vatSlotWord (initRateSlot I) evm.accountMap evm.executionEnv).toNat) ==
        Value.int 0) = true := by
    rw [hrate]
    rfl
  simp only [evalExpr?, hr, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem evalExpr_initRateEqZero_false {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hrate : vatSlotWord (initRateSlot I) evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := initStore I } evm
      (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0)) =
        .ok (.bool false) := by
  have hr := evalExpr_initStorageRate evm I hsz36
  have hval :
      (Value.int (Int.ofNat
          (vatSlotWord (initRateSlot I) evm.accountMap evm.executionEnv).toNat) ==
        Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hrate (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  simp only [evalExpr?, hr, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem assign_initRateStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (initRateSlot I)
      initRayWord
    assignStorageRef? config { contract := contract, locals := initStore I } evm
      .storage (ilksF (.var "ilk") "rate") (.int (Int.ofNat initRayWord.toNat)) =
        .ok ({ contract := contract, locals := initStore I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := initRateEvaledRef I)
      (loc := wordLoc (initRateSlot I))
      (hbase := initStore_get_ilks I)
      (her := by
        have hkeyLen : ((I.calldata.toList.drop 4).take 32).length =
            ↑bytes32Width + 1 := initIlkBytes_length hsz36
        simp [initRateEvaledRef, initIlkKey, initIlkValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (hty := by
        simp [initIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm'] using vatStorageLocStore_uint256 evm (initRateSlot I) initRayWord

theorem vatInitSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hrate : vatSlotWord (initRateSlot I) σ I = ⟨0⟩) :
    let locals := initStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (initRateSlot I) initRayWord
    ExecTransitionBody config contract evm0 locals initTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (initStore I).get? "wards" = none; exact initStore_get_wards I) hauth
  have hrateGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, vatSlotWord] using
      (evalExpr_initRateEqZero_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, vatSlotWord] using hrate))
  have hray :
      evalExpr? config { contract := contract, locals := locals } evm0 (.intLit ray) =
        .ok (.int (Int.ofNat initRayWord.toNat)) := by
    have htoNat : initRayWord.toNat = 1000000000000000000000000000 := by
      change (UInt256.ofNat 1000000000000000000000000000).toNat =
        1000000000000000000000000000
      exact ulit_toNat' _ (by decide +native)
    simp [evalExpr?, ray, initRayWord, pure, htoNat]
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "rate") (.int (Int.ofNat initRayWord.toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_initRateStorage evm0 I hsz36
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 initTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hrateGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hray hassign) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem vatInitSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := initStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
  intro locals evm0
  have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (initStore I).get? "wards" = none; exact initStore_get_wards I) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [initTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.require (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0)),
        .assign .storage (ilksF (.var "ilk") "rate") (.intLit ray)])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem vatInitSourceBodyAlreadyInit {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hrate : vatSlotWord (initRateSlot I) σ I ≠ ⟨0⟩) :
    let locals := initStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
  intro locals evm0
  have hguard := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (initStore I).get? "wards" = none; exact initStore_get_wards I) hauth
  have hrateGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0)) =
          .ok (.bool false) := by
    simpa [locals, evm0, initState, vatSlotWord] using
      (evalExpr_initRateEqZero_false (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, vatSlotWord] using hrate))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 initTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hrateGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem decodeCalldata_legacyBytes32_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [bytes32] cd =
      some ((∅ : Store).insert x (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [bytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake : List.take (↑bytes32Width + 1) ((cd.toList.drop 4).take 32) =
      (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen]; simp [bytes32Width])
  have htake32 : List.take 32 ((cd.toList.drop 4).take 32) =
      (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, bytes32,
    ABI.decodeABIValues?, ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?,
    abiTupleHeadSize?, hread, bytes32Width, htake32, hnotArgShort]

theorem decodeCalldata_legacyBytes32_none_short {cd : ByteArray} {x : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [bytes32] cd = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [bytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, bytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem vatDecode_init_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (_hsize : I.calldata.size < UInt256.size) :
    decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
      (transitionSignature initTransition).paramTypes I.calldata = some (initStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = _
  simpa [config, initStore, initIlkValue, bytes32] using
    decodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem vatDecode_init_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
      (transitionSignature initTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = none
  simpa [config, bytes32] using
    decodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "ilk") hsz4 hshort

theorem vatDispatchInit {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 17)) :
    dispatchMsg contract I.calldata = some initTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 17 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some initTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes, initSelectorBytes]
  decide +native

theorem vatReachInitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 17)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨682⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x3b663195⟩ :=
    vatSelWord_eq_of_beq I hsz 0x3b 0x66 0x31 0x95 ⟨0x3b663195⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc 3))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms370Body 3 (by omega) ⟨682⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by decide +native)

@[reducible] def solcOneWordExternalLoadAndJumpWf
    (code : ByteArray) (pc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p6 := p3 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.CALLDATALOAD, .none)
  ∧ decode code p3 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p6 = some (.JUMP, .none)

theorem RD.solcOneWordExternalLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hwf : solcOneWordExternalLoadAndJumpWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd6⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.calldataload hd2 (by evm_ov)
  have rd6 := rd3.push2 routine hd3 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd6.jump hd6 hroutine (by evm_ov)⟩

theorem vatInitX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨682⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2231⟩
        [initIlkWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨682⟩) (ret := ⟨524⟩)
    (decoded := ⟨704⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨704⟩) (ret := ⟨524⟩) (routine := ⟨2231⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcOneWordExternalLoadAndJumpWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [initIlkWord] using hroutine⟩

@[reducible] def vatInitRateGuardTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  p23 + ⟨1⟩

@[reducible] def vatInitRateGuardWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.DUP2, .none)
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.MSTORE, .none)
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p17 = some (.ADD, .none)
  ∧ decode code p18 = some (.SLOAD, .none)
  ∧ decode code p19 = some (.ISZERO, .none)
  ∧ decode code p20 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p23 = some (.JUMPI, .none)

abbrev vatIlkAlreadyInitRawWord : UInt256 :=
  ⟨123286624933419720108220527846135141904676526685⟩

theorem RD.vatInitRateGuardOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatInitRateGuardWf code pc okPc)
    (hrate : solcSlotWord σ ee (solcMappingSlot ⟨2⟩ key + ⟨1⟩) = ⟨0⟩)
    (hmem : mem.size = 96)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R)
      (twoWordHashMem key ⟨2⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd8, hd10, hd11, hd13, hd14, hd15, hd17,
      hd18, hd19, hd20, hd23⟩
  have rd4 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨0⟩ hd1 (by evm_ov)
    |>.dup2 hd3 (by evm_ov) |>.dup2 hd4 (by evm_ov)
  have rd5 := rd4.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd10pre := evm_run rd5 with [
    raw push1 ⟨2⟩ hd6 (by evm_ov),
    raw push1 ⟨32⟩ hd8 (by evm_ov)]
  have rd10 := rd10pre.mstore 0 (twoWordHashMem key ⟨2⟩ mem)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd14pre := evm_run rd10 with [
    raw push1 ⟨64⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨2⟩ key hmem
  have rd15 := rd14pre.keccak256 0 (solcMappingSlot ⟨2⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost hslot (by decide +native) (by evm_ov)
  have rd17 := rd15.push1 ⟨1⟩ hd15 (by evm_ov)
  have rd18 := rd17.add hd17 (by evm_ov)
  obtain ⟨_, _, rd19raw⟩ := rd18.sload hd18 (by evm_ov)
  have hrateRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + solcMappingSlot ⟨2⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord, u256_add_comm (⟨1⟩ : UInt256) (solcMappingSlot ⟨2⟩ key)]
      using hrate
  have rd19 := rd19raw
  rw [hrateRaw] at rd19
  have rd20₀ := rd19.iszero hd19 (by evm_ov)
  have rd20 := rd20₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  exact ⟨_, _, rd23.jumpiT hd23 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.vatInitRateGuardRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatInitRateGuardWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (vatInitRateGuardTailPc pc) ⟨20⟩
      vatIlkAlreadyInitRawWord ⟨98⟩ .PUSH20 20)
    (hrate : solcSlotWord σ ee (solcMappingSlot ⟨2⟩ key + ⟨1⟩) ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd8, hd10, hd11, hd13, hd14, hd15, hd17,
      hd18, hd19, hd20, hd23⟩
  have rd4 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨0⟩ hd1 (by evm_ov)
    |>.dup2 hd3 (by evm_ov) |>.dup2 hd4 (by evm_ov)
  have rd5 := rd4.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd10pre := evm_run rd5 with [
    raw push1 ⟨2⟩ hd6 (by evm_ov),
    raw push1 ⟨32⟩ hd8 (by evm_ov)]
  have rd10 := rd10pre.mstore 0 (twoWordHashMem key ⟨2⟩ mem)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd14pre := evm_run rd10 with [
    raw push1 ⟨64⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨2⟩ key hmem
  have rd15 := rd14pre.keccak256 0 (solcMappingSlot ⟨2⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost hslot (by decide +native) (by evm_ov)
  have rd17 := rd15.push1 ⟨1⟩ hd15 (by evm_ov)
  have rd18 := rd17.add hd17 (by evm_ov)
  obtain ⟨_, _, rd19raw⟩ := rd18.sload hd18 (by evm_ov)
  have hrateRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (⟨1⟩ + solcMappingSlot ⟨2⟩ key) ⟨0⟩)) ≠ ⟨0⟩ := by
    simpa [solcSlotWord, u256_add_comm (⟨1⟩ : UInt256) (solcMappingSlot ⟨2⟩ key)]
      using hrate
  have rd20₀ := rd19raw.iszero hd19 (by evm_ov)
  have hiszero :
      UInt256.isZero
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (⟨1⟩ + solcMappingSlot ⟨2⟩ key) ⟨0⟩)) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hrateRaw
  have rd20 := rd20₀
  rw [hiszero] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  have rdTail₀ := rd23.jumpiNT hd23 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have hhashMem : (twoWordHashMem key ⟨2⟩ mem).size = 96 :=
    twoWordHashMem_size_96 key ⟨2⟩ hmem
  have hhashRead64 :
      (twoWordHashMem key ⟨2⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨2⟩ hmem hread64
  exact RD.solcErrorStringRevertTail
    (word := UInt256.shiftLeft vatIlkAlreadyInitRawWord ⟨98⟩)
    (by simpa [vatInitRateGuardTailPc] using rdTail₀)
    htail (by decide) rfl hhashMem hhashRead64
    (by simpa only [List.length_cons] using hov)

@[reducible] def vatInitStoreRayWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p28 := p15 + UInt256.ofNat 13
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.SWAP1, .none)
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.MSTORE, .none)
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.Push .PUSH12, some (initRayWord, 12))
  ∧ decode code p28 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p30 = some (.SWAP1, .none)
  ∧ decode code p31 = some (.SWAP2, .none)
  ∧ decode code p32 = some (.ADD, .none)
  ∧ decode code p33 = some (.SSTORE, .none)
  ∧ decode code p34 = some (.JUMP, .none)

theorem RD.vatInitStoreRay {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatInitStoreRayWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨2⟩ key + ⟨1⟩) initRayWord)
      k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd8, hd10, hd11, hd13, hd14, hd15, hd28,
      hd30, hd31, hd32, hd33, hd34⟩
  have rd4 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨0⟩ hd1 (by evm_ov)
    |>.swap1 hd3 (by evm_ov) |>.dup2 hd4 (by evm_ov)
  have rd5 := rd4.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd10pre := evm_run rd5 with [
    raw push1 ⟨2⟩ hd6 (by evm_ov),
    raw push1 ⟨32⟩ hd8 (by evm_ov)]
  have rd10 := rd10pre.mstore 0 (twoWordHashMem key ⟨2⟩ mem)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd14pre := evm_run rd10 with [
    raw push1 ⟨64⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨2⟩ key hmem
  have rd15 := rd14pre.keccak256 0 (solcMappingSlot ⟨2⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost hslot (by decide +native) (by evm_ov)
  have rd28 := rd15.pushConst initRayWord
    (width := 12) (op := .PUSH12) (by decide) hd15 (by evm_ov)
  have rd33 := evm_run rd28 with [
    raw push1 ⟨1⟩ hd28 (by evm_ov),
    raw swap1 hd30 (by evm_ov),
    raw swap2 hd31 (by evm_ov),
    raw add hd32 (by evm_ov)]
  obtain ⟨_, _, rd34⟩ := rd33.sstore hperm hd33 (by evm_ov)
  exact ⟨_, _, rd34.jump hd34 hret (by evm_ov)⟩

theorem vatInitX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨682⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨682⟩) (ret := ⟨524⟩)
    (decoded := ⟨704⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem vatInitBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hrate : vatSlotWord (initRateSlot I) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
        (transitionSignature initTransition).paramTypes I.calldata = some (initStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨682⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let slot := initRateSlot I
  let locals := initStore I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner slot initRayWord
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauth
  have hrateWord : vatSlotWord slot σ_evm I = vatSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hrateSolm : vatSlotWord slot σ_solm I = ⟨0⟩ := by
    rw [← hrateWord]
    exact hrate
  have hbody :
      ExecTransitionBody config contract evm0 locals initTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, slot] using
      (vatInitSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hauthSolm hrateSolm)
  obtain ⟨_, _, hdecoded⟩ := vatInitX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨2231⟩) (okPc := ⟨2313⟩)
    (key := initIlkWord I) (ret := ⟨524⟩) (R := [sel])
    hdecoded
    (by
      unfold vatAuthCheckWf
      repeat' first | apply And.intro | decide +native)
    hauthSolc (by jump_dest) (by simp)
  have hrateSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨2⟩ (initIlkWord I) + ⟨1⟩) = ⟨0⟩ := by
    simpa [vatSlotWord, initRateSlot_eq I hsz36] using hrate
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hstorePc⟩ := RD.vatInitRateGuardOk
    (code := vatBytecode) (pc := ⟨2313⟩) (okPc := ⟨2404⟩)
    (key := initIlkWord I) (ret := ⟨524⟩) (R := [sel])
    hafterAuth
    (by
      unfold vatInitRateGuardWf
      repeat' first | apply And.intro | decide +native)
    hrateSolc hmemAuth (by jump_dest) (by simp)
  have hrateMem :
      (twoWordHashMem (initIlkWord I) ⟨2⟩
        (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 96 :=
    twoWordHashMem_size_96 (initIlkWord I) ⟨2⟩ hmemAuth
  obtain ⟨_, _, hretPc⟩ := RD.vatInitStoreRay
    (code := vatBytecode) (pc := ⟨2404⟩)
    (key := initIlkWord I) (ret := ⟨524⟩) (R := [sel])
    hstorePc
    (by
      unfold vatInitStoreRayWf initRayWord
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) hperm hrateMem (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm slot initRayWord) ByteArray.empty := by
    simpa [slot, initRateSlot_eq I hsz36] using
      RD.stop hretPc' (by decide +native) (by simp)
  have haccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm slot initRayWord)
        evm1.accountMap := by
    simpa [evm1, evm0, initState, storageStore_accountMap, slot] using
      accountMapEquiv_sstoreAccountMap I.codeOwner slot initRayWord hAccounts
  have henc : returnEquiv ByteArray.empty none initTransition.returnType := by
    rw [show initTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    haccounts henc

theorem vatInitBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
        (transitionSignature initTransition).paramTypes I.calldata = some (initStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨682⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := initStore I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I ≠ ⟨1⟩ := by
    intro hbad
    exact hauth (by rw [hcallerWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatInitSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := vatInitX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  have hrev := RD.vatAuthCheckRevert
    (pc := ⟨2231⟩) (okPc := ⟨2313⟩)
    (key := initIlkWord I) (ret := ⟨524⟩) (R := [sel])
    hdecoded
    (by
      unfold vatAuthCheckWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold vatAuthRevertTailWf vatAuthTailPc
      repeat' first | apply And.intro | decide +native)
    hauthSolc (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatInitBodyCoreAlreadyInit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hrate : vatSlotWord (initRateSlot I) σ_evm I ≠ ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (initTransition.params.map Param.name)
        (transitionSignature initTransition).paramTypes I.calldata = some (initStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨682⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := initStore I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauth
  have hrateWord : vatSlotWord (initRateSlot I) σ_evm I =
      vatSlotWord (initRateSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (initRateSlot I) ⟨0⟩
  have hrateSolm : vatSlotWord (initRateSlot I) σ_solm I ≠ ⟨0⟩ := by
    intro hbad
    exact hrate (by rw [hrateWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals initTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatInitSourceBodyAlreadyInit (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hauthSolm hrateSolm)
  obtain ⟨_, _, hdecoded⟩ := vatInitX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨2231⟩) (okPc := ⟨2313⟩)
    (key := initIlkWord I) (ret := ⟨524⟩) (R := [sel])
    hdecoded
    (by
      unfold vatAuthCheckWf
      repeat' first | apply And.intro | decide +native)
    hauthSolc (by jump_dest) (by simp)
  have hrateSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨2⟩ (initIlkWord I) + ⟨1⟩) ≠ ⟨0⟩ := by
    simpa [vatSlotWord, initRateSlot_eq I hsz36] using hrate
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hreadAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have hrev := RD.vatInitRateGuardRevert
    (code := vatBytecode) (pc := ⟨2313⟩) (okPc := ⟨2404⟩)
    (key := initIlkWord I) (ret := ⟨524⟩) (R := [sel])
    hafterAuth
    (by
      unfold vatInitRateGuardWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcErrorStringRevertTailWf vatInitRateGuardTailPc vatIlkAlreadyInitRawWord
      repeat' first | apply And.intro | decide +native)
    hrateSolc hmemAuth hreadAuth (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatInitBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some initTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨682⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatInitX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (vatDecode_init_none_short hsz4 hshort)

theorem vatInitBodyCore : VatBodyTheorem 17 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 17) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some initTransition :=
    vatDispatchInit hsel
  have hreach := vatReachInitBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩
    · by_cases hrate : vatSlotWord (initRateSlot I) σ_evm I = ⟨0⟩
      · exact vatInitBodyCoreOk hcode hsize hperm hwv hsz36 hauth hrate hdispatch
          (vatDecode_init_ok hsz36 hsize) hreach hAccounts
      · exact vatInitBodyCoreAlreadyInit hcode hsize hwv hsz36 hauth hrate hdispatch
          (vatDecode_init_ok hsz36 hsize) hreach hAccounts
    · exact vatInitBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (vatDecode_init_ok hsz36 hsize) hreach hAccounts
  · exact vatInitBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
