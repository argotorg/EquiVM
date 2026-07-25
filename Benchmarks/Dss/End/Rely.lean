import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `rely(address)` -/

abbrev endRelyConcreteSelector : ByteArray := selectorBytes 0x65 0xfa 0xe3 0x5e

abbrev endRelyUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev endRelyUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (endRelyUsrWord I)

abbrev endRelyUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (endRelyUsrWord I).toNat)

abbrev endRelyUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (endRelyUsrWord I).toNat)

abbrev endRelyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev endRelyStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "usr" (endRelyUsrValue I)

def endRelyUsrStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (endRelyUsrKey I)

def endRelyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (endRelyAuthKey I)

def endRelyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endRelyAuthStorageSlot I) σ I

def endRelyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endRelyUsrStorageSlot I) ⟨1⟩

abbrev endRelyUsrEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (endRelyUsrKey I)] }

abbrev endRelyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (endRelyAuthKey I)] }

theorem endRelyStore_wards (I : ExecutionEnv) :
    (endRelyStore I).get? "wards" = none := by
  unfold endRelyStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem endRelyUsrStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    endRelyUsrStorageSlot I = mapSlot (endRelyUsrMaskedWord I) ⟨0⟩ := by
  unfold endRelyUsrStorageSlot wardsSlot endRelyUsrKey endRelyUsrMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem endRelyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    endRelyAuthStorageSlot I = mapSlot (solcSourceWord I) ⟨0⟩ := by
  unfold endRelyAuthStorageSlot wardsSlot endRelyAuthKey
  rw [keyValueToWord_address]

theorem endDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = some (endRelyStore I) := by
  simpa [config, relyTransition, endRelyStore, endRelyUsrValue, endRelyUsrWord,
    calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem endDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

theorem evalStorageRef_endRely_usr (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endRelyStore I } evm
      (wardsRef (.var "usr")) = .ok (endRelyUsrEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, endRelyStore, endRelyUsrValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_endRely_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := endRelyStore I } evm
      (wardsRef sender) = .ok (endRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, endRelyAuthEvaledRef,
    endRelyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem endUInt256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem evalExpr_endRely_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) =
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endRelyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endRelyStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endRelyStore I })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [endRelyStore, wardsRef])
      (her := evalStorageRef_endRely_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endRely_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) ≠
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endRelyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endRelyStore I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endRelyStore I })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (hbase := by simp [endRelyStore, wardsRef])
      (her := evalStorageRef_endRely_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact endUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (endRelyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem endRelyAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endRelyStore I } evm
      .storage (wardsRef (.var "usr")) (.int 1) =
        .ok ({ contract := contract, locals := endRelyStore I }, endRelyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (endRelyUsrStorageSlot I))
      (hbase := endRelyStore_wards I)
      (her := evalStorageRef_endRely_usr evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endRelyPostState] using
    endStorageLocStore_uint256 evm (endRelyUsrStorageSlot I) ⟨1⟩

theorem endRelyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) =
        ⟨1⟩) :
    ExecTransitionBody config contract evm (endRelyStore I) relyTransition.body
      (.returned { contract := contract, locals := endRelyStore I }
        (endRelyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := endRelyStore I })
      (evm := evm)
      (evm' := endRelyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 1)
      (ref := wardsRef (.var "usr"))
      (value := .int 1)
      hwv
      (evalExpr_endRely_auth_true evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (endRelyAssign evm I)

theorem endRelyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) ≠
        ⟨1⟩) :
    ExecTransitionBody config contract evm (endRelyStore I) relyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endRelyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 1)])
      hwv
      (evalExpr_endRely_auth_false evm I hsrc hauth)

noncomputable abbrev endRelyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev endRelyStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endRelyUsrMaskedWord I) ⟨0⟩ (endRelyAuthHashMem I)

theorem endRelyUsrMaskedWord_canonical (I : ExecutionEnv) :
    (endRelyUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold endRelyUsrMaskedWord
  rw [u256_land_comm solcAddrMask (endRelyUsrWord I)]
  exact solcAddrMask_result_canonical (endRelyUsrWord I)

theorem endRelyAuthHashMem_size (I : ExecutionEnv) :
    (endRelyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem endRelyAuthHashMem_read64 (I : ExecutionEnv) :
    (endRelyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem endRelyStoreHashMem_size (I : ExecutionEnv) :
    (endRelyStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (endRelyUsrMaskedWord I) ⟨0⟩ (endRelyAuthHashMem_size I)

theorem endRelyStoreHashMem_read64 (I : ExecutionEnv) :
    (endRelyStoreHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (endRelyUsrMaskedWord I) ⟨0⟩ (endRelyAuthHashMem_size I)
    (endRelyAuthHashMem_read64 I)

/-! ### Shared auth-check bytecode helper -/

@[reducible] def endAuthTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  p23 + ⟨1⟩

@[reducible] def endAuthCheckWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.CALLER, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.MSTORE, .none)
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.SWAP1, .none)
  ∧ decode code p11 = some (.MSTORE, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.KECCAK256, .none)
  ∧ decode code p16 = some (.SLOAD, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p19 = some (.EQ, .none)
  ∧ decode code p20 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p23 = some (.JUMPI, .none)

abbrev endNotAuthorizedRawWord : UInt256 :=
  ⟨0x115b990bdb9bdd0b585d5d1a1bdc9a5e9959⟩

theorem RD.endAuthCheckOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : endAuthCheckWf code pc okPc)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R)
      (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) =
          ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have rd20 := rd20₀
  rw [hauthRaw, uInt256_eq_self] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  exact ⟨_, _, rd23.jumpiT hd23 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.endAuthCheckRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : endAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (endAuthTailPc pc) ⟨18⟩
      endNotAuthorizedRawWord ⟨114⟩ .PUSH18 18)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) ≠
          ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) =
          ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hauthRaw h1.symm)
  have rd20 := rd20₀
  rw [heq0] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  have rdTail₀ := rd23.jumpiNT hd23 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [endAuthTailPc] using rdTail₀) htail
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons]; omega)

/-! ### Dispatch reachability -/

abbrev endRelyMidSplitPc : UInt256 := ⟨283⟩
abbrev endRelyGroupJumpdestPc : UInt256 := ⟨342⟩
abbrev endRelyFirstArmPc : UInt256 := ⟨343⟩
abbrev endRelyReturnPc : UInt256 := ⟨562⟩
abbrev endRelyEntryPc : UInt256 := ⟨760⟩
abbrev endRelyDecodedPc : UInt256 := ⟨782⟩
abbrev endRelyAuthPc : UInt256 := ⟨5275⟩
abbrev endRelyStorePc : UInt256 := ⟨5364⟩

theorem endRelyMidSplitWellFormed :
    selectorSplitWellFormed endBytecode endRelyMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endRelyArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endRelyFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem endReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endRelyConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endRelyEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x65fae35e⟩ :=
    endSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by native_decide) (by simpa [selIs, endRelyConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endLow1JumpdestPc] using
      RD.selectorSplitTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by native_decide) (by simp)
  have h283 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endRelyMidSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [endLow1SplitPc, endRelyMidSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272 endLow1SplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h342 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endRelyGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    simpa [endRelyMidSplitPc, endRelyGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h283 endRelyMidSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h343 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endRelyFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5 + 1)
        (C32 + 22 + 1 + 22 + 22 + 1) := by
    simpa [endRelyFirstArmPc] using h342.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endRelyFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endRelyFirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endRelyEntryPc 3 h343
    (fun j hj => endRelyArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

/-! ### Runtime trace -/

theorem endRelyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endRelyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endRelyAuthPc
        [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endRelyEntryPc) (ret := endRelyReturnPc) (decoded := endRelyDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := endBytecode) (decoded := endRelyDecodedPc) (ret := endRelyReturnPc)
    (routine := endRelyAuthPc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endRelyUsrMaskedWord, endRelyUsrWord, calldataWord] using hroutine⟩

theorem endRelyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endRelyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endRelyEntryPc) (ret := endRelyReturnPc) (decoded := endRelyDecodedPc)
    (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endRelyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endRelyAuthPc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endRelyStorePc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  simpa [endRelyAuthHashMem] using
    RD.endAuthCheckOk
      (code := endBytecode) (pc := endRelyAuthPc) (okPc := endRelyStorePc)
      (key := endRelyUsrMaskedWord I) (ret := endRelyReturnPc) (R := [sel])
      h
      (by
        unfold endAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)

theorem endRelyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endRelyAuthPc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  exact RD.endAuthCheckRevert
    (code := endBytecode) (pc := endRelyAuthPc) (okPc := endRelyStorePc)
    (key := endRelyUsrMaskedWord I) (ret := endRelyReturnPc) (R := [sel])
    h
    (by
      unfold endAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endAuthTailPc endNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)

theorem endRelyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD endBytecode I g s0 endRelyStorePc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (endRelyUsrStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((endRelyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (endRelyUsrMaskedWord I) ⟨0⟩ := by
    simpa [endRelyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (endRelyUsrMaskedWord I)
        (endRelyAuthHashMem_size I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endRelyUsrMaskedWord I)
        = endRelyUsrMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (endRelyUsrMaskedWord_canonical I)
  have hmask' :
      UInt256.land (endRelyUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = endRelyUsrMaskedWord I := by
    rw [u256_land_comm]
    exact hmask
  rw [hmask'] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdKeyMem := rdMstoreKeyPrefix.mstore 0
    (wordAt0Mem (endRelyUsrMaskedWord I) (endRelyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdKeyMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (endRelyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (mapSlot (endRelyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rdSstorePrefix := evm_run rdSlot with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdStoredRaw⟩ := rdSstorePrefix.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdStored := by
    simpa [endRelyUsrStorageSlot_eq_mapSlot_masked I] using rdStoredRaw
  have rdMload := rdStored.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [endRelyStoreHashMem_size I]; decide) (by decide)
      (endRelyStoreHashMem_read64 I))
    (by native_decide) (by evm_ov)
  have rdTopic := rdMload.pushConst
    (⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rdLogPrefix := evm_run rdTopic with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdLog := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := ⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩)
    (d := endRelyUsrMaskedWord I)
    (t := [endRelyUsrMaskedWord I, endRelyReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rdLogPrefix (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop := RD.pop (a := endRelyUsrMaskedWord I) (t := [endRelyReturnPc, sel]) rdLog
    (by native_decide) (by evm_ov)
  have rdRet := RD.jump (a := endRelyReturnPc) (t := [sel]) rdPop
    (by native_decide) (by jump_dest) (by evm_ov)
  have rdStopPc := RD.jumpdest (pc := endRelyReturnPc) (stk := [sel]) rdRet
    (by native_decide) (by evm_ov)
  have hstop := RD.stop rdStopPc (by native_decide) (by evm_ov)
  simpa [endRelyUsrStorageSlot_eq_mapSlot_masked I] using hstop

theorem endX_rely_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endRelyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (endRelyUsrStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, hdecoded⟩ := endRelyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, hokPc⟩ := endRelyX_authorized (I := I) hauth hdecoded
  exact endRelyX_storeAuthorized hperm hokPc

theorem endX_rely_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : endRelyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endRelyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := endRelyX_decoded (g := g) hsz36 hsize hreach
  exact endRelyX_unauthorized (I := I) hauth hdecoded

/-! ### Equivalence wrapper -/

theorem endRelyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : endRelyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (endRelyStore I))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endRelyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : endRelyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endRelyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (endRelyStore I)
        relyTransition.body
        (.returned { contract := contract, locals := endRelyStore I }
          (endRelyPostState evmSolm I) none) := by
    simpa [evmSolm, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endRelyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (endX_rely_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [endRelyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [endRelyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (endRelyUsrStorageSlot I) ⟨1⟩
            hAccounts)
      (by
        simpa [relyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem endRelyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : endRelyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (endRelyStore I))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endRelyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : endRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endRelyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (endRelyStore I)
        relyTransition.body .reverted := by
    simpa [evmSolm, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endRelyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (endX_rely_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem endRelyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endRelyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endRelyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_rely_none_short hsz4 hshort)

theorem endRelyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf relyTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endRelyConcreteSelector := by
    simpa [endRelySelectorBytes, endRelyConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endRelyConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    endDispatchRely hsel
  have hreach := endReachRelyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : endRelyAuthWord σ_evm I = ⟨1⟩
    · exact endRelyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (endDecode_rely_ok hsz36) hreach hAccounts
    · exact endRelyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (endDecode_rely_ok hsz36) hreach hAccounts
  · exact endRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.End
