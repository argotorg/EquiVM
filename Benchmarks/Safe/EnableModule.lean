import Benchmarks.Safe.Routines

/-! # Safe `enableModule(address)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Benchmarks.Safe

abbrev safeEnableModuleWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeEnableModuleValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeEnableModuleWord I).toNat)

abbrev safeEnableModuleLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "module" (safeEnableModuleValue I)

abbrev safeEnableModuleKeyValue (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (safeEnableModuleWord I).toNat)

abbrev safeEnableModuleEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "modules", steps := [.mindex (safeEnableModuleKeyValue I)] }

abbrev safeEnableModuleSlotFor (I : ExecutionEnv) : UInt256 :=
  modulesSlot (safeEnableModuleKeyValue I)

abbrev safeEnableModuleSentinelKeyValue : KeyValue :=
  .address (AccountAddress.ofNat 1)

abbrev safeEnableModuleSentinelEvaledRef : EvaledStorageRef :=
  { base := "_modulesSentinel" }

abbrev safeEnableModuleSentinelSlot : UInt256 :=
  modulesSentinelSlot

def safeEnableModuleStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeEnableModuleSlotFor I)

abbrev safeEnableModuleMaskedStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (safeEnableModuleStorageWord σ I) solcAddrMask

def safeEnableModuleSentinelStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I safeEnableModuleSentinelSlot

abbrev safeEnableModuleMaskedSentinelWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (safeEnableModuleSentinelStorageWord σ I) solcAddrMask

def safeEnableModuleSentinelValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeEnableModuleMaskedSentinelWord σ I).toNat)

def safeEnableModuleTargetStoreWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word (safeEnableModuleStorageWord σ I)
    (safeEnableModuleMaskedSentinelWord σ I)

def safeEnableModuleTargetPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (safeEnableModuleSlotFor I)
    (safeEnableModuleTargetStoreWord σ I)

def safeEnableModuleSentinelStoreWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (solcSlotWord (safeEnableModuleTargetPostMap σ I) I safeEnableModuleSentinelSlot)
    (safeEnableModuleWord I)

def safeEnableModulePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (safeEnableModuleTargetPostMap σ I)
    safeEnableModuleSentinelSlot (safeEnableModuleSentinelStoreWord σ I)

def safeEnableModuleTargetPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (safeEnableModuleSlotFor I)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (safeEnableModuleSlotFor I))
      (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner safeEnableModuleSentinelSlot)
        solcAddrMask))

def safeEnableModuleSentinelPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner safeEnableModuleSentinelSlot
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner safeEnableModuleSentinelSlot)
      (safeEnableModuleWord I))

def safeEnableModulePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  safeEnableModuleSentinelPostState (safeEnableModuleTargetPostState evm I) I

def safeEnableModuleEnabledTopic : UInt256 :=
  ⟨107140241160852291599652060716272525823670339549878733384263921823022862795840⟩

noncomputable def safeEnableModuleCheckMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem

noncomputable def safeEnableModuleBaseMem (I : ExecutionEnv) : ByteArray :=
  wordAt32Mem ⟨1⟩ (safeEnableModuleCheckMem I)

noncomputable def safeEnableModuleTargetHashMem (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem (safeEnableModuleWord I) (safeEnableModuleBaseMem I)

noncomputable def safeEnableModuleLogMem (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem ⟨1⟩ (safeEnableModuleTargetHashMem I)

theorem safeEnableModuleKeyValue_eq {I : ExecutionEnv}
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    keyValueToWord (safeEnableModuleKeyValue I) = safeEnableModuleWord I :=
  keyValueToWord_address_of_canonical (safeEnableModuleWord I) hcanon

theorem safeEnableModuleSlotFor_eq {I : ExecutionEnv}
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    safeEnableModuleSlotFor I = solcMappingSlot ⟨1⟩ (safeEnableModuleWord I) := by
  unfold safeEnableModuleSlotFor modulesSlot mapSlot solcMappingSlot
  rw [safeEnableModuleKeyValue_eq hcanon]

theorem safeEnableModuleAccountAddress_ofNat_zero_iff {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat = AccountAddress.ofNat 0 ↔ w = ⟨0⟩ := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    unfold AccountAddress.ofNat at hv
    simp only [Fin.val_ofNat] at hv
    have hwmod : w.toNat % AccountAddress.size = w.toNat := by
      exact Nat.mod_eq_of_lt (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
    rw [hwmod] at hv
    exact uint256_toNat_eq_zero hv
  · intro h
    rw [h]
    rfl

theorem safeEnableModuleAccountAddress_ofNat_one_iff {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat = AccountAddress.ofNat 1 ↔ w = ⟨1⟩ := by
  constructor
  · intro h
    apply u256_inj
    have hv := congrArg Fin.val h
    unfold AccountAddress.ofNat at hv
    simp only [Fin.val_ofNat] at hv
    have hwmod : w.toNat % AccountAddress.size = w.toNat := by
      exact Nat.mod_eq_of_lt (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
    rw [hwmod] at hv
    simpa [UInt256.toNat] using hv
  · intro h
    rw [h]
    rfl

theorem safeDecode_enableModule_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (enablemoduleTransition.params.map Param.name)
      (transitionSignature enablemoduleTransition).paramTypes I.calldata =
        some (safeEnableModuleLocals I) := by
  simpa [config, safeDecodeMode, enablemoduleTransition, safeEnableModuleLocals,
    safeEnableModuleValue, safeEnableModuleWord, addr] using
      (decodeCalldata_address_ok (cd := I.calldata) (x := "module")
        hsz36 hsmall hcanon)

theorem safeDecode_enableModule_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (enablemoduleTransition.params.map Param.name)
      (transitionSignature enablemoduleTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, enablemoduleTransition, addr] using
    (decodeCalldata_address_none_short (cd := I.calldata) (x := "module") hsz4 hshort)

theorem safeDecode_enableModule_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (enablemoduleTransition.params.map Param.name)
      (transitionSignature enablemoduleTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, enablemoduleTransition, addr] using
    (decodeCalldata_address_none_huge (cd := I.calldata) (x := "module") hbig)

theorem safeDecode_enableModule_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (enablemoduleTransition.params.map Param.name)
      (transitionSignature enablemoduleTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, enablemoduleTransition, safeEnableModuleWord, addr] using
    (decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "module")
      hsz36 hsmall hnc)

theorem safeEnableModuleVarEval {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I } evm
      (.var "module") = .ok (safeEnableModuleValue I) := by
  simp [evalExpr?, safeEnableModuleLocals, EvalResult.ofOption]

theorem safeEnableModuleStorageEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (modulesRef (.var "module"))) =
      .ok (.address (AccountAddress.ofNat (safeEnableModuleMaskedStorageWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeEnableModuleLocals I })
    (slot := modulesRef (.var "module"))
    (er := safeEnableModuleEvaledRef I)
    (t := .address)
    (loc := addrLoc (safeEnableModuleSlotFor I))
    (value := .address
      (AccountAddress.ofNat (safeEnableModuleMaskedStorageWord σ I).toNat))
    (hbase := by simp [modulesRef, safeEnableModuleLocals])
    (her := by
      simp [safeEnableModuleEvaledRef, safeEnableModuleKeyValue, safeEnableModuleValue,
        safeEnableModuleLocals, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        modulesRef, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
        bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [safeEnableModuleMaskedStorageWord, safeEnableModuleStorageWord, addrLoc,
        addressOffset0Loc] using
        storageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeEnableModuleSlotFor I))]

theorem safeEnableModuleSentinelStorageEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage modulesSentinelRef) =
      .ok (safeEnableModuleSentinelValue σ I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeEnableModuleLocals I })
    (slot := modulesSentinelRef)
    (er := safeEnableModuleSentinelEvaledRef)
    (t := .address)
    (loc := addrLoc safeEnableModuleSentinelSlot)
    (value := safeEnableModuleSentinelValue σ I)
    (hbase := by simp [modulesSentinelRef, safeEnableModuleLocals])
    (her := by
      simp [safeEnableModuleSentinelEvaledRef, modulesSentinelRef, safeEnableModuleLocals,
        evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [safeEnableModuleSentinelValue, safeEnableModuleMaskedSentinelWord,
        safeEnableModuleSentinelStorageWord, addrLoc, addressOffset0Loc] using
        storageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
          safeEnableModuleSentinelSlot)]

theorem safeEnableModuleModuleNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeEnableModuleWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") zeroAddr) =
      .ok (.bool false) := by
  have hmoduleAddr :
      AccountAddress.ofNat (safeEnableModuleWord I).toNat = AccountAddress.ofNat 0 := by
    rw [hzero]
    rfl
  have hmoduleBeq :
      (safeEnableModuleValue I == Value.address (AccountAddress.ofNat 0)) = true := by
    simp [safeEnableModuleValue, BEq.beq, hmoduleAddr]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeEnableModuleLocals, safeEnableModuleValue,
    hmoduleBeq]

theorem safeEnableModuleModuleNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") zeroAddr) =
      .ok (.bool true) := by
  have hmoduleAddrNe :
      AccountAddress.ofNat (safeEnableModuleWord I).toNat ≠ AccountAddress.ofNat 0 := by
    intro haddr
    exact hzero ((safeEnableModuleAccountAddress_ofNat_zero_iff hcanon).mp haddr)
  have hmoduleBeq :
      (safeEnableModuleValue I == Value.address (AccountAddress.ofNat 0)) = false := by
    simp [safeEnableModuleValue, BEq.beq, hmoduleAddrNe]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeEnableModuleLocals, safeEnableModuleValue,
    hmoduleBeq]

theorem safeEnableModuleModuleNeSentinel_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsent : safeEnableModuleWord I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") sentinelAddr) =
      .ok (.bool false) := by
  have hmoduleAddr :
      AccountAddress.ofNat (safeEnableModuleWord I).toNat = AccountAddress.ofNat 1 := by
    rw [hsent]
    rfl
  have hmoduleBeq :
      (safeEnableModuleValue I == Value.address (AccountAddress.ofNat 1)) = true := by
    simp [safeEnableModuleValue, BEq.beq, hmoduleAddr]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeEnableModuleLocals, safeEnableModuleValue,
    hmoduleBeq]

theorem safeEnableModuleModuleNeSentinel_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") sentinelAddr) =
      .ok (.bool true) := by
  have hmoduleAddrNe :
      AccountAddress.ofNat (safeEnableModuleWord I).toNat ≠ AccountAddress.ofNat 1 := by
    intro haddr
    exact hsent ((safeEnableModuleAccountAddress_ofNat_one_iff hcanon).mp haddr)
  have hmoduleBeq :
      (safeEnableModuleValue I == Value.address (AccountAddress.ofNat 1)) = false := by
    simp [safeEnableModuleValue, BEq.beq, hmoduleAddrNe]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeEnableModuleLocals, safeEnableModuleValue,
    hmoduleBeq]

theorem safeEnableModuleModuleGuard_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool true) := by
  have hleft := safeEnableModuleModuleNeZero_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
  have hright := safeEnableModuleModuleNeSentinel_true (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hsent
  unfold andE
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem safeEnableModuleModuleGuard_false_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeEnableModuleWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool false) := by
  have hleft := safeEnableModuleModuleNeZero_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
  unfold andE
  simp [evalExpr?, hleft, EvalResult.bind, bind, pure]

theorem safeEnableModuleModuleGuard_false_sentinel {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsent : safeEnableModuleWord I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool false) := by
  have hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus := by
    rw [hsent]
    native_decide
  have hzero : safeEnableModuleWord I ≠ ⟨0⟩ := by
    rw [hsent]
    native_decide
  have hleft := safeEnableModuleModuleNeZero_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
  have hright := safeEnableModuleModuleNeSentinel_false (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsent
  unfold andE
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem safeEnableModuleStorageEqZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeEnableModuleMaskedStorageWord σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.storage (modulesRef (.var "module"))) zeroAddr) =
      .ok (.bool true) := by
  have hstorage := safeEnableModuleStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddr :
      AccountAddress.ofNat (safeEnableModuleMaskedStorageWord σ I).toNat =
        AccountAddress.ofNat 0 := by
    rw [hzero]
    rfl
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeEnableModuleMaskedStorageWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = true := by
    simp [BEq.beq, hstorageAddr]
  unfold eqE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeEnableModuleStorageEqZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeEnableModuleMaskedStorageWord σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeEnableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.storage (modulesRef (.var "module"))) zeroAddr) =
      .ok (.bool false) := by
  have hstorage := safeEnableModuleStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddrNe :
      AccountAddress.ofNat (safeEnableModuleMaskedStorageWord σ I).toNat ≠
        AccountAddress.ofNat 0 := by
    intro haddr
    exact hzero ((safeEnableModuleAccountAddress_ofNat_zero_iff
      (solcAddrMask_result_canonical (safeEnableModuleStorageWord σ I))).mp haddr)
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeEnableModuleMaskedStorageWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false := by
    simp [BEq.beq, hstorageAddrNe]
  unfold eqE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeEnableModuleAssignTarget {cA gh bl σ σ₀ A I} {g : Sat256} :
    assignStorageRef? config { contract := contract, locals := safeEnableModuleLocals I }
        (initState cA gh bl σ σ₀ g A I) .storage (modulesRef (.var "module"))
        (safeEnableModuleSentinelValue σ I) =
      .ok ({ contract := contract, locals := safeEnableModuleLocals I },
        safeEnableModuleTargetPostState (initState cA gh bl σ σ₀ g A I) I) := by
  rw [assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeEnableModuleLocals I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (evm' := safeEnableModuleTargetPostState (initState cA gh bl σ σ₀ g A I) I)
    (slot := modulesRef (.var "module"))
    (er := safeEnableModuleEvaledRef I)
    (ty := addrSt)
    (loc := addrLoc (safeEnableModuleSlotFor I))
    (value := safeEnableModuleSentinelValue σ I)
    (hbase := by simp [modulesRef, safeEnableModuleLocals])
    (her := by
      simp [safeEnableModuleEvaledRef, safeEnableModuleKeyValue, safeEnableModuleValue,
        safeEnableModuleLocals, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        modulesRef, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
        bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hscalar := by simp [safeEnableModuleSentinelValue])
    (hstore := by
      simpa [safeEnableModuleTargetPostState, safeEnableModuleSentinelValue,
        safeEnableModuleMaskedSentinelWord, safeEnableModuleSentinelStorageWord,
        safeEnableModuleStorageWord, addrLoc, addressOffset0Loc] using
        storageLocStore_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeEnableModuleSlotFor I) (safeEnableModuleMaskedSentinelWord σ I)
          (solcAddrMask_result_canonical (safeEnableModuleSentinelStorageWord σ I)))]

theorem safeEnableModuleAssignSentinel {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := safeEnableModuleLocals I }
        (safeEnableModuleTargetPostState (initState cA gh bl σ σ₀ g A I) I)
        .storage modulesSentinelRef (safeEnableModuleValue I) =
      .ok ({ contract := contract, locals := safeEnableModuleLocals I },
        safeEnableModulePostState (initState cA gh bl σ σ₀ g A I) I) := by
  rw [assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeEnableModuleLocals I })
    (evm := safeEnableModuleTargetPostState (initState cA gh bl σ σ₀ g A I) I)
    (evm' := safeEnableModulePostState (initState cA gh bl σ σ₀ g A I) I)
    (slot := modulesSentinelRef)
    (er := safeEnableModuleSentinelEvaledRef)
    (ty := addrSt)
    (loc := addrLoc safeEnableModuleSentinelSlot)
    (value := safeEnableModuleValue I)
    (hbase := by simp [modulesSentinelRef, safeEnableModuleLocals])
    (her := by
      simp [safeEnableModuleSentinelEvaledRef, modulesSentinelRef, safeEnableModuleLocals,
        evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hscalar := by simp [safeEnableModuleValue])
    (hstore := by
      simpa [safeEnableModulePostState, safeEnableModuleSentinelPostState,
        safeEnableModuleValue, addrLoc, addressOffset0Loc] using
        storageLocStore_address_offset0
          (safeEnableModuleTargetPostState (initState cA gh bl σ σ₀ g A I) I)
          safeEnableModuleSentinelSlot (safeEnableModuleWord I) hcanon)]

theorem safeEnableModuleBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩)
    (hslotZero : safeEnableModuleMaskedStorageWord σ I = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeEnableModuleLocals I) enablemoduleTransition.body
      (.returned { contract := contract, locals := safeEnableModuleLocals I }
        (safeEnableModulePostState (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeEnableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeEnableModuleModuleGuard_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
      hsent)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeEnableModuleStorageEqZero_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hslotZero)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (safeEnableModuleSentinelStorageEval (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
      (safeEnableModuleAssignTarget (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign safeEnableModuleVarEval
      (safeEnableModuleAssignSentinel (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon)) ExecBlock.nil

theorem safeEnableModuleBodyReverts_auth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source ≠ I.codeOwner) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeEnableModuleLocals I) enablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeAuthorized_false (locals := safeEnableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth))

theorem safeEnableModuleBodyReverts_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hzero : safeEnableModuleWord I = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeEnableModuleLocals I) enablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeEnableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeEnableModuleModuleGuard_false_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero))

theorem safeEnableModuleBodyReverts_sentinel {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hsent : safeEnableModuleWord I = ⟨1⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeEnableModuleLocals I) enablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeEnableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeEnableModuleModuleGuard_false_sentinel (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsent))

theorem safeEnableModuleBodyReverts_enabled {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩)
    (hslotNonzero : safeEnableModuleMaskedStorageWord σ I ≠ ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeEnableModuleLocals I) enablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeEnableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeEnableModuleModuleGuard_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
      hsent)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeEnableModuleStorageEqZero_false (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hslotNonzero))

theorem safeEnableModuleDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1001⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1014⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have h9591 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1014⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9591⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9599 := h9591.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9599' := h9599
  rw [hlt] at h9599'
  have h9607 := h9599'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9607⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9607
  have h9608 := h9607.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076 := h9608.jumpdest (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨6891⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088 := h9076.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088' := h9088
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask,
    show uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) =
        safeEnableModuleWord I from rfl,
    solcAddrCanon_eq hcanon] at h9088'
  have h6840 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  have h6891 := h6840.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6897 := h6891.jumpdest (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [safeEnableModuleWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using h6897.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeEnableModuleDecodeReverts_len {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1001⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9591 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1014⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9591⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9599 := h9591.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9599' := h9599
  rw [hlt] at h9599'
  have h9604 := h9599'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9607⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h9604
  have h9604' := h9604.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9604'.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeEnableModuleDecodeReverts_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1001⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have heqZero :
      UInt256.eq (safeEnableModuleWord I)
        (UInt256.land (safeEnableModuleWord I) solcAddrMask) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnc (solcAddrCanonical_of_clean heq)
  have h9591 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1014⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9591⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9599 := h9591.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9599' := h9599
  rw [hlt] at h9599'
  have h9607 := h9599'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9607⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9607
  have h9608 := h9607.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076 := h9608.jumpdest (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨6891⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088 := h9076.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088' := h9088
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask,
    show uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) =
        safeEnableModuleWord I from rfl,
    heqZero] at h9088'
  have h9093 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9093.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeEnableModuleAuthorizedOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3168⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hauth : I.source = I.codeOwner) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3176⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3176⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨6757⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6761 := h6757.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h6761' := h6761
  rw [safeAddressEq_one hauth] at h6761'
  have h6781 := h6761'
    |>.push2 ⟨6781⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, h6781.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeEnableModuleAuthorizedReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3168⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hauth : I.source ≠ I.codeOwner) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3176⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨6757⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6761 := h6757.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h6761' := h6761
  rw [safeAddressEq_zero hauth] at h6761'
  have h6765 := h6761'
    |>.push2 ⟨6781⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have h6777 := h6765.push2 ⟨6781⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338345777⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have h6898 := h6777.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 h6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeEnableModuleRequireModuleOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3176⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3229⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeEnableModuleWord I) solcAddrMask =
      safeEnableModuleWord I :=
    solcAddrMask_clean hcanon
  have heqZero : UInt256.eq (safeEnableModuleWord I) ⟨1⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hsent (uInt256_eq_one_eq heq)
  have heqZeroLeft : UInt256.eq ⟨1⟩ (safeEnableModuleWord I) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hsent (uInt256_eq_one_eq heq).symm
  have rd3187 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd3187' := rd3187
  rw [hmask, hclean, isZero_eq_zero_of_ne hzero] at rd3187'
  have rd3193 := rd3187'
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨3207⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  have rd3206 := rd3193
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have rd3206' := rd3206
  rw [hmask, hclean, heqZeroLeft] at rd3206'
  have rd3229 := rd3206'
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨3229⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3229
  exact ⟨_, _, rd3229.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)⟩

theorem safeEnableModuleRequireModuleReverts_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3176⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hzero : safeEnableModuleWord I = ⟨0⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd3187 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd3187' := rd3187
  rw [hmask, hzero,
    show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ from by native_decide,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3187'
  have rd3207 := rd3187'
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨3207⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3207
  have rd3213 := rd3207
    |>.push2 ⟨3229⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd6898 := rd3213
    |>.push2 ⟨3229⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338410545⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 rd6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeEnableModuleRequireModuleReverts_sentinel {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3176⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hsent : safeEnableModuleWord I = ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus := by
    rw [hsent]
    native_decide
  have hzero : safeEnableModuleWord I ≠ ⟨0⟩ := by
    rw [hsent]
    native_decide
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeEnableModuleWord I) solcAddrMask =
      safeEnableModuleWord I :=
    solcAddrMask_clean hcanon
  have hcleanLeft : UInt256.land solcAddrMask (safeEnableModuleWord I) =
      safeEnableModuleWord I :=
    solcAddrMask_clean_left hcanon
  have hcleanLeft : UInt256.land solcAddrMask (safeEnableModuleWord I) =
      safeEnableModuleWord I :=
    solcAddrMask_clean_left hcanon
  have rd3187 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd3187' := rd3187
  rw [hmask, hclean, isZero_eq_zero_of_ne hzero] at rd3187'
  have rd3193 := rd3187'
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨3207⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  have rd3206 := rd3193
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have rd3206' := rd3206
  rw [hmask, hclean, hsent, show UInt256.eq (⟨1⟩ : UInt256) ⟨1⟩ = ⟨1⟩ from by
    decide] at rd3206'
  have rd3207 := rd3206'
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3207
  have rd3213 := rd3207
    |>.push2 ⟨3229⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd6898 := rd3213
    |>.push2 ⟨3229⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338410545⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 rd6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeEnableModuleRequireSlotOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3229⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hslotZero : safeEnableModuleMaskedStorageWord σ I = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3277⟩
      [safeEnableModuleWord I, ⟨664⟩, sel]
      (twoWordHashMem (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeEnableModuleWord I) solcAddrMask =
      safeEnableModuleWord I :=
    solcAddrMask_clean hcanon
  have hcleanLeft : UInt256.land solcAddrMask (safeEnableModuleWord I) =
      safeEnableModuleWord I :=
    solcAddrMask_clean_left hcanon
  have hword :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)) =
        safeEnableModuleStorageWord σ I := by
    unfold safeEnableModuleStorageWord
    rw [safeEnableModuleSlotFor_eq hcanon]
  have hmaskedWord :
      UInt256.land
        (Option.option ⟨0⟩
          (fun acc => Batteries.RBMap.findD acc.storage
            (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) solcAddrMask =
        safeEnableModuleMaskedStorageWord σ I := by
    simpa [safeEnableModuleMaskedStorageWord] using
      congrArg (fun w => UInt256.land w solcAddrMask) hword
  have rd3240 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd3240' := rd3240
  rw [hmask, hcleanLeft] at rd3240'
  have rd3243 := rd3240'
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd3244 := rd3243.mstore 0
    (wordAt0Mem (safeEnableModuleWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3249pre := rd3244
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3249 := rd3249pre.mstore 0
    (twoWordHashMem (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)
    solcFreePtrMem_size
  have rd3253pre := rd3249
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd3253 := rd3253pre.keccak256 0 (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3254⟩ := rd3253.sload (by native_decide) (by evm_ov)
  have rd3256 := rd3254.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd3256' := rd3256
  rw [hmaskedWord, hslotZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3256'
  have rd3277 := rd3256'
    |>.push2 ⟨3277⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa using rd3277⟩

theorem safeEnableModuleRequireSlotReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3229⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hslotNonzero : safeEnableModuleMaskedStorageWord σ I ≠ ⟨0⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeEnableModuleWord I) solcAddrMask =
      safeEnableModuleWord I :=
    solcAddrMask_clean hcanon
  have hcleanLeft : UInt256.land solcAddrMask (safeEnableModuleWord I) =
      safeEnableModuleWord I :=
    solcAddrMask_clean_left hcanon
  have hword :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)) =
        safeEnableModuleStorageWord σ I := by
    unfold safeEnableModuleStorageWord
    rw [safeEnableModuleSlotFor_eq hcanon]
  have hmaskedWord :
      UInt256.land
        (Option.option ⟨0⟩
          (fun acc => Batteries.RBMap.findD acc.storage
            (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) solcAddrMask =
        safeEnableModuleMaskedStorageWord σ I := by
    simpa [safeEnableModuleMaskedStorageWord] using
      congrArg (fun w => UInt256.land w solcAddrMask) hword
  have hnotZero :
      UInt256.isZero (safeEnableModuleMaskedStorageWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hslotNonzero
  have rd3240 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd3240' := rd3240
  rw [hmask, hcleanLeft] at rd3240'
  have rd3243 := rd3240'
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd3244 := rd3243.mstore 0
    (wordAt0Mem (safeEnableModuleWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3249pre := rd3244
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3249 := rd3249pre.mstore 0
    (twoWordHashMem (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)
    solcFreePtrMem_size
  have rd3253pre := rd3249
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd3253 := rd3253pre.keccak256 0 (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3254⟩ := rd3253.sload (by native_decide) (by evm_ov)
  have rd3256 := rd3254.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd3256' := rd3256
  rw [hmaskedWord, hnotZero] at rd3256'
  have rd3261 := rd3256'
    |>.push2 ⟨3277⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd6898 := rd3261
    |>.push2 ⟨3277⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨153169205273⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨217⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 rd6898
      (twoWordHashMem_size_96 (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem_size
        solcFreePtrMem_read64)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeEnableModuleStoreLog {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3277⟩
      [safeEnableModuleWord I, ⟨664⟩, sel] (safeEnableModuleCheckMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeEnableModulePostMap σ I) ByteArray.empty := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeEnableModuleWord I) solcAddrMask =
      safeEnableModuleWord I :=
    solcAddrMask_clean hcanon
  have hcleanLeft : UInt256.land solcAddrMask (safeEnableModuleWord I) =
      safeEnableModuleWord I :=
    solcAddrMask_clean_left hcanon
  have hsentMasked :
      UInt256.land (safeEnableModuleSentinelStorageWord σ I) solcAddrMask =
        safeEnableModuleMaskedSentinelWord σ I := rfl
  have htargetSlot :
      solcMappingSlot ⟨1⟩ (safeEnableModuleWord I) = safeEnableModuleSlotFor I := by
    rw [safeEnableModuleSlotFor_eq hcanon]
  have htargetLoaded :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)) =
        safeEnableModuleStorageWord σ I := by
    unfold safeEnableModuleStorageWord
    rw [safeEnableModuleSlotFor_eq hcanon]
  have htargetLoadedRaw :
      Option.option ⟨0⟩
        (fun ac => Batteries.RBMap.findD ac.storage
          (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I)) ⟨0⟩)
        (Batteries.RBMap.find? σ I.codeOwner) =
        safeEnableModuleStorageWord σ I := by
    simpa [solcSlotWord] using htargetLoaded
  have hsentMaskedRaw :
      UInt256.land
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage safeEnableModuleSentinelSlot ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) solcAddrMask =
        safeEnableModuleMaskedSentinelWord σ I := by
    simpa [safeEnableModuleSentinelStorageWord, solcSlotWord] using hsentMasked
  have htargetStore :
      UInt256.lor
        (UInt256.land (UInt256.lnot solcAddrMask) (safeEnableModuleStorageWord σ I))
        (safeEnableModuleMaskedSentinelWord σ I) =
        safeEnableModuleTargetStoreWord σ I := by
    unfold safeEnableModuleTargetStoreWord setAddressOffset0Word safeEnableModuleMaskedSentinelWord
    rw [Reasoning.Theory.u256_land_comm (UInt256.lnot solcAddrMask)
      (safeEnableModuleStorageWord σ I)]
    rw [solcAddrMask_clean (solcAddrMask_result_canonical
      (safeEnableModuleSentinelStorageWord σ I))]
  have hsentStore :
      UInt256.lor (safeEnableModuleWord I)
        (UInt256.land (UInt256.lnot solcAddrMask)
          (solcSlotWord (safeEnableModuleTargetPostMap σ I) I safeEnableModuleSentinelSlot)) =
        safeEnableModuleSentinelStoreWord σ I := by
    unfold safeEnableModuleSentinelStoreWord setAddressOffset0Word
    rw [Reasoning.Theory.u256_land_comm (UInt256.lnot solcAddrMask)
      (solcSlotWord (safeEnableModuleTargetPostMap σ I) I safeEnableModuleSentinelSlot)]
    rw [Reasoning.Theory.u256_lor_comm (safeEnableModuleWord I)]
    rw [hclean]
  have hsentStoreRaw :
      UInt256.lor (safeEnableModuleWord I)
        (UInt256.land (UInt256.lnot solcAddrMask)
          (Option.option ⟨0⟩
            (fun ac => Batteries.RBMap.findD ac.storage safeEnableModuleSentinelSlot ⟨0⟩)
            (Batteries.RBMap.find?
              (sstoreAccountMap I.codeOwner σ
                (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I))
                (safeEnableModuleTargetStoreWord σ I)) I.codeOwner))) =
        safeEnableModuleSentinelStoreWord σ I := by
    simpa [solcSlotWord, safeEnableModuleTargetPostMap, htargetSlot] using hsentStore
  have htargetHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((safeEnableModuleTargetHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (safeEnableModuleWord I) := by
    unfold safeEnableModuleTargetHashMem safeEnableModuleBaseMem safeEnableModuleCheckMem
    rw [wordAt0Mem_after_wordAt32Mem_read0_64]
    · unfold solcMappingSlot
      exact mappingSlot_single (safeEnableModuleWord I) ⟨1⟩
    · exact twoWordHashMem_size_96 (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem_size
  have htargetHashSize :
      (safeEnableModuleTargetHashMem I).size = 96 := by
    unfold safeEnableModuleTargetHashMem safeEnableModuleBaseMem safeEnableModuleCheckMem
    exact wordAt0Mem_size_96 (safeEnableModuleWord I)
      (wordAt32Mem_size_96 ⟨1⟩
        (twoWordHashMem_size_96 (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem_size))
  have hlogMemSize : (safeEnableModuleLogMem I).size = 96 := by
    unfold safeEnableModuleLogMem
    exact wordAt0Mem_size_96 ⟨1⟩ htargetHashSize
  have hlogMemRead64 :
      (safeEnableModuleLogMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold safeEnableModuleLogMem
    exact wordAt0Mem_read64 ⟨1⟩ htargetHashSize (by
      unfold safeEnableModuleTargetHashMem safeEnableModuleBaseMem safeEnableModuleCheckMem
      exact wordAt0Mem_read64 (safeEnableModuleWord I)
        (wordAt32Mem_size_96 ⟨1⟩
          (twoWordHashMem_size_96 (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem_size))
        (wordAt32Mem_read64 ⟨1⟩
          (twoWordHashMem_size_96 (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem_size)
          (twoWordHashMem_read64 (safeEnableModuleWord I) ⟨1⟩ solcFreePtrMem_size
            solcFreePtrMem_read64)))
  have rd3284pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd3284 := rd3284pre.mstore 0 (safeEnableModuleBaseMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd3319pre := rd3284
    |>.pushConst safeEnableModuleSentinelSlot (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3319⟩ := rd3319pre.sload (by native_decide) (by evm_ov)
  have rd3330 := rd3319
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd3330' := rd3330
  rw [hmask, hcleanLeft] at rd3330'
  have rd3333 := rd3330'
    |>.push0 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd3334 := rd3333.mstore 0 (safeEnableModuleTargetHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd3339pre := rd3334
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
  have rd3339 := rd3339pre.keccak256 0 (solcMappingSlot ⟨1⟩ (safeEnableModuleWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using htargetHash)
    (by native_decide) (by evm_ov)
  have rd3340 := rd3339.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3341⟩ := rd3340.sload (by native_decide) (by evm_ov)
  have rd3345 := rd3341
    |>.swap5 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap6 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd3345' := rd3345
  rw [htargetLoadedRaw, hsentMaskedRaw] at rd3345'
  have rd3358 := rd3345'
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.not (by native_decide) (by evm_ov)
    |>.swap5 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.lor (by native_decide) (by evm_ov)
  have rd3358' := rd3358
  rw [hmask, htargetStore] at rd3358'
  have rd3360 := rd3358'
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3361⟩ := rd3360.sstore hperm (by native_decide) (by evm_ov)
  have rd3364pre := rd3361
    |>.swap5 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
  have rd3364 := rd3364pre.mstore 0 (safeEnableModuleLogMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd3365 := rd3364.dup4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3366⟩ := rd3365.sload (by native_decide) (by evm_ov)
  have rd3371 := rd3366
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.lor (by native_decide) (by evm_ov)
  have rd3371' := rd3371
  rw [hsentStoreRaw] at rd3371'
  have rd3373 := rd3371'
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3374⟩ := rd3373.sstore hperm (by native_decide) (by evm_ov)
  have rd3375 := rd3374.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost
    (mloadFreePtrValue
      (by rw [hlogMemSize]; decide)
      (by native_decide)
      hlogMemRead64)
    (by native_decide) (by evm_ov)
  have rd3412pre := rd3375
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pushConst safeEnableModuleEnabledTopic (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have rd3413 := RD.log2 0 (UInt256.ofNat 3) rd3412pre (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by change 3 ≤ 1024; decide)
  have rd664 := rd3413
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd665 := rd664.jumpdest (by native_decide) (by evm_ov)
  simpa [safeEnableModulePostMap, safeEnableModuleTargetPostMap, htargetSlot] using
    rd665.stop (by native_decide) (by evm_ov)

theorem safeEnableModuleX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩)
    (hslotZero : safeEnableModuleMaskedStorageWord σ I = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 11)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeEnableModulePostMap σ I) ByteArray.empty := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1014⟩ :=
    safeEnableModuleDecodeOk h1001 hsz36 hsmall hsize hcanon
  have h3168 := h1014.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3168⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h3176⟩ := safeEnableModuleAuthorizedOk h3168 hauth
  obtain ⟨_, _, h3229⟩ := safeEnableModuleRequireModuleOk h3176 hcanon hzero hsent
  obtain ⟨_, _, h3277⟩ := safeEnableModuleRequireSlotOk h3229 hcanon hslotZero
  exact safeEnableModuleStoreLog h3277 hperm hcanon

theorem safeEnableModuleX_authRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hauth : I.source ≠ I.codeOwner) (hsel : selIs I (safeSelBytes 11)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1014⟩ :=
    safeEnableModuleDecodeOk h1001 hsz36 hsmall hsize hcanon
  have h3168 := h1014.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3168⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  exact safeEnableModuleAuthorizedReverts h3168 hauth

theorem safeEnableModuleX_zeroRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I = ⟨0⟩) (hsel : selIs I (safeSelBytes 11)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1014⟩ :=
    safeEnableModuleDecodeOk h1001 hsz36 hsmall hsize hcanon
  have h3168 := h1014.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3168⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h3176⟩ := safeEnableModuleAuthorizedOk h3168 hauth
  exact safeEnableModuleRequireModuleReverts_zero h3176 hzero

theorem safeEnableModuleX_sentinelRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hsent : safeEnableModuleWord I = ⟨1⟩) (hsel : selIs I (safeSelBytes 11)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1014⟩ :=
    safeEnableModuleDecodeOk h1001 hsz36 hsmall hsize hcanon
  have h3168 := h1014.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3168⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h3176⟩ := safeEnableModuleAuthorizedOk h3168 hauth
  exact safeEnableModuleRequireModuleReverts_sentinel h3176 hsent

theorem safeEnableModuleX_enabledRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩)
    (hslotNonzero : safeEnableModuleMaskedStorageWord σ I ≠ ⟨0⟩)
    (hsel : selIs I (safeSelBytes 11)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1014⟩ :=
    safeEnableModuleDecodeOk h1001 hsz36 hsmall hsize hcanon
  have h3168 := h1014.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3168⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h3176⟩ := safeEnableModuleAuthorizedOk h3168 hauth
  obtain ⟨_, _, h3229⟩ := safeEnableModuleRequireModuleOk h3176 hcanon hzero hsent
  exact safeEnableModuleRequireSlotReverts h3229 hcanon hslotNonzero

theorem safeEnableModuleBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩)
    (hslotZero : safeEnableModuleMaskedStorageWord σ_evm I = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have htargetWord :
      safeEnableModuleStorageWord σ_evm I =
        safeEnableModuleStorageWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeEnableModuleSlotFor I) ⟨0⟩
  have hsentWord :
      safeEnableModuleSentinelStorageWord σ_evm I =
        safeEnableModuleSentinelStorageWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner safeEnableModuleSentinelSlot ⟨0⟩
  have hslotZeroSolm : safeEnableModuleMaskedStorageWord σ_solm I = ⟨0⟩ := by
    unfold safeEnableModuleMaskedStorageWord
    rw [← htargetWord]
    exact hslotZero
  have htargetStoreWord :
      safeEnableModuleTargetStoreWord σ_evm I =
        safeEnableModuleTargetStoreWord σ_solm I := by
    unfold safeEnableModuleTargetStoreWord safeEnableModuleMaskedSentinelWord
    rw [htargetWord, hsentWord]
  have htargetAccounts :
      accountMapEquiv (safeEnableModuleTargetPostMap σ_evm I)
        (safeEnableModuleTargetPostMap σ_solm I) := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner
      (safeEnableModuleSlotFor I) (safeEnableModuleTargetStoreWord σ_evm I) hAccounts
    simpa [safeEnableModuleTargetPostMap, ← htargetStoreWord] using hstore
  have hsentinelLoad :
      solcSlotWord (safeEnableModuleTargetPostMap σ_evm I) I
          safeEnableModuleSentinelSlot =
        solcSlotWord (safeEnableModuleTargetPostMap σ_solm I) I
          safeEnableModuleSentinelSlot :=
    accountMapEquiv_storage_findD htargetAccounts I.codeOwner safeEnableModuleSentinelSlot
      ⟨0⟩
  have hsentStoreWord :
      safeEnableModuleSentinelStoreWord σ_evm I =
        safeEnableModuleSentinelStoreWord σ_solm I := by
    unfold safeEnableModuleSentinelStoreWord
    rw [hsentinelLoad]
  have hpostAccounts :
      accountMapEquiv (safeEnableModulePostMap σ_evm I)
        (safeEnableModulePostMap σ_solm I) := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner
      safeEnableModuleSentinelSlot (safeEnableModuleSentinelStoreWord σ_evm I)
      htargetAccounts
    simpa [safeEnableModulePostMap, ← hsentStoreWord] using hstore
  have hbody := safeEnableModuleBodyReturns (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hwv hauth hcanon hzero hsent hslotZeroSolm
  have hcreated :
      (cA, safeEnableModulePostMap σ_evm I).1 =
        (safeEnableModulePostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).createdAccounts := by
    simp [safeEnableModulePostState, safeEnableModuleTargetPostState,
      safeEnableModuleSentinelPostState, initState, storageStore_createdAccounts]
  have haccounts :
      accountMapEquiv (cA, safeEnableModulePostMap σ_evm I).2
        (safeEnableModulePostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
    simpa [safeEnableModulePostMap, safeEnableModuleTargetPostMap,
      safeEnableModulePostState, safeEnableModuleTargetPostState,
      safeEnableModuleSentinelPostState, safeEnableModuleTargetStoreWord,
      safeEnableModuleSentinelStoreWord, safeEnableModuleStorageWord,
      safeEnableModuleSentinelStorageWord, safeEnableModuleMaskedSentinelWord,
      initState, storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, solcSlotWord] using hpostAccounts
  have henc : returnEquiv ByteArray.empty none enablemoduleTransition.returnType := by
    rw [show enablemoduleTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact safeReEquivExecGen hcode
    (safeEnableModuleX_ok (g := Sat256.ofUInt256 g) hcode hwv hperm hsz36 hsmall
      hsize hauth hcanon hzero hsent hslotZero hsel)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_ok hsz36 hsmall hcanon)
    hbody hcreated haccounts henc

theorem safeEnableModuleBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) (hsel : selIs I (safeSelBytes 11)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode
    (safeEnableModuleDecodeReverts_len h1001 hlt)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_none_short hsz4 hshort)

theorem safeEnableModuleBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 11)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact safeReEquivDecodeFailed hcode
    (safeEnableModuleDecodeReverts_len h1001 hlt)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_none_huge hbig)

theorem safeEnableModuleBodyCoreDecodeFailed_noncanon
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 11)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1001⟩ := safeGuardPeelOk (gt := ⟨999⟩) h988 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  exact safeReEquivDecodeFailed hcode
    (safeEnableModuleDecodeReverts_noncanon h1001 hsz36 hsmall hsize hnc)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_none_noncanon hsz36 hsmall hnc)

theorem safeEnableModuleBodyCoreRevert_auth
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hauth : I.source ≠ I.codeOwner) (hsel : selIs I (safeSelBytes 11)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact safeReEquivExecRev hcode
    (safeEnableModuleX_authRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36
      hsmall hsize hcanon hauth hsel)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_ok hsz36 hsmall hcanon)
    (safeEnableModuleBodyReverts_auth (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth)

theorem safeEnableModuleBodyCoreRevert_zero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I = ⟨0⟩) (hsel : selIs I (safeSelBytes 11)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact safeReEquivExecRev hcode
    (safeEnableModuleX_zeroRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36
      hsmall hsize hauth hcanon hzero hsel)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_ok hsz36 hsmall hcanon)
    (safeEnableModuleBodyReverts_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth hzero)

theorem safeEnableModuleBodyCoreRevert_sentinel
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hsent : safeEnableModuleWord I = ⟨1⟩) (hsel : selIs I (safeSelBytes 11)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact safeReEquivExecRev hcode
    (safeEnableModuleX_sentinelRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36
      hsmall hsize hauth hcanon hsent hsel)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_ok hsz36 hsmall hcanon)
    (safeEnableModuleBodyReverts_sentinel (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth hsent)

theorem safeEnableModuleBodyCoreRevert_enabled
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeEnableModuleWord I ≠ ⟨0⟩)
    (hsent : safeEnableModuleWord I ≠ ⟨1⟩)
    (hslotNonzero : safeEnableModuleMaskedStorageWord σ_evm I ≠ ⟨0⟩)
    (hsel : selIs I (safeSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have htargetWord :
      safeEnableModuleStorageWord σ_evm I =
        safeEnableModuleStorageWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeEnableModuleSlotFor I) ⟨0⟩
  have hslotNonzeroSolm : safeEnableModuleMaskedStorageWord σ_solm I ≠ ⟨0⟩ := by
    unfold safeEnableModuleMaskedStorageWord
    rw [← htargetWord]
    exact hslotNonzero
  exact safeReEquivExecRev hcode
    (safeEnableModuleX_enabledRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36
      hsmall hsize hauth hcanon hzero hsent hslotNonzero hsel)
    (safeSelectorDispatchEnableModule hsel)
    (safeDecode_enableModule_ok hsz36 hsmall hcanon)
    (safeEnableModuleBodyReverts_enabled (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth hcanon hzero hsent hslotNonzeroSolm)

theorem safeEnableModuleBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 11) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases hcanon : (safeEnableModuleWord I).toNat < EVM.addressModulus
        · by_cases hauth : I.source = I.codeOwner
          · by_cases hzero : safeEnableModuleWord I = ⟨0⟩
            · exact safeEnableModuleBodyCoreRevert_zero hcode hsize hwv hsz36
                hsmall hauth hcanon hzero hsel
            · by_cases hsent : safeEnableModuleWord I = ⟨1⟩
              · exact safeEnableModuleBodyCoreRevert_sentinel hcode hsize hwv hsz36
                  hsmall hauth hcanon hsent hsel
              · by_cases hslot : safeEnableModuleMaskedStorageWord σ_evm I = ⟨0⟩
                · exact safeEnableModuleBodyCoreOk hcode hsize hwv hperm hsz36 hsmall
                    hauth hcanon hzero hsent hslot hsel hAccounts
                · exact safeEnableModuleBodyCoreRevert_enabled hcode hsize hwv hsz36
                    hsmall hauth hcanon hzero hsent hslot hsel hAccounts
          · exact safeEnableModuleBodyCoreRevert_auth hcode hsize hwv hsz36 hsmall
              hcanon hauth hsel
        · exact safeEnableModuleBodyCoreDecodeFailed_noncanon hcode hsize hwv hsz36
            hsmall hcanon hsel
      · exact safeEnableModuleBodyCoreDecodeFailed_short hcode hsize hwv hsz4
          (by omega) hsel
    · exact safeEnableModuleBodyCoreDecodeFailed_huge hcode hsize hwv hsz4
        (by omega) hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 11) (by native_decide) hsel
    obtain ⟨_, _, h988⟩ := safeReachEnableModuleBody (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨999⟩) h988 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchEnableModule hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
