import Benchmarks.Safe.Routines

/-! # Safe `disableModule(address,address)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Benchmarks.Safe

abbrev safeDisableModulePrevWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeDisableModuleWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev safeDisableModulePrevValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeDisableModulePrevWord I).toNat)

abbrev safeDisableModuleValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeDisableModuleWord I).toNat)

abbrev safeDisableModuleLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "prevModule" (safeDisableModulePrevValue I)).insert "module"
    (safeDisableModuleValue I)

theorem safeDisableModuleLocals_index_prev (I : ExecutionEnv) :
    (safeDisableModuleLocals I)["prevModule"] = safeDisableModulePrevValue I := by
  unfold safeDisableModuleLocals
  rw [Std.HashMap.getElem_insert]
  simp

abbrev safeDisableModulePrevKeyValue (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (safeDisableModulePrevWord I).toNat)

abbrev safeDisableModuleKeyValue (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (safeDisableModuleWord I).toNat)

abbrev safeDisableModulePrevEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "modules", steps := [.mindex (safeDisableModulePrevKeyValue I)] }

abbrev safeDisableModuleEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "modules", steps := [.mindex (safeDisableModuleKeyValue I)] }

abbrev safeDisableModulePrevSlotFor (I : ExecutionEnv) : UInt256 :=
  modulesSlot (safeDisableModulePrevKeyValue I)

abbrev safeDisableModuleSlotFor (I : ExecutionEnv) : UInt256 :=
  modulesSlot (safeDisableModuleKeyValue I)

def safeDisableModulePrevStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeDisableModulePrevSlotFor I)

abbrev safeDisableModuleMaskedPrevStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (safeDisableModulePrevStorageWord σ I) solcAddrMask

def safeDisableModuleStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeDisableModuleSlotFor I)

abbrev safeDisableModuleMaskedStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (safeDisableModuleStorageWord σ I) solcAddrMask

def safeDisableModulePrevStoreWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word (safeDisableModulePrevStorageWord σ I)
    (safeDisableModuleMaskedStorageWord σ I)

def safeDisableModulePrevPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (safeDisableModulePrevSlotFor I)
    (safeDisableModulePrevStoreWord σ I)

def safeDisableModuleStoreWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (solcSlotWord (safeDisableModulePrevPostMap σ I) I (safeDisableModuleSlotFor I))
    ⟨0⟩

def safeDisableModulePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (safeDisableModulePrevPostMap σ I)
    (safeDisableModuleSlotFor I) (safeDisableModuleStoreWord σ I)

def safeDisableModulePrevPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (safeDisableModulePrevSlotFor I)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (safeDisableModulePrevSlotFor I))
      (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (safeDisableModuleSlotFor I))
        solcAddrMask))

def safeDisableModulePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (safeDisableModulePrevPostState evm I)
    (safeDisableModulePrevPostState evm I).executionEnv.codeOwner (safeDisableModuleSlotFor I)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad (safeDisableModulePrevPostState evm I)
        (safeDisableModulePrevPostState evm I).executionEnv.codeOwner
        (safeDisableModuleSlotFor I))
      ⟨0⟩)

def safeDisableModuleDisabledTopic : UInt256 :=
  ⟨77212943334077718225880146371662869374096224703205130304566303938038540354166⟩

noncomputable def safeDisableModulePrevCheckMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem

noncomputable def safeDisableModuleModuleHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (safeDisableModuleWord I) ⟨1⟩ (safeDisableModulePrevCheckMem I)

noncomputable def safeDisableModulePrevHashMem (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem (safeDisableModulePrevWord I) (safeDisableModuleModuleHashMem I)

noncomputable def safeDisableModuleLogMem (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem (safeDisableModuleWord I) (safeDisableModulePrevHashMem I)

theorem safeDisableModuleKeyValue_eq {I : ExecutionEnv}
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus) :
    keyValueToWord (safeDisableModuleKeyValue I) = safeDisableModuleWord I :=
  keyValueToWord_address_of_canonical (safeDisableModuleWord I) hcanon

theorem safeDisableModulePrevKeyValue_eq {I : ExecutionEnv}
    (hcanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus) :
    keyValueToWord (safeDisableModulePrevKeyValue I) = safeDisableModulePrevWord I :=
  keyValueToWord_address_of_canonical (safeDisableModulePrevWord I) hcanon

theorem safeDisableModuleSlotFor_eq {I : ExecutionEnv}
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus) :
    safeDisableModuleSlotFor I = solcMappingSlot ⟨1⟩ (safeDisableModuleWord I) := by
  unfold safeDisableModuleSlotFor modulesSlot mapSlot solcMappingSlot
  rw [safeDisableModuleKeyValue_eq hcanon]

theorem safeDisableModulePrevSlotFor_eq {I : ExecutionEnv}
    (hcanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus) :
    safeDisableModulePrevSlotFor I = solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I) := by
  unfold safeDisableModulePrevSlotFor modulesSlot mapSlot solcMappingSlot
  rw [safeDisableModulePrevKeyValue_eq hcanon]

theorem safeDisableModuleAccountAddress_ofNat_eq_iff {a b : UInt256}
    (ha : a.toNat < EVM.addressModulus) (hb : b.toNat < EVM.addressModulus) :
    AccountAddress.ofNat a.toNat = AccountAddress.ofNat b.toNat ↔ a = b := by
  constructor
  · intro h
    apply u256_inj
    have hv := congrArg Fin.val h
    unfold AccountAddress.ofNat at hv
    simp only [Fin.val_ofNat] at hv
    have hamod : a.toNat % AccountAddress.size = a.toNat := by
      exact Nat.mod_eq_of_lt (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using ha)
    have hbmod : b.toNat % AccountAddress.size = b.toNat := by
      exact Nat.mod_eq_of_lt (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hb)
    rw [hamod, hbmod] at hv
    simpa [UInt256.toNat] using hv
  · intro h
    rw [h]

theorem safeDecode_disableModule_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (disablemoduleTransition.params.map Param.name)
      (transitionSignature disablemoduleTransition).paramTypes I.calldata =
        some (safeDisableModuleLocals I) := by
  simpa [config, safeDecodeMode, disablemoduleTransition, safeDisableModuleLocals,
    safeDisableModulePrevValue, safeDisableModuleValue, safeDisableModulePrevWord,
    safeDisableModuleWord, addr] using
      (decodeCalldata_address_address_ok (cd := I.calldata) (x := "prevModule")
        (y := "module") hsz68 hsmall hprevCanon hcanon)

theorem safeDecode_disableModule_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode
      (disablemoduleTransition.params.map Param.name)
      (transitionSignature disablemoduleTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, disablemoduleTransition, addr] using
    (decodeCalldata_address_address_none_short (cd := I.calldata) (x := "prevModule")
      (y := "module") hsz4 hshort)

theorem safeDecode_disableModule_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (disablemoduleTransition.params.map Param.name)
      (transitionSignature disablemoduleTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, disablemoduleTransition, addr] using
    (decodeCalldata_address_address_none_huge (cd := I.calldata) (x := "prevModule")
      (y := "module") hbig)

theorem safeDecode_disableModule_none_noncanon_prev {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeDisableModulePrevWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (disablemoduleTransition.params.map Param.name)
      (transitionSignature disablemoduleTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, disablemoduleTransition, safeDisableModulePrevWord,
    addr] using
      (decodeCalldata_address_address_none_noncanon0 (cd := I.calldata)
        (x := "prevModule") (y := "module") hsz68 hsmall hnc)

theorem safeDecode_disableModule_none_noncanon_module {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (safeDisableModuleWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (disablemoduleTransition.params.map Param.name)
      (transitionSignature disablemoduleTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, disablemoduleTransition, safeDisableModulePrevWord,
    safeDisableModuleWord, addr] using
      (decodeCalldata_address_address_none_noncanon1 (cd := I.calldata)
        (x := "prevModule") (y := "module") hsz68 hsmall hprevCanon hnc)

theorem safeDisableModulePrevVarEval {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I } evm
      (.var "prevModule") = .ok (safeDisableModulePrevValue I) := by
  simp [evalExpr?, safeDisableModuleLocals, EvalResult.ofOption,
    safeDisableModuleLocals_index_prev]

theorem safeDisableModuleVarEval {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I } evm
      (.var "module") = .ok (safeDisableModuleValue I) := by
  simp [evalExpr?, safeDisableModuleLocals, EvalResult.ofOption]

theorem safeDisableModulePrevStorageEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (modulesRef (.var "prevModule"))) =
      .ok (.address
        (AccountAddress.ofNat (safeDisableModuleMaskedPrevStorageWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeDisableModuleLocals I })
    (slot := modulesRef (.var "prevModule"))
    (er := safeDisableModulePrevEvaledRef I)
    (t := .address)
    (loc := addrLoc (safeDisableModulePrevSlotFor I))
    (value := .address
      (AccountAddress.ofNat (safeDisableModuleMaskedPrevStorageWord σ I).toNat))
    (hbase := by simp [modulesRef, safeDisableModuleLocals])
    (her := by
      simp [safeDisableModulePrevEvaledRef, safeDisableModulePrevKeyValue,
        safeDisableModulePrevValue, safeDisableModuleLocals, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, modulesRef, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, safeDisableModuleLocals_index_prev])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [safeDisableModuleMaskedPrevStorageWord, safeDisableModulePrevStorageWord,
        addrLoc, addressOffset0Loc] using
        storageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeDisableModulePrevSlotFor I))]

theorem safeDisableModuleStorageEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (modulesRef (.var "module"))) =
      .ok (.address
        (AccountAddress.ofNat (safeDisableModuleMaskedStorageWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeDisableModuleLocals I })
    (slot := modulesRef (.var "module"))
    (er := safeDisableModuleEvaledRef I)
    (t := .address)
    (loc := addrLoc (safeDisableModuleSlotFor I))
    (value := .address
      (AccountAddress.ofNat (safeDisableModuleMaskedStorageWord σ I).toNat))
    (hbase := by simp [modulesRef, safeDisableModuleLocals])
    (her := by
      simp [safeDisableModuleEvaledRef, safeDisableModuleKeyValue, safeDisableModuleValue,
        safeDisableModuleLocals, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        modulesRef, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
        bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [safeDisableModuleMaskedStorageWord, safeDisableModuleStorageWord, addrLoc,
        addressOffset0Loc] using
        storageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeDisableModuleSlotFor I))]

theorem safeDisableModuleModuleNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeDisableModuleWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") zeroAddr) =
      .ok (.bool false) := by
  have hmoduleAddr :
      AccountAddress.ofNat (safeDisableModuleWord I).toNat = AccountAddress.ofNat 0 := by
    rw [hzero]
    rfl
  have hmoduleBeq :
      (safeDisableModuleValue I == Value.address (AccountAddress.ofNat 0)) = true := by
    simp [safeDisableModuleValue, BEq.beq, hmoduleAddr]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeDisableModuleLocals, safeDisableModuleValue,
    hmoduleBeq]

theorem safeDisableModuleModuleNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeDisableModuleWord I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") zeroAddr) =
      .ok (.bool true) := by
  have hmoduleAddrNe :
      AccountAddress.ofNat (safeDisableModuleWord I).toNat ≠ AccountAddress.ofNat 0 := by
    intro haddr
    exact hzero ((safeDisableModuleAccountAddress_ofNat_eq_iff hcanon
      (by native_decide)).mp haddr)
  have hmoduleBeq :
      (safeDisableModuleValue I == Value.address (AccountAddress.ofNat 0)) = false := by
    simp [safeDisableModuleValue, BEq.beq, hmoduleAddrNe]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeDisableModuleLocals, safeDisableModuleValue,
    hmoduleBeq]

theorem safeDisableModuleModuleNeSentinel_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsent : safeDisableModuleWord I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") sentinelAddr) =
      .ok (.bool false) := by
  have hmoduleAddr :
      AccountAddress.ofNat (safeDisableModuleWord I).toNat = AccountAddress.ofNat 1 := by
    rw [hsent]
    rfl
  have hmoduleBeq :
      (safeDisableModuleValue I == Value.address (AccountAddress.ofNat 1)) = true := by
    simp [safeDisableModuleValue, BEq.beq, hmoduleAddr]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeDisableModuleLocals, safeDisableModuleValue,
    hmoduleBeq]

theorem safeDisableModuleModuleNeSentinel_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hsent : safeDisableModuleWord I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") sentinelAddr) =
      .ok (.bool true) := by
  have hmoduleAddrNe :
      AccountAddress.ofNat (safeDisableModuleWord I).toNat ≠ AccountAddress.ofNat 1 := by
    intro haddr
    exact hsent ((safeDisableModuleAccountAddress_ofNat_eq_iff hcanon
      (by native_decide)).mp haddr)
  have hmoduleBeq :
      (safeDisableModuleValue I == Value.address (AccountAddress.ofNat 1)) = false := by
    simp [safeDisableModuleValue, BEq.beq, hmoduleAddrNe]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeDisableModuleLocals, safeDisableModuleValue,
    hmoduleBeq]

theorem safeDisableModuleModuleGuard_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeDisableModuleWord I ≠ ⟨0⟩)
    (hsent : safeDisableModuleWord I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool true) := by
  have hleft := safeDisableModuleModuleNeZero_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
  have hright := safeDisableModuleModuleNeSentinel_true (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hsent
  unfold andE
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem safeDisableModuleModuleGuard_false_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeDisableModuleWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool false) := by
  have hleft := safeDisableModuleModuleNeZero_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
  unfold andE
  simp [evalExpr?, hleft, EvalResult.bind, bind, pure]

theorem safeDisableModuleModuleGuard_false_sentinel {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsent : safeDisableModuleWord I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool false) := by
  have hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus := by
    rw [hsent]
    native_decide
  have hzero : safeDisableModuleWord I ≠ ⟨0⟩ := by
    rw [hsent]
    native_decide
  have hleft := safeDisableModuleModuleNeZero_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
  have hright := safeDisableModuleModuleNeSentinel_false (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsent
  unfold andE
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem safeDisableModulePrevEqModule_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlink : safeDisableModuleMaskedPrevStorageWord σ I = safeDisableModuleWord I) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.storage (modulesRef (.var "prevModule"))) (.var "module")) =
      .ok (.bool true) := by
  have hstorage := safeDisableModulePrevStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have haddr :
      AccountAddress.ofNat (safeDisableModuleMaskedPrevStorageWord σ I).toNat =
        AccountAddress.ofNat (safeDisableModuleWord I).toNat := by
    rw [hlink]
  have hbeq :
      (Value.address
          (AccountAddress.ofNat (safeDisableModuleMaskedPrevStorageWord σ I).toNat) ==
        safeDisableModuleValue I) = true := by
    simp [safeDisableModuleValue, BEq.beq, haddr]
  unfold eqE
  simp [evalExpr?, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, safeDisableModuleLocals,
    safeDisableModuleValue, hbeq]

theorem safeDisableModulePrevEqModule_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hlink : safeDisableModuleMaskedPrevStorageWord σ I ≠ safeDisableModuleWord I) :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.storage (modulesRef (.var "prevModule"))) (.var "module")) =
      .ok (.bool false) := by
  have hstorage := safeDisableModulePrevStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have haddrNe :
      AccountAddress.ofNat (safeDisableModuleMaskedPrevStorageWord σ I).toNat ≠
        AccountAddress.ofNat (safeDisableModuleWord I).toNat := by
    intro haddr
    exact hlink ((safeDisableModuleAccountAddress_ofNat_eq_iff
      (solcAddrMask_result_canonical (safeDisableModulePrevStorageWord σ I)) hcanon).mp haddr)
  have hbeq :
      (Value.address
          (AccountAddress.ofNat (safeDisableModuleMaskedPrevStorageWord σ I).toNat) ==
        safeDisableModuleValue I) = false := by
    simp [safeDisableModuleValue, BEq.beq, haddrNe]
  unfold eqE
  simp [evalExpr?, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, safeDisableModuleLocals,
    safeDisableModuleValue, hbeq]

theorem safeDisableModuleAssignPrev {cA gh bl σ σ₀ A I} {g : Sat256} :
    assignStorageRef? config { contract := contract, locals := safeDisableModuleLocals I }
        (initState cA gh bl σ σ₀ g A I) .storage (modulesRef (.var "prevModule"))
        (.address (AccountAddress.ofNat (safeDisableModuleMaskedStorageWord σ I).toNat)) =
      .ok ({ contract := contract, locals := safeDisableModuleLocals I },
        safeDisableModulePrevPostState (initState cA gh bl σ σ₀ g A I) I) := by
  rw [assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeDisableModuleLocals I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (evm' := safeDisableModulePrevPostState (initState cA gh bl σ σ₀ g A I) I)
    (slot := modulesRef (.var "prevModule"))
    (er := safeDisableModulePrevEvaledRef I)
    (ty := addrSt)
    (loc := addrLoc (safeDisableModulePrevSlotFor I))
    (value := .address
      (AccountAddress.ofNat (safeDisableModuleMaskedStorageWord σ I).toNat))
    (hbase := by simp [modulesRef, safeDisableModuleLocals])
    (her := by
      simp [safeDisableModulePrevEvaledRef, safeDisableModulePrevKeyValue,
        safeDisableModulePrevValue, safeDisableModuleLocals, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, modulesRef, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, safeDisableModuleLocals_index_prev])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hscalar := by simp)
    (hstore := by
      simpa [safeDisableModulePrevPostState, safeDisableModuleMaskedStorageWord,
        safeDisableModuleStorageWord, safeDisableModulePrevStorageWord, addrLoc,
        addressOffset0Loc] using
        storageLocStore_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeDisableModulePrevSlotFor I) (safeDisableModuleMaskedStorageWord σ I)
          (solcAddrMask_result_canonical (safeDisableModuleStorageWord σ I)))]

theorem safeDisableModuleAssignModuleZero {cA gh bl σ σ₀ A I} {g : Sat256} :
    assignStorageRef? config { contract := contract, locals := safeDisableModuleLocals I }
        (safeDisableModulePrevPostState (initState cA gh bl σ σ₀ g A I) I)
        .storage (modulesRef (.var "module")) (Value.address (AccountAddress.ofNat 0)) =
      .ok ({ contract := contract, locals := safeDisableModuleLocals I },
        safeDisableModulePostState (initState cA gh bl σ σ₀ g A I) I) := by
  rw [assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeDisableModuleLocals I })
    (evm := safeDisableModulePrevPostState (initState cA gh bl σ σ₀ g A I) I)
    (evm' := safeDisableModulePostState (initState cA gh bl σ σ₀ g A I) I)
    (slot := modulesRef (.var "module"))
    (er := safeDisableModuleEvaledRef I)
    (ty := addrSt)
    (loc := addrLoc (safeDisableModuleSlotFor I))
    (value := Value.address (AccountAddress.ofNat 0))
    (hbase := by simp [modulesRef, safeDisableModuleLocals])
    (her := by
      simp [safeDisableModuleEvaledRef, safeDisableModuleKeyValue, safeDisableModuleValue,
        safeDisableModuleLocals, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        modulesRef, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
        bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hscalar := by simp)
    (hstore := by
      simpa [safeDisableModulePostState, addrLoc, addressOffset0Loc] using
        storageLocStore_address_offset0
          (safeDisableModulePrevPostState (initState cA gh bl σ σ₀ g A I) I)
          (safeDisableModuleSlotFor I) ⟨0⟩ (by native_decide))]

theorem safeDisableModuleZeroAddrEval {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := safeDisableModuleLocals I } evm
      zeroAddr = .ok (Value.address (AccountAddress.ofNat 0)) := by
  simp [evalExpr?, zeroAddr, addrSt, castValue?, EvalResult.ofOption, EvalResult.bind,
    bind, pure]

theorem safeDisableModuleBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeDisableModuleWord I ≠ ⟨0⟩)
    (hsent : safeDisableModuleWord I ≠ ⟨1⟩)
    (hlink : safeDisableModuleMaskedPrevStorageWord σ I = safeDisableModuleWord I) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeDisableModuleLocals I) disablemoduleTransition.body
      (.returned { contract := contract, locals := safeDisableModuleLocals I }
        (safeDisableModulePostState (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeDisableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeDisableModuleModuleGuard_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
      hsent)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeDisableModulePrevEqModule_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hlink)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (safeDisableModuleStorageEval (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
      (safeDisableModuleAssignPrev (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign safeDisableModuleZeroAddrEval
      (safeDisableModuleAssignModuleZero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))) ExecBlock.nil

theorem safeDisableModuleBodyReverts_auth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source ≠ I.codeOwner) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeDisableModuleLocals I) disablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeAuthorized_false (locals := safeDisableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth))

theorem safeDisableModuleBodyReverts_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hzero : safeDisableModuleWord I = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeDisableModuleLocals I) disablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeDisableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeDisableModuleModuleGuard_false_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero))

theorem safeDisableModuleBodyReverts_sentinel {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hsent : safeDisableModuleWord I = ⟨1⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeDisableModuleLocals I) disablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeDisableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeDisableModuleModuleGuard_false_sentinel (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsent))

theorem safeDisableModuleBodyReverts_unlinked {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeDisableModuleWord I ≠ ⟨0⟩)
    (hsent : safeDisableModuleWord I ≠ ⟨1⟩)
    (hlink : safeDisableModuleMaskedPrevStorageWord σ I ≠ safeDisableModuleWord I) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeDisableModuleLocals I) disablemoduleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeDisableModuleLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeDisableModuleModuleGuard_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hzero
      hsent)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeDisableModulePrevEqModule_false (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hlink))

theorem safeDisableModuleDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1390⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1403⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  have h10868 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1403⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨10868⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h10877 := h10868.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h10877' := h10877
  rw [hlt] at h10877'
  have h10885 := h10877'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨10885⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h10885
  have h10886 := h10885.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076a := h10886.jumpdest (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨10896⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088a := h9076a.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088a' := h9088a
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask,
    show uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) =
        safeDisableModulePrevWord I from rfl,
    solcAddrCanon_eq hprevCanon] at h9088a'
  have h6840a := h9088a'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  have h10896 := h6840a.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h10903 := h10896.jumpdest (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
  have h9076b := h10903
    |>.push2 ⟨10912⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088b := h9076b.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088b' := h9088b
  rw [hmask,
    show uInt256OfByteArray
          (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) =
        safeDisableModuleWord I from by
          simp [safeDisableModuleWord, calldataWord,
            show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide],
    solcAddrCanon_eq hcanon] at h9088b'
  have h6840b := h9088b'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  have h10912 := h6840b.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h10922 := h10912.jumpdest (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [safeDisableModulePrevWord, safeDisableModuleWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide]
      using h10922.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeDisableModuleDecodeReverts_len {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1390⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h10868 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1403⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨10868⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h10877 := h10868.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h10877' := h10877
  rw [hlt] at h10877'
  have h10884 := h10877'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨10885⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h10884
  have h10884' := h10884.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h10884'.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeDisableModuleDecodeReverts_noncanon_prev {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1390⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (safeDisableModulePrevWord I).toNat < EVM.addressModulus) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  have heqZero :
      UInt256.eq (safeDisableModulePrevWord I)
        (UInt256.land (safeDisableModulePrevWord I) solcAddrMask) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnc (solcAddrCanonical_of_clean heq)
  have h10868 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1403⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨10868⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h10877 := h10868.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h10877' := h10877
  rw [hlt] at h10877'
  have h10885 := h10877'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨10885⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h10885
  have h10886 := h10885.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076a := h10886.jumpdest (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨10896⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088a := h9076a.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088a' := h9088a
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask,
    show uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) =
        safeDisableModulePrevWord I from rfl,
    heqZero] at h9088a'
  have h9093 := h9088a'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9093.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeDisableModuleDecodeReverts_noncanon_module {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1390⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (safeDisableModuleWord I).toNat < EVM.addressModulus) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  have heqZero :
      UInt256.eq (safeDisableModuleWord I)
        (UInt256.land (safeDisableModuleWord I) solcAddrMask) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnc (solcAddrCanonical_of_clean heq)
  have h10868 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1403⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨10868⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h10877 := h10868.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h10877' := h10877
  rw [hlt] at h10877'
  have h10885 := h10877'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨10885⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h10885
  have h10886 := h10885.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076a := h10886.jumpdest (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨10896⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088a := h9076a.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088a' := h9088a
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask,
    show uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) =
        safeDisableModulePrevWord I from rfl,
    solcAddrCanon_eq hprevCanon] at h9088a'
  have h6840a := h9088a'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  have h10896 := h6840a.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h10903 := h10896.jumpdest (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
  have h9076b := h10903
    |>.push2 ⟨10912⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088b := h9076b.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088b' := h9088b
  rw [hmask,
    show uInt256OfByteArray
          (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) =
        safeDisableModuleWord I from by
          simp [safeDisableModuleWord, calldataWord,
            show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide],
    heqZero] at h9088b'
  have h9093 := h9088b'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9093.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeDisableModuleAuthorizedOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5524⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hauth : I.source = I.codeOwner) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5532⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨5532⟩ (by native_decide) (by evm_ov)
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

theorem safeDisableModuleAuthorizedReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5524⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hauth : I.source ≠ I.codeOwner) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨5532⟩ (by native_decide) (by evm_ov)
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

theorem safeDisableModuleRequireModuleOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5532⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hzero : safeDisableModuleWord I ≠ ⟨0⟩)
    (hsent : safeDisableModuleWord I ≠ ⟨1⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5585⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeDisableModuleWord I) solcAddrMask =
      safeDisableModuleWord I :=
    solcAddrMask_clean hcanon
  have heqZeroLeft : UInt256.eq ⟨1⟩ (safeDisableModuleWord I) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hsent (uInt256_eq_one_eq heq).symm
  have rd5543 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd5543' := rd5543
  rw [hmask, hclean, isZero_eq_zero_of_ne hzero] at rd5543'
  have rd5549 := rd5543'
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨5563⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  have rd5562 := rd5549
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have rd5562' := rd5562
  rw [hmask, hclean, heqZeroLeft] at rd5562'
  have rd5585 := rd5562'
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨5585⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5585
  exact ⟨_, _, rd5585.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)⟩

theorem safeDisableModuleRequireModuleReverts_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5532⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hzero : safeDisableModuleWord I = ⟨0⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd5543 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd5543' := rd5543
  rw [hmask, hzero,
    show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ from by native_decide,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5543'
  have rd5563 := rd5543'
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨5563⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5563
  have rd5568 := rd5563
    |>.push2 ⟨5585⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd6898 := rd5568
    |>.push2 ⟨5585⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338410545⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 rd6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeDisableModuleRequireModuleReverts_sentinel {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5532⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsent : safeDisableModuleWord I = ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus := by
    rw [hsent]
    native_decide
  have hzero : safeDisableModuleWord I ≠ ⟨0⟩ := by
    rw [hsent]
    native_decide
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeDisableModuleWord I) solcAddrMask =
      safeDisableModuleWord I :=
    solcAddrMask_clean hcanon
  have rd5543 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have rd5543' := rd5543
  rw [hmask, hclean, isZero_eq_zero_of_ne hzero] at rd5543'
  have rd5549 := rd5543'
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨5563⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  have rd5562 := rd5549
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have rd5562' := rd5562
  rw [hmask, hclean, hsent, show UInt256.eq (⟨1⟩ : UInt256) ⟨1⟩ = ⟨1⟩ from by
    decide] at rd5562'
  have rd5563 := rd5562'
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5563
  have rd5568 := rd5563
    |>.push2 ⟨5585⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd6898 := rd5568
    |>.push2 ⟨5585⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338410545⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 rd6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeDisableModuleRequireLinkOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5585⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hlink : safeDisableModuleMaskedPrevStorageWord σ I = safeDisableModuleWord I) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5637⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      (safeDisableModulePrevCheckMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k' C' := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hprevCleanLeft : UInt256.land solcAddrMask (safeDisableModulePrevWord I) =
      safeDisableModulePrevWord I :=
    solcAddrMask_clean_left hprevCanon
  have hclean : UInt256.land (safeDisableModuleWord I) solcAddrMask =
      safeDisableModuleWord I :=
    solcAddrMask_clean hcanon
  have hprevLoaded :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) =
        safeDisableModulePrevStorageWord σ I := by
    unfold safeDisableModulePrevStorageWord
    rw [safeDisableModulePrevSlotFor_eq hprevCanon]
  have hmaskedPrevRaw :
      UInt256.land
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) solcAddrMask =
        safeDisableModuleMaskedPrevStorageWord σ I := by
    simpa [safeDisableModuleMaskedPrevStorageWord] using
      congrArg (fun w => UInt256.land w solcAddrMask) hprevLoaded
  have hmaskedPrevRawLeft :
      UInt256.land solcAddrMask
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) =
        safeDisableModuleMaskedPrevStorageWord σ I := by
    rw [Reasoning.Theory.u256_land_comm solcAddrMask
      (Option.option ⟨0⟩
        (fun ac => Batteries.RBMap.findD ac.storage
          (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) ⟨0⟩)
        (Batteries.RBMap.find? σ I.codeOwner))]
    exact hmaskedPrevRaw
  have rd5596 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5596' := rd5596
  rw [hmask, hprevCleanLeft] at rd5596'
  have rd5599 := rd5596'
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd5600 := rd5599.mstore 0 (wordAt0Mem (safeDisableModulePrevWord I)
      solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd5605pre := rd5600
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5605 := rd5605pre.mstore 0 (safeDisableModulePrevCheckMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)
    solcFreePtrMem_size
  have rd5609pre := rd5605
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd5609 := rd5609pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost
    (by simpa [safeDisableModulePrevCheckMem,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5610⟩ := rd5609.sload (by native_decide) (by evm_ov)
  have rd5616 := rd5610
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have rd5616' := rd5616
  rw [hmaskedPrevRawLeft, hclean, hlink, uInt256_eq_self] at rd5616'
  have rd5637 := rd5616'
    |>.push2 ⟨5637⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [safeDisableModulePrevCheckMem] using rd5637⟩

theorem safeDisableModuleRequireLinkReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5585⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus)
    (hlink : safeDisableModuleMaskedPrevStorageWord σ I ≠ safeDisableModuleWord I) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hprevCleanLeft : UInt256.land solcAddrMask (safeDisableModulePrevWord I) =
      safeDisableModulePrevWord I :=
    solcAddrMask_clean_left hprevCanon
  have hclean : UInt256.land (safeDisableModuleWord I) solcAddrMask =
      safeDisableModuleWord I :=
    solcAddrMask_clean hcanon
  have hprevLoaded :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) =
        safeDisableModulePrevStorageWord σ I := by
    unfold safeDisableModulePrevStorageWord
    rw [safeDisableModulePrevSlotFor_eq hprevCanon]
  have hmaskedPrevRaw :
      UInt256.land
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) solcAddrMask =
        safeDisableModuleMaskedPrevStorageWord σ I := by
    simpa [safeDisableModuleMaskedPrevStorageWord] using
      congrArg (fun w => UInt256.land w solcAddrMask) hprevLoaded
  have hmaskedPrevRawLeft :
      UInt256.land solcAddrMask
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) =
        safeDisableModuleMaskedPrevStorageWord σ I := by
    rw [Reasoning.Theory.u256_land_comm solcAddrMask
      (Option.option ⟨0⟩
        (fun ac => Batteries.RBMap.findD ac.storage
          (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) ⟨0⟩)
        (Batteries.RBMap.find? σ I.codeOwner))]
    exact hmaskedPrevRaw
  have heqZero :
      UInt256.eq (safeDisableModuleWord I)
        (safeDisableModuleMaskedPrevStorageWord σ I) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hlink (uInt256_eq_one_eq heq).symm
  have heqZeroRev :
      UInt256.eq (safeDisableModuleMaskedPrevStorageWord σ I)
        (safeDisableModuleWord I) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hlink (uInt256_eq_one_eq heq)
  have rd5596 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5596' := rd5596
  rw [hmask, hprevCleanLeft] at rd5596'
  have rd5599 := rd5596'
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd5600 := rd5599.mstore 0 (wordAt0Mem (safeDisableModulePrevWord I)
      solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd5605pre := rd5600
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5605 := rd5605pre.mstore 0 (safeDisableModulePrevCheckMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)
    solcFreePtrMem_size
  have rd5609pre := rd5605
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd5609 := rd5609pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost
    (by simpa [safeDisableModulePrevCheckMem,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5610⟩ := rd5609.sload (by native_decide) (by evm_ov)
  have rd5616 := rd5610
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have rd5616' := rd5616
  rw [hmaskedPrevRawLeft, hclean, heqZero] at rd5616'
  have rd5620 := rd5616'
    |>.push2 ⟨5637⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd6898 := rd5620
    |>.push2 ⟨5637⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338410547⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 rd6898
      (twoWordHashMem_size_96 (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem_size
        solcFreePtrMem_read64)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeDisableModuleStoreLog {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5637⟩
      [safeDisableModuleWord I, safeDisableModulePrevWord I, ⟨664⟩, sel]
      (safeDisableModulePrevCheckMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus)
    (hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeDisableModulePostMap σ I) ByteArray.empty := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeDisableModuleWord I) solcAddrMask =
      safeDisableModuleWord I :=
    solcAddrMask_clean hcanon
  have hcleanLeft : UInt256.land solcAddrMask (safeDisableModuleWord I) =
      safeDisableModuleWord I :=
    solcAddrMask_clean_left hcanon
  have hprevCleanLeft : UInt256.land solcAddrMask (safeDisableModulePrevWord I) =
      safeDisableModulePrevWord I :=
    solcAddrMask_clean_left hprevCanon
  have hmoduleSlot :
      solcMappingSlot ⟨1⟩ (safeDisableModuleWord I) =
        safeDisableModuleSlotFor I := by
    rw [safeDisableModuleSlotFor_eq hcanon]
  have hprevSlot :
      solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I) =
        safeDisableModulePrevSlotFor I := by
    rw [safeDisableModulePrevSlotFor_eq hprevCanon]
  have hmoduleLoaded :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeDisableModuleWord I)) =
        safeDisableModuleStorageWord σ I := by
    unfold safeDisableModuleStorageWord
    rw [safeDisableModuleSlotFor_eq hcanon]
  have hprevLoaded :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) =
        safeDisableModulePrevStorageWord σ I := by
    unfold safeDisableModulePrevStorageWord
    rw [safeDisableModulePrevSlotFor_eq hprevCanon]
  have hmoduleLoadedRaw :
      Option.option ⟨0⟩
        (fun ac => Batteries.RBMap.findD ac.storage
          (solcMappingSlot ⟨1⟩ (safeDisableModuleWord I)) ⟨0⟩)
        (Batteries.RBMap.find? σ I.codeOwner) =
        safeDisableModuleStorageWord σ I := by
    simpa [solcSlotWord] using hmoduleLoaded
  have hprevLoadedRaw :
      Option.option ⟨0⟩
        (fun ac => Batteries.RBMap.findD ac.storage
          (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) ⟨0⟩)
        (Batteries.RBMap.find? σ I.codeOwner) =
        safeDisableModulePrevStorageWord σ I := by
    simpa [solcSlotWord] using hprevLoaded
  have hmoduleMaskedRaw :
      UInt256.land solcAddrMask
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨1⟩ (safeDisableModuleWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) =
        safeDisableModuleMaskedStorageWord σ I := by
    rw [hmoduleLoadedRaw]
    unfold safeDisableModuleMaskedStorageWord
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (safeDisableModuleStorageWord σ I)]
  have hprevStore :
      UInt256.lor
        (UInt256.land (UInt256.lnot solcAddrMask) (safeDisableModulePrevStorageWord σ I))
        (safeDisableModuleMaskedStorageWord σ I) =
        safeDisableModulePrevStoreWord σ I := by
    unfold safeDisableModulePrevStoreWord setAddressOffset0Word
      safeDisableModuleMaskedStorageWord
    rw [Reasoning.Theory.u256_land_comm (UInt256.lnot solcAddrMask)
      (safeDisableModulePrevStorageWord σ I)]
    rw [solcAddrMask_clean (solcAddrMask_result_canonical
      (safeDisableModuleStorageWord σ I))]
  have hmoduleAfterRaw :
      Option.option ⟨0⟩
        (fun ac => Batteries.RBMap.findD ac.storage
          (solcMappingSlot ⟨1⟩ (safeDisableModuleWord I)) ⟨0⟩)
        (Batteries.RBMap.find?
          (sstoreAccountMap I.codeOwner σ
            (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I))
            (safeDisableModulePrevStoreWord σ I)) I.codeOwner) =
      solcSlotWord (safeDisableModulePrevPostMap σ I) I
        (safeDisableModuleSlotFor I) := by
    simp [solcSlotWord, safeDisableModulePrevPostMap, hprevSlot, hmoduleSlot]
  have hmoduleStore :
      UInt256.land (UInt256.lnot solcAddrMask)
        (solcSlotWord (safeDisableModulePrevPostMap σ I) I
          (safeDisableModuleSlotFor I)) =
        safeDisableModuleStoreWord σ I := by
    unfold safeDisableModuleStoreWord setAddressOffset0Word
    rw [show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ from by native_decide]
    rw [Reasoning.Theory.u256_lor_zero]
    rw [Reasoning.Theory.u256_land_comm (UInt256.lnot solcAddrMask)
      (solcSlotWord (safeDisableModulePrevPostMap σ I) I (safeDisableModuleSlotFor I))]
  have hmoduleStoreRaw :
      UInt256.land (UInt256.lnot solcAddrMask)
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨1⟩ (safeDisableModuleWord I)) ⟨0⟩)
          (Batteries.RBMap.find?
            (sstoreAccountMap I.codeOwner σ
              (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I))
              (safeDisableModulePrevStoreWord σ I)) I.codeOwner)) =
        safeDisableModuleStoreWord σ I := by
    rw [hmoduleAfterRaw, hmoduleStore]
  have hmoduleHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((safeDisableModuleModuleHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (safeDisableModuleWord I) := by
    unfold safeDisableModuleModuleHashMem
    exact twoWordHashMem_solcMappingSlot ⟨1⟩ (safeDisableModuleWord I)
      (twoWordHashMem_size_96 (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem_size)
  have hprevHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((safeDisableModulePrevHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I) := by
    unfold safeDisableModulePrevHashMem safeDisableModuleModuleHashMem
      safeDisableModulePrevCheckMem twoWordHashMem
    rw [wordAt0Mem_after_wordAt32Mem_read0_64]
    · unfold solcMappingSlot
      exact mappingSlot_single (safeDisableModulePrevWord I) ⟨1⟩
    · exact wordAt0Mem_size_96 (safeDisableModuleWord I)
        (twoWordHashMem_size_96 (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem_size)
  have hmoduleHashMemSize : (safeDisableModuleModuleHashMem I).size = 96 := by
    unfold safeDisableModuleModuleHashMem
    exact twoWordHashMem_size_96 (safeDisableModuleWord I) ⟨1⟩
      (twoWordHashMem_size_96 (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem_size)
  have hprevHashMemSize : (safeDisableModulePrevHashMem I).size = 96 := by
    unfold safeDisableModulePrevHashMem
    exact wordAt0Mem_size_96 (safeDisableModulePrevWord I) hmoduleHashMemSize
  have hlogMemSize : (safeDisableModuleLogMem I).size = 96 := by
    unfold safeDisableModuleLogMem
    exact wordAt0Mem_size_96 (safeDisableModuleWord I) hprevHashMemSize
  have hlogMemRead64 :
      (safeDisableModuleLogMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold safeDisableModuleLogMem
    exact wordAt0Mem_read64 (safeDisableModuleWord I) hprevHashMemSize (by
      unfold safeDisableModulePrevHashMem
      exact wordAt0Mem_read64 (safeDisableModulePrevWord I) hmoduleHashMemSize (by
        unfold safeDisableModuleModuleHashMem
        exact twoWordHashMem_read64 (safeDisableModuleWord I) ⟨1⟩
          (twoWordHashMem_size_96 (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem_size)
          (twoWordHashMem_read64 (safeDisableModulePrevWord I) ⟨1⟩ solcFreePtrMem_size
            solcFreePtrMem_read64)))
  have rd5648 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5648' := rd5648
  rw [hmask, hcleanLeft] at rd5648'
  have rd5651 := rd5648'
    |>.push0 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd5652 := rd5651.mstore 0
    (wordAt0Mem (safeDisableModuleWord I) (safeDisableModulePrevCheckMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5657pre := rd5652
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5657 := rd5657pre.mstore 0 (safeDisableModuleModuleHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd5662pre := rd5657
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
  have rd5662 := rd5662pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (safeDisableModuleWord I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmoduleHash)
    (by native_decide) (by evm_ov)
  have rd5663 := rd5662.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5664⟩ := rd5663.sload (by native_decide) (by evm_ov)
  have rd5668 := rd5664
    |>.dup8 (by native_decide) (by evm_ov)
    |>.dup7 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5668' := rd5668
  rw [hprevCleanLeft] at rd5668'
  have rd5669pre := rd5668'.dup5 (by native_decide) (by evm_ov)
  have rd5669 := rd5669pre.mstore 0 (safeDisableModulePrevHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd5672pre := rd5669
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
  have rd5672 := rd5672pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (safeDisableModulePrevWord I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hprevHash)
    (by native_decide) (by evm_ov)
  have rd5673 := rd5672.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5674⟩ := rd5673.sload (by native_decide) (by evm_ov)
  have rd5678 := rd5674
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap7 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5678' := rd5678
  rw [hmoduleMaskedRaw] at rd5678'
  have rd5691 := rd5678'
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.not (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.lor (by native_decide) (by evm_ov)
  have rd5691' := rd5691
  rw [hmask, hprevLoadedRaw, hprevStore] at rd5691'
  have rd5693 := rd5691'
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5694⟩ := rd5693.sstore hperm (by native_decide) (by evm_ov)
  have rd5697pre := rd5694
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
  have rd5697 := rd5697pre.mstore 0 (safeDisableModuleLogMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rd5698 := rd5697.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5699⟩ := rd5698.sload (by native_decide) (by evm_ov)
  have rd5702 := rd5699
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap5 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5702' := rd5702
  rw [hmoduleStoreRaw] at rd5702'
  have rd5704 := rd5702'
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5705⟩ := rd5704.sstore hperm (by native_decide) (by evm_ov)
  have rd5707 := rd5705
    |>.swap2 (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [hlogMemSize]; decide) (by native_decide) hlogMemRead64)
      (by native_decide) (by evm_ov)
  have rd5743pre := rd5707
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pushConst safeDisableModuleDisabledTopic (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have rd5744 := RD.log2 0 (UInt256.ofNat 3) rd5743pre (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by change 4 ≤ 1024; decide)
  have rd664 := rd5744
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd665 := rd664.jumpdest (by native_decide) (by evm_ov)
  simpa [safeDisableModulePostMap, safeDisableModulePrevPostMap, hprevSlot, hmoduleSlot]
    using rd665.stop (by native_decide) (by evm_ov)

theorem safeDisableModuleBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := safeSelectorDispatchDisableModule hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 9) (by native_decide) hsel
    have hdecodeStart :
        ∃ k C, RD safeBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1390⟩
          [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ_evm) k C := by
      obtain ⟨_, _, h1377⟩ := safeReachDisableModuleBody (cA := cA) (gh := gh)
        (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
      exact safeGuardPeelOk (gt := ⟨1388⟩) h1377 hwv
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide)
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz68 : 68 ≤ I.calldata.size
      · by_cases hprevCanon : (safeDisableModulePrevWord I).toNat < EVM.addressModulus
        · by_cases hcanon : (safeDisableModuleWord I).toNat < EVM.addressModulus
          · by_cases hauth : I.source = I.codeOwner
            · by_cases hzero : safeDisableModuleWord I = ⟨0⟩
              · obtain ⟨_, _, h1390⟩ := hdecodeStart
                obtain ⟨_, _, h1403⟩ :=
                  safeDisableModuleDecodeOk h1390 hsz68 hsmall hsize hprevCanon hcanon
                have h5524 := h1403.jumpdest (by native_decide) (by evm_ov)
                  |>.push2 ⟨5524⟩ (by native_decide) (by evm_ov)
                  |>.jump (by native_decide) (by native_decide) (by evm_ov)
                obtain ⟨_, _, h5532⟩ := safeDisableModuleAuthorizedOk h5524 hauth
                exact safeReEquivExecRev hcode
                  (safeDisableModuleRequireModuleReverts_zero h5532 hzero) hdispatch
                  (safeDecode_disableModule_ok hsz68 hsmall hprevCanon hcanon)
                  (safeDisableModuleBodyReverts_zero (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) hwv hauth hzero)
              · by_cases hsent : safeDisableModuleWord I = ⟨1⟩
                · obtain ⟨_, _, h1390⟩ := hdecodeStart
                  obtain ⟨_, _, h1403⟩ :=
                    safeDisableModuleDecodeOk h1390 hsz68 hsmall hsize hprevCanon hcanon
                  have h5524 := h1403.jumpdest (by native_decide) (by evm_ov)
                    |>.push2 ⟨5524⟩ (by native_decide) (by evm_ov)
                    |>.jump (by native_decide) (by native_decide) (by evm_ov)
                  obtain ⟨_, _, h5532⟩ := safeDisableModuleAuthorizedOk h5524 hauth
                  exact safeReEquivExecRev hcode
                    (safeDisableModuleRequireModuleReverts_sentinel h5532 hsent)
                    hdispatch (safeDecode_disableModule_ok hsz68 hsmall hprevCanon hcanon)
                    (safeDisableModuleBodyReverts_sentinel (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) hwv hauth hsent)
                · by_cases hlink :
                    safeDisableModuleMaskedPrevStorageWord σ_evm I =
                      safeDisableModuleWord I
                  · have hprevWord :
                        safeDisableModulePrevStorageWord σ_evm I =
                          safeDisableModulePrevStorageWord σ_solm I :=
                      accountMapEquiv_storage_findD hAccounts I.codeOwner
                        (safeDisableModulePrevSlotFor I) ⟨0⟩
                    have hmoduleWord :
                        safeDisableModuleStorageWord σ_evm I =
                          safeDisableModuleStorageWord σ_solm I :=
                      accountMapEquiv_storage_findD hAccounts I.codeOwner
                        (safeDisableModuleSlotFor I) ⟨0⟩
                    have hlinkSolm :
                        safeDisableModuleMaskedPrevStorageWord σ_solm I =
                          safeDisableModuleWord I := by
                      unfold safeDisableModuleMaskedPrevStorageWord
                      rw [← hprevWord]
                      exact hlink
                    have hprevStoreWord :
                        safeDisableModulePrevStoreWord σ_evm I =
                          safeDisableModulePrevStoreWord σ_solm I := by
                      unfold safeDisableModulePrevStoreWord safeDisableModuleMaskedStorageWord
                      rw [hprevWord, hmoduleWord]
                    have hprevAccounts :
                        accountMapEquiv (safeDisableModulePrevPostMap σ_evm I)
                          (safeDisableModulePrevPostMap σ_solm I) := by
                      have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner
                        (safeDisableModulePrevSlotFor I)
                        (safeDisableModulePrevStoreWord σ_evm I) hAccounts
                      simpa [safeDisableModulePrevPostMap, ← hprevStoreWord] using hstore
                    have hmoduleAfterLoad :
                        solcSlotWord (safeDisableModulePrevPostMap σ_evm I) I
                            (safeDisableModuleSlotFor I) =
                          solcSlotWord (safeDisableModulePrevPostMap σ_solm I) I
                            (safeDisableModuleSlotFor I) :=
                      accountMapEquiv_storage_findD hprevAccounts I.codeOwner
                        (safeDisableModuleSlotFor I) ⟨0⟩
                    have hstoreWord :
                        safeDisableModuleStoreWord σ_evm I =
                          safeDisableModuleStoreWord σ_solm I := by
                      unfold safeDisableModuleStoreWord
                      rw [hmoduleAfterLoad]
                    have hpostAccounts :
                        accountMapEquiv (safeDisableModulePostMap σ_evm I)
                          (safeDisableModulePostMap σ_solm I) := by
                      have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner
                        (safeDisableModuleSlotFor I) (safeDisableModuleStoreWord σ_evm I)
                        hprevAccounts
                      simpa [safeDisableModulePostMap, ← hstoreWord] using hstore
                    have hbody := safeDisableModuleBodyReturns (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) hwv hauth hcanon hzero hsent hlinkSolm
                    have hcreated :
                        (cA, safeDisableModulePostMap σ_evm I).1 =
                          (safeDisableModulePostState
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            I).createdAccounts := by
                      simp [safeDisableModulePostState, safeDisableModulePrevPostState,
                        initState, storageStore_createdAccounts]
                    have haccounts :
                        accountMapEquiv (cA, safeDisableModulePostMap σ_evm I).2
                          (safeDisableModulePostState
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            I).accountMap := by
                      simpa [safeDisableModulePostMap, safeDisableModulePrevPostMap,
                        safeDisableModulePostState, safeDisableModulePrevPostState,
                        safeDisableModuleStoreWord, safeDisableModulePrevStoreWord,
                        safeDisableModuleStorageWord, safeDisableModulePrevStorageWord,
                        safeDisableModuleMaskedStorageWord, initState,
                        storageStore_accountMap, storageStore_executionEnv,
                        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                        solcSlotWord] using hpostAccounts
                    have henc : returnEquiv ByteArray.empty none
                        disablemoduleTransition.returnType := by
                      rw [show disablemoduleTransition.returnType = [] by rfl]
                      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
                    obtain ⟨_, _, h1390⟩ := hdecodeStart
                    obtain ⟨_, _, h1403⟩ :=
                      safeDisableModuleDecodeOk h1390 hsz68 hsmall hsize hprevCanon hcanon
                    have h5524 := h1403.jumpdest (by native_decide) (by evm_ov)
                      |>.push2 ⟨5524⟩ (by native_decide) (by evm_ov)
                      |>.jump (by native_decide) (by native_decide) (by evm_ov)
                    obtain ⟨_, _, h5532⟩ := safeDisableModuleAuthorizedOk h5524 hauth
                    obtain ⟨_, _, h5585⟩ :=
                      safeDisableModuleRequireModuleOk h5532 hcanon hzero hsent
                    obtain ⟨_, _, h5637⟩ :=
                      safeDisableModuleRequireLinkOk h5585 hprevCanon hcanon hlink
                    exact safeReEquivExecGen hcode
                      (safeDisableModuleStoreLog h5637 hperm hprevCanon hcanon) hdispatch
                      (safeDecode_disableModule_ok hsz68 hsmall hprevCanon hcanon)
                      hbody hcreated haccounts henc
                  · have hprevWord :
                        safeDisableModulePrevStorageWord σ_evm I =
                          safeDisableModulePrevStorageWord σ_solm I :=
                      accountMapEquiv_storage_findD hAccounts I.codeOwner
                        (safeDisableModulePrevSlotFor I) ⟨0⟩
                    have hlinkSolm :
                        safeDisableModuleMaskedPrevStorageWord σ_solm I ≠
                          safeDisableModuleWord I := by
                      unfold safeDisableModuleMaskedPrevStorageWord
                      rw [← hprevWord]
                      exact hlink
                    obtain ⟨_, _, h1390⟩ := hdecodeStart
                    obtain ⟨_, _, h1403⟩ :=
                      safeDisableModuleDecodeOk h1390 hsz68 hsmall hsize hprevCanon hcanon
                    have h5524 := h1403.jumpdest (by native_decide) (by evm_ov)
                      |>.push2 ⟨5524⟩ (by native_decide) (by evm_ov)
                      |>.jump (by native_decide) (by native_decide) (by evm_ov)
                    obtain ⟨_, _, h5532⟩ := safeDisableModuleAuthorizedOk h5524 hauth
                    obtain ⟨_, _, h5585⟩ :=
                      safeDisableModuleRequireModuleOk h5532 hcanon hzero hsent
                    exact safeReEquivExecRev hcode
                      (safeDisableModuleRequireLinkReverts h5585 hprevCanon hcanon hlink)
                      hdispatch (safeDecode_disableModule_ok hsz68 hsmall hprevCanon hcanon)
                      (safeDisableModuleBodyReverts_unlinked (cA := cA) (gh := gh)
                        (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) hwv hauth hcanon hzero hsent
                        hlinkSolm)
            · obtain ⟨_, _, h1390⟩ := hdecodeStart
              obtain ⟨_, _, h1403⟩ :=
                safeDisableModuleDecodeOk h1390 hsz68 hsmall hsize hprevCanon hcanon
              have h5524 := h1403.jumpdest (by native_decide) (by evm_ov)
                |>.push2 ⟨5524⟩ (by native_decide) (by evm_ov)
                |>.jump (by native_decide) (by native_decide) (by evm_ov)
              exact safeReEquivExecRev hcode
                (safeDisableModuleAuthorizedReverts h5524 hauth) hdispatch
                (safeDecode_disableModule_ok hsz68 hsmall hprevCanon hcanon)
                (safeDisableModuleBodyReverts_auth (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hwv hauth)
          · obtain ⟨_, _, h1390⟩ := hdecodeStart
            exact safeReEquivDecodeFailed hcode
              (safeDisableModuleDecodeReverts_noncanon_module h1390 hsz68 hsmall hsize
                hprevCanon hcanon)
              hdispatch (safeDecode_disableModule_none_noncanon_module hsz68 hsmall
                hprevCanon hcanon)
        · obtain ⟨_, _, h1390⟩ := hdecodeStart
          exact safeReEquivDecodeFailed hcode
            (safeDisableModuleDecodeReverts_noncanon_prev h1390 hsz68 hsmall hsize
              hprevCanon)
            hdispatch (safeDecode_disableModule_none_noncanon_prev hsz68 hsmall hprevCanon)
      · obtain ⟨_, _, h1390⟩ := hdecodeStart
        have hlt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
              ⟨1⟩ :=
          solcDecodeLenCheckShort_4_64 hsz4 (by omega) hsize
        exact safeReEquivDecodeFailed hcode (safeDisableModuleDecodeReverts_len h1390 hlt)
          hdispatch (safeDecode_disableModule_none_short hsz4 (by omega))
    · obtain ⟨_, _, h1390⟩ := hdecodeStart
      have hlt :
          UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
            ⟨1⟩ :=
        solcDecodeLenCheckHuge_4_64 (by omega) hsize
      exact safeReEquivDecodeFailed hcode (safeDisableModuleDecodeReverts_len h1390 hlt)
        hdispatch (safeDecode_disableModule_none_huge (by omega))
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 9) (by native_decide) hsel
    obtain ⟨_, _, h1377⟩ := safeReachDisableModuleBody (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1388⟩) h1377 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev hdispatch
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
