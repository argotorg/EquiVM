import Benchmarks.Safe.Routines

/-! # Safe `isModuleEnabled(address)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeIsModuleEnabledWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeIsModuleEnabledValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeIsModuleEnabledWord I).toNat)

abbrev safeIsModuleEnabledLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "module" (safeIsModuleEnabledValue I)

theorem safeIsModuleEnabledLocals_index_module (I : ExecutionEnv) :
    (safeIsModuleEnabledLocals I)["module"] = safeIsModuleEnabledValue I := by
  unfold safeIsModuleEnabledLocals
  rw [Std.HashMap.getElem_insert]
  simp

abbrev safeIsModuleEnabledKeyValue (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (safeIsModuleEnabledWord I).toNat)

abbrev safeIsModuleEnabledEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "modules", steps := [.mindex (safeIsModuleEnabledKeyValue I)] }

abbrev safeIsModuleEnabledSlotFor (I : ExecutionEnv) : UInt256 :=
  modulesSlot (safeIsModuleEnabledKeyValue I)

def safeIsModuleEnabledStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeIsModuleEnabledSlotFor I)

abbrev safeIsModuleEnabledMaskedStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (safeIsModuleEnabledStorageWord σ I) solcAddrMask

def safeIsModuleEnabledReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if safeIsModuleEnabledWord I = ⟨1⟩ then ⟨0⟩
  else UInt256.isZero (UInt256.isZero (safeIsModuleEnabledMaskedStorageWord σ I))

def safeIsModuleEnabledReturnValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  if safeIsModuleEnabledWord I = ⟨1⟩ then .bool false
  else if safeIsModuleEnabledMaskedStorageWord σ I = ⟨0⟩ then .bool false else .bool true

theorem safeIsModuleEnabledReturnEncoding (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValue? boolTy (safeIsModuleEnabledReturnValue σ I) =
      some (UInt256.toByteArray (safeIsModuleEnabledReturnWord σ I)) := by
  unfold safeIsModuleEnabledReturnValue safeIsModuleEnabledReturnWord
  by_cases hsent : safeIsModuleEnabledWord I = ⟨1⟩
  · simp [hsent]
    simpa [boolTy] using boolFalseReturnEncoding
  · simp [hsent]
    by_cases hzero : safeIsModuleEnabledMaskedStorageWord σ I = ⟨0⟩
    · have hnorm :
          UInt256.isZero (UInt256.isZero (safeIsModuleEnabledMaskedStorageWord σ I)) =
            ⟨0⟩ := by
        rw [hzero]
        decide
      simp [hzero]
      simpa [boolTy] using boolFalseReturnEncoding
    · have hiz : UInt256.isZero (safeIsModuleEnabledMaskedStorageWord σ I) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hzero
      have hnorm :
          UInt256.isZero (UInt256.isZero (safeIsModuleEnabledMaskedStorageWord σ I)) =
            ⟨1⟩ := by
        rw [hiz]
        decide
      simp [hzero, hnorm]
      simpa [boolTy] using boolTrueReturnEncoding

theorem safeIsModuleEnabledKeyValue_eq {I : ExecutionEnv}
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus) :
    keyValueToWord (safeIsModuleEnabledKeyValue I) = safeIsModuleEnabledWord I :=
  keyValueToWord_address_of_canonical (safeIsModuleEnabledWord I) hcanon

theorem safeIsModuleEnabledSlotFor_eq {I : ExecutionEnv}
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus) :
    safeIsModuleEnabledSlotFor I = solcMappingSlot ⟨1⟩ (safeIsModuleEnabledWord I) := by
  unfold safeIsModuleEnabledSlotFor modulesSlot mapSlot solcMappingSlot
  rw [safeIsModuleEnabledKeyValue_eq hcanon]

theorem safeIsModuleEnabledAccountAddress_ofNat_zero_iff {w : UInt256}
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

theorem safeIsModuleEnabledAccountAddress_ofNat_one_iff {w : UInt256}
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

theorem safeDecode_isModuleEnabled_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (ismoduleenabledTransition.params.map Param.name)
      (transitionSignature ismoduleenabledTransition).paramTypes I.calldata =
        some (safeIsModuleEnabledLocals I) := by
  simpa [config, safeDecodeMode, ismoduleenabledTransition, safeIsModuleEnabledLocals,
    safeIsModuleEnabledValue, safeIsModuleEnabledWord, addr] using
      (decodeCalldata_address_ok (cd := I.calldata) (x := "module")
        hsz36 hsmall hcanon)

theorem safeDecode_isModuleEnabled_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (ismoduleenabledTransition.params.map Param.name)
      (transitionSignature ismoduleenabledTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, ismoduleenabledTransition, addr] using
    (decodeCalldata_address_none_short (cd := I.calldata) (x := "module") hsz4 hshort)

theorem safeDecode_isModuleEnabled_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (ismoduleenabledTransition.params.map Param.name)
      (transitionSignature ismoduleenabledTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, ismoduleenabledTransition, addr] using
    (decodeCalldata_address_none_huge (cd := I.calldata) (x := "module") hbig)

theorem safeDecode_isModuleEnabled_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeIsModuleEnabledWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (ismoduleenabledTransition.params.map Param.name)
      (transitionSignature ismoduleenabledTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, ismoduleenabledTransition, safeIsModuleEnabledWord, addr] using
    (decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "module")
      hsz36 hsmall hnc)

theorem safeIsModuleEnabledStorageEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeIsModuleEnabledLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (modulesRef (.var "module"))) =
      .ok (.address (AccountAddress.ofNat (safeIsModuleEnabledMaskedStorageWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeIsModuleEnabledLocals I })
    (slot := modulesRef (.var "module"))
    (er := safeIsModuleEnabledEvaledRef I)
    (t := .address)
    (loc := addrLoc (safeIsModuleEnabledSlotFor I))
    (value := .address
      (AccountAddress.ofNat (safeIsModuleEnabledMaskedStorageWord σ I).toNat))
    (hbase := by simp [modulesRef, safeIsModuleEnabledLocals])
    (her := by
      simp [safeIsModuleEnabledEvaledRef, safeIsModuleEnabledKeyValue,
        safeIsModuleEnabledValue, safeIsModuleEnabledLocals, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, modulesRef, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [safeIsModuleEnabledMaskedStorageWord, safeIsModuleEnabledStorageWord, addrLoc,
        addressOffset0Loc] using
        storageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeIsModuleEnabledSlotFor I))]

theorem safeIsModuleEnabledDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨741⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨754⟩
      [safeIsModuleEnabledWord I, ⟨759⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have h9591 := h.push2 ⟨759⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨754⟩ (by native_decide) (by evm_ov)
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
        safeIsModuleEnabledWord I from rfl,
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
    simpa [safeIsModuleEnabledWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using h6897.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeIsModuleEnabledDecodeReverts_len {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨741⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9591 := h.push2 ⟨759⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨754⟩ (by native_decide) (by evm_ov)
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

theorem safeIsModuleEnabledDecodeReverts_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨741⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (safeIsModuleEnabledWord I).toNat < EVM.addressModulus) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have heqZero :
      UInt256.eq (safeIsModuleEnabledWord I)
        (UInt256.land (safeIsModuleEnabledWord I) solcAddrMask) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnc (solcAddrCanonical_of_clean heq)
  have h9591 := h.push2 ⟨759⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨754⟩ (by native_decide) (by evm_ov)
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
        safeIsModuleEnabledWord I from rfl,
    heqZero] at h9088'
  have h9093 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9093.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeIsModuleEnabled_isZero_isZero_idem (w : UInt256) :
    UInt256.isZero (UInt256.isZero (UInt256.isZero (UInt256.isZero w))) =
      UInt256.isZero (UInt256.isZero w) := by
  by_cases hz : w = ⟨0⟩
  · rw [hz]
    decide
  · have hiz : UInt256.isZero w = ⟨0⟩ := isZero_eq_zero_of_ne hz
    rw [hiz]
    decide

theorem safeIsModuleEnabledHelperSentinel {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {k C : ℕ} {module sel : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD safeBytecode ee g s0 ⟨754⟩ [module, ⟨759⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsent : module = ⟨1⟩) :
    RDret safeBytecode g s0 (cA, σ) (UInt256.toByteArray ⟨0⟩) := by
  have h2802 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨2802⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h2823 := h2802.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.push2 ⟨2853⟩ (by native_decide) (by evm_ov)
  have h2823' := h2823
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hsent, hmask,
    show UInt256.land (⟨1⟩ : UInt256) solcAddrMask = ⟨1⟩ from by native_decide,
    show UInt256.eq (⟨1⟩ : UInt256) ⟨1⟩ = ⟨1⟩ from by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2823'
  have h2853 := h2823'.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h759 := h2853.jumpdest (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have hret := RD.safeReturnBoolFromScratchMem759 (val := (⟨0⟩ : UInt256)) (R := [sel])
    h759 solcFreePtrMem_size solcFreePtrMem_read64 (by simp)
  simpa using hret

theorem safeIsModuleEnabledHelperNonSentinel {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {k C : ℕ} {module sel : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD safeBytecode ee g s0 ⟨754⟩ [module, ⟨759⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanon : module.toNat < EVM.addressModulus) (hnot : module ≠ ⟨1⟩) :
    RDret safeBytecode g s0 (cA, σ)
      (UInt256.toByteArray
        (UInt256.isZero
          (UInt256.isZero
            (UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ module)) solcAddrMask)))) := by
  have h2802 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨2802⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h2823 := h2802.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.push2 ⟨2853⟩ (by native_decide) (by evm_ov)
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hmoduleMask :
      UInt256.land module (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) = module := by
    rw [hmask]
    exact solcAddrMask_clean hcanon
  have heqZero : UInt256.eq module ⟨1⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnot (uInt256_eq_one_eq heq)
  have h2823' := h2823
  rw [hmoduleMask, heqZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2823'
  have h2824 := h2823'.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have h2835 := h2824.pop (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have h2835' := h2835
  have hmaskModuleLeft :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) module = module := by
    rw [hmask]
    exact solcAddrMask_clean_left hcanon
  rw [hmaskModuleLeft] at h2835'
  have h2838pre := h2835'
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have h2839 := h2838pre.mstore 0 (wordAt0Mem module solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have h2843pre := h2839
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have h2844 := h2843pre.mstore 0 (twoWordHashMem module ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have h2848pre := h2844
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ module solcFreePtrMem_size
  have h2849 := h2848pre.keccak256 0 (solcMappingSlot ⟨1⟩ module)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, h2850⟩ := h2849.sload (by native_decide) (by evm_ov)
  have h2851 := h2850.and (by native_decide) (by evm_ov)
  have h2851' := h2851
  rw [hmask] at h2851'
  have h2853 := h2851'
    |>.iszero (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  have h759 := h2853.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have hret := RD.safeReturnBoolFromScratchMem759
    (val := UInt256.isZero
      (UInt256.isZero
        (UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ module)) solcAddrMask)))
    (R := [sel]) h759
    (twoWordHashMem_size_96 module ⟨1⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 module ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp)
  simpa [safeIsModuleEnabled_isZero_isZero_idem] using hret

theorem safeIsModuleEnabledX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 20)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (safeIsModuleEnabledReturnWord σ I)) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h728⟩ := safeReachIsModuleEnabledBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h741⟩ := safeGuardPeelOk (gt := ⟨739⟩) h728 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h754⟩ := safeIsModuleEnabledDecodeOk h741 hsz36 hsmall hsize hcanon
  by_cases hsent : safeIsModuleEnabledWord I = ⟨1⟩
  · have hret := safeIsModuleEnabledHelperSentinel h754 hsent
    simpa [safeIsModuleEnabledReturnWord, hsent] using hret
  · have hret := safeIsModuleEnabledHelperNonSentinel h754 hcanon hsent
    have hword :
        solcSlotWord σ I (solcMappingSlot ⟨1⟩ (safeIsModuleEnabledWord I)) =
          safeIsModuleEnabledStorageWord σ I := by
      unfold safeIsModuleEnabledStorageWord
      rw [safeIsModuleEnabledSlotFor_eq hcanon]
    simpa [safeIsModuleEnabledReturnWord, hsent, safeIsModuleEnabledMaskedStorageWord,
      hword] using hret

theorem safeIsModuleEnabledStorageNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeIsModuleEnabledMaskedStorageWord σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeIsModuleEnabledLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.storage (modulesRef (.var "module"))) zeroAddr) =
      .ok (.bool false) := by
  have hstorage := safeIsModuleEnabledStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddr :
      AccountAddress.ofNat (safeIsModuleEnabledMaskedStorageWord σ I).toNat =
        AccountAddress.ofNat 0 := by
    rw [hzero]
    rfl
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeIsModuleEnabledMaskedStorageWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = true := by
    simp [BEq.beq, hstorageAddr]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeIsModuleEnabledStorageNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeIsModuleEnabledMaskedStorageWord σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeIsModuleEnabledLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.storage (modulesRef (.var "module"))) zeroAddr) =
      .ok (.bool true) := by
  have hstorage := safeIsModuleEnabledStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddrNe :
      AccountAddress.ofNat (safeIsModuleEnabledMaskedStorageWord σ I).toNat ≠
        AccountAddress.ofNat 0 := by
    intro haddr
    exact hzero ((safeIsModuleEnabledAccountAddress_ofNat_zero_iff
      (solcAddrMask_result_canonical (safeIsModuleEnabledStorageWord σ I))).mp haddr)
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeIsModuleEnabledMaskedStorageWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false := by
    simp [BEq.beq, hstorageAddrNe]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeIsModuleEnabledModuleNeSentinel_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsent : safeIsModuleEnabledWord I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeIsModuleEnabledLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") sentinelAddr) =
      .ok (.bool false) := by
  have hmoduleAddr :
      AccountAddress.ofNat (safeIsModuleEnabledWord I).toNat = AccountAddress.ofNat 1 := by
    rw [hsent]
    rfl
  have hmoduleBeq :
      (safeIsModuleEnabledValue I == Value.address (AccountAddress.ofNat 1)) = true := by
    simp [safeIsModuleEnabledValue, BEq.beq, hmoduleAddr]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeIsModuleEnabledLocals, safeIsModuleEnabledValue,
    hmoduleBeq]

theorem safeIsModuleEnabledModuleNeSentinel_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus)
    (hsent : safeIsModuleEnabledWord I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeIsModuleEnabledLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "module") sentinelAddr) =
      .ok (.bool true) := by
  have hmoduleAddrNe :
      AccountAddress.ofNat (safeIsModuleEnabledWord I).toNat ≠ AccountAddress.ofNat 1 := by
    intro haddr
    exact hsent ((safeIsModuleEnabledAccountAddress_ofNat_one_iff hcanon).mp haddr)
  have hmoduleBeq :
      (safeIsModuleEnabledValue I == Value.address (AccountAddress.ofNat 1)) = false := by
    simp [safeIsModuleEnabledValue, BEq.beq, hmoduleAddrNe]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeIsModuleEnabledLocals, safeIsModuleEnabledValue,
    hmoduleBeq]

theorem safeIsModuleEnabledBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeIsModuleEnabledLocals I) ismoduleenabledTransition.body
      (.returned { contract := contract, locals := safeIsModuleEnabledLocals I }
        (initState cA gh bl σ σ₀ g A I)
        (some [safeIsModuleEnabledReturnValue σ I])) := by
  refine nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (by simp only [initState]; exact hwv) ?_
  by_cases hsent : safeIsModuleEnabledWord I = ⟨1⟩
  · by_cases hzero : safeIsModuleEnabledMaskedStorageWord σ I = ⟨0⟩
    · have hleft := safeIsModuleEnabledStorageNeZero_false (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      unfold moduleEnabledExpr andE
      simp [evalExpr?, hleft, safeIsModuleEnabledReturnValue, hsent,
        EvalResult.bind, bind, pure]
    · have hleft := safeIsModuleEnabledStorageNeZero_true (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      have hright := safeIsModuleEnabledModuleNeSentinel_false (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsent
      unfold moduleEnabledExpr andE
      simp [evalExpr?, hleft, hright, safeIsModuleEnabledReturnValue, hsent,
        EvalResult.bind, bind, pure]
  · by_cases hzero : safeIsModuleEnabledMaskedStorageWord σ I = ⟨0⟩
    · have hleft := safeIsModuleEnabledStorageNeZero_false (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      unfold moduleEnabledExpr andE
      simp [evalExpr?, hleft, safeIsModuleEnabledReturnValue, hsent, hzero,
        EvalResult.bind, bind, pure]
    · have hleft := safeIsModuleEnabledStorageNeZero_true (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      have hright := safeIsModuleEnabledModuleNeSentinel_true (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hsent
      unfold moduleEnabledExpr andE
      simp [evalExpr?, hleft, hright, safeIsModuleEnabledReturnValue, hsent, hzero,
        EvalResult.bind, bind, pure]

theorem safeIsModuleEnabledBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 20))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword :
      safeIsModuleEnabledStorageWord σ_evm I =
        safeIsModuleEnabledStorageWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeIsModuleEnabledSlotFor I) ⟨0⟩
  have hretVal :
      safeIsModuleEnabledReturnValue σ_solm I =
        safeIsModuleEnabledReturnValue σ_evm I := by
    unfold safeIsModuleEnabledReturnValue safeIsModuleEnabledMaskedStorageWord
    rw [← hword]
  exact safeReEquivExecTransport hcode
    (safeIsModuleEnabledX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hsmall hsize
      hcanon hsel)
    (safeSelectorDispatchIsModuleEnabled hsel)
    (safeDecode_isModuleEnabled_ok hsz36 hsmall hcanon)
    (safeIsModuleEnabledBodyReturns hwv hcanon) (by rw [hretVal])
    hAccounts
    (returnEquiv_of_encode (safeIsModuleEnabledReturnEncoding σ_evm I))

theorem safeIsModuleEnabledBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) (hsel : selIs I (safeSelBytes 20)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h728⟩ := safeReachIsModuleEnabledBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h741⟩ := safeGuardPeelOk (gt := ⟨739⟩) h728 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode (safeIsModuleEnabledDecodeReverts_len h741 hlt)
    (safeSelectorDispatchIsModuleEnabled hsel)
    (safeDecode_isModuleEnabled_none_short hsz4 hshort)

theorem safeIsModuleEnabledBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 20)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h728⟩ := safeReachIsModuleEnabledBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h741⟩ := safeGuardPeelOk (gt := ⟨739⟩) h728 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact safeReEquivDecodeFailed hcode (safeIsModuleEnabledDecodeReverts_len h741 hlt)
    (safeSelectorDispatchIsModuleEnabled hsel)
    (safeDecode_isModuleEnabled_none_huge hbig)

theorem safeIsModuleEnabledBodyCoreDecodeFailed_noncanon
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeIsModuleEnabledWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 20)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h728⟩ := safeReachIsModuleEnabledBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h741⟩ := safeGuardPeelOk (gt := ⟨739⟩) h728 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  exact safeReEquivDecodeFailed hcode
    (safeIsModuleEnabledDecodeReverts_noncanon h741 hsz36 hsmall hsize hnc)
    (safeSelectorDispatchIsModuleEnabled hsel)
    (safeDecode_isModuleEnabled_none_noncanon hsz36 hsmall hnc)

theorem safeIsModuleEnabledBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 20))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 20) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases hcanon : (safeIsModuleEnabledWord I).toNat < EVM.addressModulus
        · exact safeIsModuleEnabledBodyCoreOk hcode hsize hwv hsz36 hsmall hcanon hsel
            hAccounts
        · exact safeIsModuleEnabledBodyCoreDecodeFailed_noncanon hcode hsize hwv hsz36
            hsmall hcanon hsel
      · exact safeIsModuleEnabledBodyCoreDecodeFailed_short hcode hsize hwv hsz4 (by omega)
          hsel
    · exact safeIsModuleEnabledBodyCoreDecodeFailed_huge hcode hsize hwv hsz4 (by omega) hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 20) (by native_decide) hsel
    obtain ⟨_, _, h728⟩ := safeReachIsModuleEnabledBody (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨739⟩) h728 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchIsModuleEnabled hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
