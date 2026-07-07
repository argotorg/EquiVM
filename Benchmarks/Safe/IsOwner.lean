import Benchmarks.Safe.Routines

/-! # Safe `isOwner(address)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeIsOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeIsOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeIsOwnerWord I).toNat)

abbrev safeIsOwnerLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (safeIsOwnerValue I)

theorem safeIsOwnerLocals_index_owner (I : ExecutionEnv) :
    (safeIsOwnerLocals I)["owner"] = safeIsOwnerValue I := by
  unfold safeIsOwnerLocals
  rw [Std.HashMap.getElem_insert]
  simp

abbrev safeIsOwnerKeyValue (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (safeIsOwnerWord I).toNat)

abbrev safeIsOwnerEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "owners", steps := [.mindex (safeIsOwnerKeyValue I)] }

abbrev safeIsOwnerSlotFor (I : ExecutionEnv) : UInt256 :=
  ownersSlot (safeIsOwnerKeyValue I)

def safeIsOwnerStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeIsOwnerSlotFor I)

abbrev safeIsOwnerMaskedStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (safeIsOwnerStorageWord σ I) solcAddrMask

def safeIsOwnerReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if safeIsOwnerWord I = ⟨1⟩ then ⟨0⟩
  else UInt256.isZero (UInt256.isZero (safeIsOwnerMaskedStorageWord σ I))

def safeIsOwnerReturnValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  if safeIsOwnerWord I = ⟨1⟩ then .bool false
  else if safeIsOwnerMaskedStorageWord σ I = ⟨0⟩ then .bool false else .bool true

theorem safeIsOwnerReturnEncoding (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValue? boolTy (safeIsOwnerReturnValue σ I) =
      some (UInt256.toByteArray (safeIsOwnerReturnWord σ I)) := by
  unfold safeIsOwnerReturnValue safeIsOwnerReturnWord
  by_cases hsent : safeIsOwnerWord I = ⟨1⟩
  · simp [hsent]
    simpa [boolTy] using boolFalseReturnEncoding
  · simp [hsent]
    by_cases hzero : safeIsOwnerMaskedStorageWord σ I = ⟨0⟩
    · have hnorm :
          UInt256.isZero (UInt256.isZero (safeIsOwnerMaskedStorageWord σ I)) = ⟨0⟩ := by
        rw [hzero]
        decide
      simp [hzero]
      simpa [boolTy] using boolFalseReturnEncoding
    · have hiz :
          UInt256.isZero (safeIsOwnerMaskedStorageWord σ I) = ⟨0⟩ :=
        isZero_eq_zero_of_ne hzero
      have hnorm :
          UInt256.isZero (UInt256.isZero (safeIsOwnerMaskedStorageWord σ I)) = ⟨1⟩ := by
        rw [hiz]
        decide
      simp [hzero, hnorm]
      simpa [boolTy] using boolTrueReturnEncoding

theorem safeIsOwnerKeyValue_eq {I : ExecutionEnv}
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus) :
    keyValueToWord (safeIsOwnerKeyValue I) = safeIsOwnerWord I :=
  keyValueToWord_address_of_canonical (safeIsOwnerWord I) hcanon

theorem safeIsOwnerSlotFor_eq {I : ExecutionEnv}
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus) :
    safeIsOwnerSlotFor I = solcMappingSlot ⟨2⟩ (safeIsOwnerWord I) := by
  unfold safeIsOwnerSlotFor ownersSlot mapSlot solcMappingSlot
  rw [safeIsOwnerKeyValue_eq hcanon]

theorem safeAccountAddress_ofNat_zero_iff {w : UInt256}
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

theorem safeAccountAddress_ofNat_one_iff {w : UInt256}
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

theorem safeDecode_isOwner_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (isownerTransition.params.map Param.name)
      (transitionSignature isownerTransition).paramTypes I.calldata =
        some (safeIsOwnerLocals I) := by
  simpa [config, safeDecodeMode, isownerTransition, safeIsOwnerLocals, safeIsOwnerValue,
    safeIsOwnerWord, addr] using
      (decodeCalldata_address_ok (cd := I.calldata) (x := "owner")
        hsz36 hsmall hcanon)

theorem safeDecode_isOwner_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (isownerTransition.params.map Param.name)
      (transitionSignature isownerTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, isownerTransition, addr] using
    (decodeCalldata_address_none_short (cd := I.calldata) (x := "owner") hsz4 hshort)

theorem safeDecode_isOwner_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (isownerTransition.params.map Param.name)
      (transitionSignature isownerTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, isownerTransition, addr] using
    (decodeCalldata_address_none_huge (cd := I.calldata) (x := "owner") hbig)

theorem safeDecode_isOwner_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeIsOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (isownerTransition.params.map Param.name)
      (transitionSignature isownerTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, isownerTransition, safeIsOwnerWord, addr] using
    (decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "owner")
      hsz36 hsmall hnc)

theorem safeIsOwnerStorageEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeIsOwnerLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (ownersRef (.var "owner"))) =
      .ok (.address (AccountAddress.ofNat (safeIsOwnerMaskedStorageWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeIsOwnerLocals I })
    (slot := ownersRef (.var "owner"))
    (er := safeIsOwnerEvaledRef I)
    (t := .address)
    (loc := addrLoc (safeIsOwnerSlotFor I))
    (value := .address (AccountAddress.ofNat (safeIsOwnerMaskedStorageWord σ I).toNat))
    (hbase := by simp [ownersRef, safeIsOwnerLocals])
    (her := by
      simp [safeIsOwnerEvaledRef, safeIsOwnerKeyValue, safeIsOwnerValue,
        safeIsOwnerLocals, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ownersRef, evalExpr?, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [safeIsOwnerMaskedStorageWord, safeIsOwnerStorageWord, addrLoc,
        addressOffset0Loc] using
        storageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeIsOwnerSlotFor I))]

theorem safeIsOwnerDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨793⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩
      [safeIsOwnerWord I, ⟨759⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have h9591 := h.push2 ⟨759⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨806⟩ (by native_decide) (by evm_ov)
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
        safeIsOwnerWord I from rfl,
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
    simpa [safeIsOwnerWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using h6897.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeIsOwnerDecodeReverts_len {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨793⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9591 := h.push2 ⟨759⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨806⟩ (by native_decide) (by evm_ov)
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

theorem safeIsOwnerDecodeReverts_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨793⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (safeIsOwnerWord I).toNat < EVM.addressModulus) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have heqZero :
      UInt256.eq (safeIsOwnerWord I)
        (UInt256.land (safeIsOwnerWord I) solcAddrMask) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnc (solcAddrCanonical_of_clean heq)
  have h9591 := h.push2 ⟨759⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨806⟩ (by native_decide) (by evm_ov)
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
        safeIsOwnerWord I from rfl,
    heqZero] at h9088'
  have h9093 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9093.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem uInt256_isZero_isZero_idem (w : UInt256) :
    UInt256.isZero (UInt256.isZero (UInt256.isZero (UInt256.isZero w))) =
      UInt256.isZero (UInt256.isZero w) := by
  by_cases hz : w = ⟨0⟩
  · rw [hz]
    decide
  · have hiz : UInt256.isZero w = ⟨0⟩ := isZero_eq_zero_of_ne hz
    rw [hiz]
    decide

theorem safeIsOwnerHelperSentinel {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {owner sel : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD safeBytecode ee g s0 ⟨806⟩ [owner, ⟨759⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsent : owner = ⟨1⟩) :
    RDret safeBytecode g s0 (cA, σ) (UInt256.toByteArray ⟨0⟩) := by
  have h2859 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨2859⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h2874 := h2859.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨2907⟩ (by native_decide) (by evm_ov)
  have h2874' := h2874
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hsent, hmask,
    show UInt256.land (⟨1⟩ : UInt256) solcAddrMask = ⟨1⟩ from by native_decide,
    show UInt256.eq (⟨1⟩ : UInt256) ⟨1⟩ = ⟨1⟩ from by decide] at h2874'
  have h2907 := h2874'.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h2908 := h2907.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2908
  have h759 := h2908.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have hret := RD.safeReturnBoolFromScratchMem759 (val := (⟨0⟩ : UInt256)) (R := [sel])
    h759 solcFreePtrMem_size solcFreePtrMem_read64 (by simp)
  simpa using hret

theorem safeIsOwnerHelperNonSentinel {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {owner sel : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD safeBytecode ee g s0 ⟨806⟩ [owner, ⟨759⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanon : owner.toNat < EVM.addressModulus) (hnot : owner ≠ ⟨1⟩) :
    RDret safeBytecode g s0 (cA, σ)
      (UInt256.toByteArray
        (UInt256.isZero
          (UInt256.isZero
            (UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨2⟩ owner)) solcAddrMask)))) := by
  have h2859 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨2859⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h2874 := h2859.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push2 ⟨2907⟩ (by native_decide) (by evm_ov)
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hownerMask :
      UInt256.land owner (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) = owner := by
    rw [hmask]
    exact solcAddrMask_clean hcanon
  have heqZero : UInt256.eq (⟨1⟩ : UInt256) owner = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnot (uInt256_eq_one_eq heq).symm
  have h2874' := h2874
  rw [hownerMask, heqZero] at h2874'
  have h2879 := h2874'.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have h2880 := h2879.pop (by native_decide) (by evm_ov)
  have h2890 := h2880
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have h2890' := h2890
  have hmaskOwnerLeft :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) owner = owner := by
    rw [hmask]
    exact solcAddrMask_clean_left hcanon
  rw [hmaskOwnerLeft] at h2890'
  have h2894pre := h2890'
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have h2895 := h2894pre.mstore 0 (wordAt0Mem owner solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have h2899pre := h2895
    |>.push1 ⟨2⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have h2900 := h2899pre.mstore 0 (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have h2903pre := h2900
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨2⟩ owner solcFreePtrMem_size
  have h2904 := h2903pre.keccak256 0 (solcMappingSlot ⟨2⟩ owner)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, h2905⟩ := h2904.sload (by native_decide) (by evm_ov)
  have h2906 := h2905.and (by native_decide) (by evm_ov)
  have h2906' := h2906
  rw [hmask] at h2906'
  have h2908 := h2906'
    |>.iszero (by native_decide) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
  have h759 := h2908.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have hret := RD.safeReturnBoolFromScratchMem759
    (val := UInt256.isZero
      (UInt256.isZero
        (UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨2⟩ owner)) solcAddrMask)))
    (R := [sel]) h759
    (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 owner ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp)
  simpa [uInt256_isZero_isZero_idem] using hret

theorem safeIsOwnerX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 21)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (safeIsOwnerReturnWord σ I)) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h780⟩ := safeReachIsOwnerBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h793⟩ := safeGuardPeelOk (gt := ⟨791⟩) h780 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h806⟩ := safeIsOwnerDecodeOk h793 hsz36 hsmall hsize hcanon
  by_cases hsent : safeIsOwnerWord I = ⟨1⟩
  · have hret := safeIsOwnerHelperSentinel h806 hsent
    simpa [safeIsOwnerReturnWord, hsent] using hret
  · have hret := safeIsOwnerHelperNonSentinel h806 hcanon hsent
    have hword :
        solcSlotWord σ I (solcMappingSlot ⟨2⟩ (safeIsOwnerWord I)) =
          safeIsOwnerStorageWord σ I := by
      unfold safeIsOwnerStorageWord
      rw [safeIsOwnerSlotFor_eq hcanon]
    simpa [safeIsOwnerReturnWord, hsent, safeIsOwnerMaskedStorageWord, hword] using hret

theorem safeIsOwnerStorageNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeIsOwnerMaskedStorageWord σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeIsOwnerLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.storage (ownersRef (.var "owner"))) zeroAddr) =
      .ok (.bool false) := by
  have hstorage := safeIsOwnerStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddr :
      AccountAddress.ofNat (safeIsOwnerMaskedStorageWord σ I).toNat =
        AccountAddress.ofNat 0 := by
    rw [hzero]
    rfl
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeIsOwnerMaskedStorageWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = true := by
    simp [BEq.beq, hstorageAddr]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeIsOwnerStorageNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeIsOwnerMaskedStorageWord σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeIsOwnerLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.storage (ownersRef (.var "owner"))) zeroAddr) =
      .ok (.bool true) := by
  have hstorage := safeIsOwnerStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddrNe :
      AccountAddress.ofNat (safeIsOwnerMaskedStorageWord σ I).toNat ≠
        AccountAddress.ofNat 0 := by
    intro haddr
    exact hzero ((safeAccountAddress_ofNat_zero_iff
      (solcAddrMask_result_canonical (safeIsOwnerStorageWord σ I))).mp haddr)
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeIsOwnerMaskedStorageWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false := by
    simp [BEq.beq, hstorageAddrNe]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeIsOwnerOwnerNeSentinel_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsent : safeIsOwnerWord I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeIsOwnerLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "owner") sentinelAddr) =
      .ok (.bool false) := by
  have hownerAddr :
      AccountAddress.ofNat (safeIsOwnerWord I).toNat = AccountAddress.ofNat 1 := by
    rw [hsent]
    rfl
  have hownerBeq :
      (safeIsOwnerValue I == Value.address (AccountAddress.ofNat 1)) = true := by
    simp [safeIsOwnerValue, BEq.beq, hownerAddr]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeIsOwnerLocals, safeIsOwnerValue, hownerBeq]

theorem safeIsOwnerOwnerNeSentinel_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus)
    (hsent : safeIsOwnerWord I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := safeIsOwnerLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "owner") sentinelAddr) =
      .ok (.bool true) := by
  have hownerAddrNe :
      AccountAddress.ofNat (safeIsOwnerWord I).toNat ≠ AccountAddress.ofNat 1 := by
    intro haddr
    exact hsent ((safeAccountAddress_ofNat_one_iff hcanon).mp haddr)
  have hownerBeq :
      (safeIsOwnerValue I == Value.address (AccountAddress.ofNat 1)) = false := by
    simp [safeIsOwnerValue, BEq.beq, hownerAddrNe]
  unfold neE
  simp [evalExpr?, sentinelAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, safeIsOwnerLocals, safeIsOwnerValue, hownerBeq]

theorem safeIsOwnerBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeIsOwnerLocals I) isownerTransition.body
      (.returned { contract := contract, locals := safeIsOwnerLocals I }
        (initState cA gh bl σ σ₀ g A I)
        (some [safeIsOwnerReturnValue σ I])) := by
  refine nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (by simp only [initState]; exact hwv) ?_
  by_cases hsent : safeIsOwnerWord I = ⟨1⟩
  · by_cases hzero : safeIsOwnerMaskedStorageWord σ I = ⟨0⟩
    · have hleft := safeIsOwnerStorageNeZero_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      unfold ownerEnabledExpr andE
      simp [evalExpr?, hleft, safeIsOwnerReturnValue, hsent,
        EvalResult.bind, bind, pure]
    · have hleft := safeIsOwnerStorageNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      have hright := safeIsOwnerOwnerNeSentinel_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsent
      unfold ownerEnabledExpr andE
      simp [evalExpr?, hleft, hright, safeIsOwnerReturnValue, hsent,
        EvalResult.bind, bind, pure]
  · by_cases hzero : safeIsOwnerMaskedStorageWord σ I = ⟨0⟩
    · have hleft := safeIsOwnerStorageNeZero_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      unfold ownerEnabledExpr andE
      simp [evalExpr?, hleft, safeIsOwnerReturnValue, hsent, hzero,
        EvalResult.bind, bind, pure]
    · have hleft := safeIsOwnerStorageNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
      have hright := safeIsOwnerOwnerNeSentinel_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hsent
      unfold ownerEnabledExpr andE
      simp [evalExpr?, hleft, hright, safeIsOwnerReturnValue, hsent, hzero,
        EvalResult.bind, bind, pure]

theorem safeIsOwnerBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 21))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : safeIsOwnerStorageWord σ_evm I = safeIsOwnerStorageWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeIsOwnerSlotFor I) ⟨0⟩
  have hretVal : safeIsOwnerReturnValue σ_solm I = safeIsOwnerReturnValue σ_evm I := by
    unfold safeIsOwnerReturnValue safeIsOwnerMaskedStorageWord
    rw [← hword]
  exact safeReEquivExecTransport hcode
    (safeIsOwnerX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hsmall hsize hcanon hsel)
    (safeSelectorDispatchIsOwner hsel)
    (safeDecode_isOwner_ok hsz36 hsmall hcanon)
    (safeIsOwnerBodyReturns hwv hcanon) (by rw [hretVal])
    hAccounts
    (returnEquiv_of_encode (safeIsOwnerReturnEncoding σ_evm I))

theorem safeIsOwnerBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) (hsel : selIs I (safeSelBytes 21)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h780⟩ := safeReachIsOwnerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h793⟩ := safeGuardPeelOk (gt := ⟨791⟩) h780 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode (safeIsOwnerDecodeReverts_len h793 hlt)
    (safeSelectorDispatchIsOwner hsel)
    (safeDecode_isOwner_none_short hsz4 hshort)

theorem safeIsOwnerBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 21)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h780⟩ := safeReachIsOwnerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h793⟩ := safeGuardPeelOk (gt := ⟨791⟩) h780 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact safeReEquivDecodeFailed hcode (safeIsOwnerDecodeReverts_len h793 hlt)
    (safeSelectorDispatchIsOwner hsel)
    (safeDecode_isOwner_none_huge hbig)

theorem safeIsOwnerBodyCoreDecodeFailed_noncanon
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeIsOwnerWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 21)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h780⟩ := safeReachIsOwnerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h793⟩ := safeGuardPeelOk (gt := ⟨791⟩) h780 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  exact safeReEquivDecodeFailed hcode
    (safeIsOwnerDecodeReverts_noncanon h793 hsz36 hsmall hsize hnc)
    (safeSelectorDispatchIsOwner hsel)
    (safeDecode_isOwner_none_noncanon hsz36 hsmall hnc)

theorem safeIsOwnerBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 21))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 21) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases hcanon : (safeIsOwnerWord I).toNat < EVM.addressModulus
        · exact safeIsOwnerBodyCoreOk hcode hsize hwv hsz36 hsmall hcanon hsel
            hAccounts
        · exact safeIsOwnerBodyCoreDecodeFailed_noncanon hcode hsize hwv hsz36
            hsmall hcanon hsel
      · exact safeIsOwnerBodyCoreDecodeFailed_short hcode hsize hwv hsz4 (by omega)
          hsel
    · exact safeIsOwnerBodyCoreDecodeFailed_huge hcode hsize hwv hsz4 (by omega) hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 21) (by native_decide) hsel
    obtain ⟨_, _, h780⟩ := safeReachIsOwnerBody (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨791⟩) h780 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchIsOwner hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
