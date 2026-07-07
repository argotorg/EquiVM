import Benchmarks.Safe.Routines

/-! # Safe `approveHash(bytes32)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeApproveHashArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev safeApproveHashWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeApproveHashValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (safeApproveHashArgBytes I)

abbrev safeApproveHashLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "hashToApprove" (safeApproveHashValue I)

abbrev safeApproveHashSourceKeyValue (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev safeApproveHashHashKeyValue (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (safeApproveHashArgBytes I)

abbrev safeApproveHashOwnerEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "owners", steps := [.mindex (safeApproveHashSourceKeyValue I)] }

abbrev safeApproveHashApprovedEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "approvedHashes",
    steps := [.mindex (safeApproveHashSourceKeyValue I),
      .mindex (safeApproveHashHashKeyValue I)] }

abbrev safeApproveHashOwnerSlotFor (I : ExecutionEnv) : UInt256 :=
  ownersSlot (safeApproveHashSourceKeyValue I)

abbrev safeApproveHashSlotFor (I : ExecutionEnv) : UInt256 :=
  approvedHashesSlot (safeApproveHashSourceKeyValue I) (safeApproveHashHashKeyValue I)

def safeApproveHashOwnerStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeApproveHashOwnerSlotFor I)

abbrev safeApproveHashMaskedOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (safeApproveHashOwnerStorageWord σ I) solcAddrMask

def safeApproveHashPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (safeApproveHashSlotFor I) ⟨1⟩

def safeApproveHashPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (safeApproveHashSlotFor I) ⟨1⟩

def safeApproveHashTopic : UInt256 :=
  ⟨109744027374643845595422045803650255011224469847570155378144108490179203321244⟩

def safeApproveHashErrorSelector : UInt256 :=
  UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩

def safeApproveHashOwnerErrorStringWord : UInt256 :=
  UInt256.shiftLeft (⟨19146146611⟩ : UInt256) ⟨220⟩

noncomputable abbrev safeApproveHashOwnerHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem

noncomputable abbrev safeApproveHashInnerHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨8⟩ (safeApproveHashOwnerHashMem I)

noncomputable abbrev safeApproveHashStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (safeApproveHashWord I) (solcMappingSlot ⟨8⟩ (solcSourceWord I))
    (safeApproveHashInnerHashMem I)

noncomputable abbrev safeApproveHashOwnerRevertSelectorMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray safeApproveHashErrorSelector).write 0
    (safeApproveHashOwnerHashMem I) 128 32

noncomputable abbrev safeApproveHashOwnerRevertOffsetMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (safeApproveHashOwnerRevertSelectorMem I) 132 32

noncomputable abbrev safeApproveHashOwnerRevertLengthMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨5⟩ : UInt256)).write 0
    (safeApproveHashOwnerRevertOffsetMem I) 164 32

noncomputable abbrev safeApproveHashOwnerRevertMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray safeApproveHashOwnerErrorStringWord).write 0
    (safeApproveHashOwnerRevertLengthMem I) 196 32

theorem safeApproveHashOwnerHashMem_size (I : ExecutionEnv) :
    (safeApproveHashOwnerHashMem I).size = 96 :=
  twoWordHashMem_size_96 (solcSourceWord I) ⟨2⟩ solcFreePtrMem_size

theorem safeApproveHashOwnerHashMem_read64 (I : ExecutionEnv) :
    (safeApproveHashOwnerHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 (solcSourceWord I) ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem safeApproveHashOwnerHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (safeApproveHashOwnerHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then
      ⟨0⟩
    else
      UInt256.ofNat (fromByteArrayBigEndian
        ((safeApproveHashOwnerHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = (⟨128⟩ : UInt256) :=
  mloadFreePtrValue (by rw [safeApproveHashOwnerHashMem_size]; decide) (by decide)
    (safeApproveHashOwnerHashMem_read64 I)

theorem safeApproveHashInnerHashMem_size (I : ExecutionEnv) :
    (safeApproveHashInnerHashMem I).size = 96 :=
  twoWordHashMem_size_96 (solcSourceWord I) ⟨8⟩ (safeApproveHashOwnerHashMem_size I)

theorem safeApproveHashInnerHashMem_read64 (I : ExecutionEnv) :
    (safeApproveHashInnerHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 (solcSourceWord I) ⟨8⟩ (safeApproveHashOwnerHashMem_size I)
    (safeApproveHashOwnerHashMem_read64 I)

theorem safeApproveHashStoreHashMem_size (I : ExecutionEnv) :
    (safeApproveHashStoreHashMem I).size = 96 :=
  twoWordHashMem_size_96 (safeApproveHashWord I)
    (solcMappingSlot ⟨8⟩ (solcSourceWord I)) (safeApproveHashInnerHashMem_size I)

theorem safeApproveHashStoreHashMem_read64 (I : ExecutionEnv) :
    (safeApproveHashStoreHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 (safeApproveHashWord I)
    (solcMappingSlot ⟨8⟩ (solcSourceWord I)) (safeApproveHashInnerHashMem_size I)
    (safeApproveHashInnerHashMem_read64 I)

theorem safeApproveHashStoreHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (safeApproveHashStoreHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then
      ⟨0⟩
    else
      UInt256.ofNat (fromByteArrayBigEndian
        ((safeApproveHashStoreHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = (⟨128⟩ : UInt256) :=
  mloadFreePtrValue (by rw [safeApproveHashStoreHashMem_size]; decide) (by decide)
    (safeApproveHashStoreHashMem_read64 I)

theorem safeApproveHashArgBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (safeApproveHashArgBytes I).length = 32 := by
  simp [safeApproveHashArgBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem safeApproveHashSourceKeyValue_eq (I : ExecutionEnv) :
    keyValueToWord (safeApproveHashSourceKeyValue I) = solcSourceWord I := by
  simpa [safeApproveHashSourceKeyValue, solcSourceWord] using keyValueToWord_address I.source

theorem safeApproveHashHashKeyValue_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (safeApproveHashHashKeyValue I) = safeApproveHashWord I := by
  have hword :
      ABI.bytesToWord (safeApproveHashArgBytes I) = safeApproveHashWord I := by
    simpa [safeApproveHashArgBytes, safeApproveHashWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hbytes :
      EVM.Word.toBytesBE (safeApproveHashWord I) = safeApproveHashArgBytes I := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length (safeApproveHashArgBytes_length hsz36)
  rw [show safeApproveHashHashKeyValue I =
      .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (safeApproveHashWord I)) by
        simp [safeApproveHashHashKeyValue, bytes32Width, hbytes]]
  exact keyValueToWord_fixedBytes32 (safeApproveHashWord I)

theorem safeApproveHashOwnerSlotFor_eq (I : ExecutionEnv) :
    safeApproveHashOwnerSlotFor I = solcMappingSlot ⟨2⟩ (solcSourceWord I) := by
  unfold safeApproveHashOwnerSlotFor ownersSlot mapSlot solcMappingSlot
  rw [safeApproveHashSourceKeyValue_eq]

theorem safeApproveHashSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    safeApproveHashSlotFor I =
      solcMappingSlot (solcMappingSlot ⟨8⟩ (solcSourceWord I)) (safeApproveHashWord I) := by
  unfold safeApproveHashSlotFor approvedHashesSlot approvedHashesOwnerSlot mapSlot solcMappingSlot
  rw [safeApproveHashSourceKeyValue_eq, safeApproveHashHashKeyValue_eq hsz36]

theorem safeApproveHashAccountAddress_ofNat_zero_iff {w : UInt256}
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

theorem safeDecode_approveHash_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (approvehashTransition.params.map Param.name)
      (transitionSignature approvehashTransition).paramTypes I.calldata =
        some (safeApproveHashLocals I) := by
  simpa [config, safeDecodeMode, approvehashTransition, safeApproveHashValue,
    safeApproveHashArgBytes, safeApproveHashLocals, bytes32, bytes32Width] using
      (decodeCalldata_bytes32_ok (cd := I.calldata) (x := "hashToApprove") hsz36
        hsmall)

theorem safeDecode_approveHash_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (approvehashTransition.params.map Param.name)
      (transitionSignature approvehashTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, approvehashTransition, bytes32, bytes32Width] using
    (decodeCalldata_bytes32_none_short (cd := I.calldata) (x := "hashToApprove") hsz4
      hshort)

theorem safeDecode_approveHash_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (approvehashTransition.params.map Param.name)
      (transitionSignature approvehashTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, approvehashTransition, bytes32, bytes32Width] using
    (decodeCalldata_bytes32_none_huge (cd := I.calldata) (x := "hashToApprove") hbig)

theorem safeApproveHashDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1341⟩
      [safeApproveHashWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have h9894 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1341⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9894⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9903 := h9894.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9903' := h9903
  rw [hlt] at h9903'
  have h9906 := h9903'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9910⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9906
  have h9910 := h9906.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9916 := h9910.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [safeApproveHashWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using h9916.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeApproveHashDecodeReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9894 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1341⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9894⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9903 := h9894.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9903' := h9903
  rw [hlt] at h9903'
  have h9906 := h9903'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9910⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h9906
  have h9907 := h9906.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9907.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeApproveHashOwnerGuardOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5195⟩
      [safeApproveHashWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (howner : safeApproveHashMaskedOwnerWord σ I ≠ ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5240⟩
      [safeApproveHashWord I, ⟨664⟩, sel] (safeApproveHashOwnerHashMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hownerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((safeApproveHashOwnerHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨2⟩ (solcSourceWord I) := by
    exact twoWordHashMem_solcMappingSlot ⟨2⟩ (solcSourceWord I) solcFreePtrMem_size
  have hloaded :
      solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I)) =
        safeApproveHashOwnerStorageWord σ I := by
    unfold safeApproveHashOwnerStorageWord solcSlotWord
    rw [safeApproveHashOwnerSlotFor_eq I]
  have hmaskLiteral :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I))) ≠ ⟨0⟩ := by
    rw [hmaskLiteral, Reasoning.Theory.u256_land_comm solcAddrMask
      (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I))), hloaded]
    exact howner
  have hcondRaw :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨2⟩ (solcSourceWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) ≠ ⟨0⟩ := by
    change UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I))) ≠ ⟨0⟩
    exact hcond
  have rd5200pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd5201 := rd5200pre.mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5205pre := rd5201
    |>.push1 ⟨2⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5206 := rd5205pre.mstore 0 (safeApproveHashOwnerHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5210 := rd5206
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd5211pre := rd5210.keccak256 0 (solcMappingSlot ⟨2⟩ (solcSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hownerSlot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5211⟩ := rd5211pre.sload (by native_decide) (by evm_ov)
  have rd5219 := rd5211
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5223 := rd5219
    |>.push2 ⟨5240⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd5223.jumpiT (by native_decide) hcondRaw (by native_decide) (by evm_ov)⟩

theorem safeApproveHashOwnerGuardReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5195⟩
      [safeApproveHashWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (howner : safeApproveHashMaskedOwnerWord σ I = ⟨0⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hownerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((safeApproveHashOwnerHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨2⟩ (solcSourceWord I) := by
    exact twoWordHashMem_solcMappingSlot ⟨2⟩ (solcSourceWord I) solcFreePtrMem_size
  have hloaded :
      solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I)) =
        safeApproveHashOwnerStorageWord σ I := by
    unfold safeApproveHashOwnerStorageWord solcSlotWord
    rw [safeApproveHashOwnerSlotFor_eq I]
  have hmaskLiteral :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I))) = ⟨0⟩ := by
    rw [hmaskLiteral, Reasoning.Theory.u256_land_comm solcAddrMask
      (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I))), hloaded]
    exact howner
  have hcondRaw :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage
            (solcMappingSlot ⟨2⟩ (solcSourceWord I)) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) = ⟨0⟩ := by
    change UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (solcSlotWord σ I (solcMappingSlot ⟨2⟩ (solcSourceWord I))) = ⟨0⟩
    exact hcond
  have rd5200pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd5201 := rd5200pre.mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5205pre := rd5201
    |>.push1 ⟨2⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5206 := rd5205pre.mstore 0 (safeApproveHashOwnerHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5210 := rd5206
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd5211pre := rd5210.keccak256 0 (solcMappingSlot ⟨2⟩ (solcSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hownerSlot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5211⟩ := rd5211pre.sload (by native_decide) (by evm_ov)
  have rd5219 := rd5211
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd5223 := rd5219
    |>.push2 ⟨5240⟩ (by native_decide) (by evm_ov)
  have rd5224 := rd5223.jumpiNT (by native_decide) hcondRaw (by evm_ov)
  have rd5236 := rd5224.push2 ⟨5240⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨19146146611⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨220⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have rd6898 := rd5236.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd6910pre := rd6898.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (safeApproveHashOwnerHashMem_mload64 I) (by decide) (by evm_ov)
    |>.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨229⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd6911 := rd6910pre.mstore 6 (safeApproveHashOwnerRevertSelectorMem I)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6917pre := rd6911
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have rd6918 := rd6917pre.mstore 3 (safeApproveHashOwnerRevertOffsetMem I)
    (UInt256.ofNat 6) (by native_decide) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by decide])
    (by native_decide) (by evm_ov)
  have rd6924pre := rd6918
    |>.push1 ⟨5⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨36⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have rd6925 := rd6924pre.mstore 3 (safeApproveHashOwnerRevertLengthMem I)
    (UInt256.ofNat 7) (by native_decide) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by decide])
    (by native_decide) (by evm_ov)
  have rd6930pre := rd6925
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push1 ⟨68⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have rd6931 := rd6930pre.mstore 3 (safeApproveHashOwnerRevertMem I)
    (UInt256.ofNat 8) (by native_decide) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by decide]; rfl)
    (by native_decide) (by evm_ov)
  have rd6934 := rd6931
    |>.push1 ⟨100⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  exact rd6934.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem safeApproveHashStoreLog {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5240⟩
      [safeApproveHashWord I, ⟨664⟩, sel] (safeApproveHashOwnerHashMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeApproveHashPostMap σ I) ByteArray.empty := by
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((safeApproveHashInnerHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨8⟩ (solcSourceWord I) := by
    exact twoWordHashMem_solcMappingSlot ⟨8⟩ (solcSourceWord I)
      (safeApproveHashOwnerHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((safeApproveHashStoreHashMem I).readWithPadding 0 64))) =
        solcMappingSlot (solcMappingSlot ⟨8⟩ (solcSourceWord I)) (safeApproveHashWord I) := by
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨8⟩ (solcSourceWord I))
      (safeApproveHashWord I) (safeApproveHashInnerHashMem_size I)
  have rd5245pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd5246 := rd5245pre.mstore 0
    (wordAt0Mem (solcSourceWord I) (safeApproveHashOwnerHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5252pre := rd5246
    |>.push1 ⟨8⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd5253 := rd5252pre.mstore 0 (safeApproveHashInnerHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5257pre := rd5253
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
  have rd5258 := rd5257pre.keccak256 0 (solcMappingSlot ⟨8⟩ (solcSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hinnerSlot)
    (by native_decide) (by evm_ov)
  have rd5260pre := rd5258
    |>.dup6 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
  have rd5261 := rd5260pre.mstore 0
    (wordAt0Mem (safeApproveHashWord I) (safeApproveHashInnerHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5263pre := rd5261
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have rd5264 := rd5263pre.mstore 0 (safeApproveHashStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5266pre := rd5264
    |>.dup1 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
  have rd5267 := rd5266pre.keccak256 0
    (solcMappingSlot (solcMappingSlot ⟨8⟩ (solcSourceWord I)) (safeApproveHashWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using houterSlot)
    (by native_decide) (by evm_ov)
  have rd5270pre := rd5267
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5271⟩ := rd5270pre.sstore hperm (by native_decide)
    (by change 6 ≤ 1024; decide)
  have rd5273pre := rd5271
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (safeApproveHashStoreHashMem_mload64 I) (by decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have rd5307 := rd5273pre.pushConst safeApproveHashTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have rd5309 := rd5307.log3 0 (UInt256.ofNat 3) (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by change 3 ≤ 1024; decide)
  have rd664 := rd5309
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd665 := rd664.jumpdest (by native_decide) (by evm_ov)
  have hslot :
      solcMappingSlot (solcMappingSlot ⟨8⟩ (solcSourceWord I)) (safeApproveHashWord I) =
        safeApproveHashSlotFor I := by
    rw [safeApproveHashSlotFor_eq (I := I) hsz36]
  simpa [safeApproveHashPostMap, hslot] using
    rd665.stop (by native_decide) (by evm_ov)

theorem safeApproveHashOwnerStorageEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeApproveHashLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (ownersRef sender)) =
      .ok (.address (AccountAddress.ofNat (safeApproveHashMaskedOwnerWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeApproveHashLocals I })
    (slot := ownersRef sender)
    (er := safeApproveHashOwnerEvaledRef I)
    (t := .address)
    (loc := addrLoc (safeApproveHashOwnerSlotFor I))
    (value := .address (AccountAddress.ofNat (safeApproveHashMaskedOwnerWord σ I).toNat))
    (hbase := by simp [ownersRef, safeApproveHashLocals])
    (her := by
      simp [safeApproveHashOwnerEvaledRef, safeApproveHashSourceKeyValue,
        safeApproveHashLocals, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        ownersRef, sender, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind, initState])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by
      simpa [safeApproveHashMaskedOwnerWord, safeApproveHashOwnerStorageWord, addrLoc,
        addressOffset0Loc] using
        storageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
          (safeApproveHashOwnerSlotFor I))]

theorem safeApproveHashOwnerNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeApproveHashMaskedOwnerWord σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeApproveHashLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.storage (ownersRef sender)) zeroAddr) =
      .ok (.bool false) := by
  have hstorage := safeApproveHashOwnerStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddr :
      AccountAddress.ofNat (safeApproveHashMaskedOwnerWord σ I).toNat =
        AccountAddress.ofNat 0 := by
    rw [hzero]
    rfl
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeApproveHashMaskedOwnerWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = true := by
    simp [BEq.beq, hstorageAddr]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeApproveHashOwnerNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeApproveHashMaskedOwnerWord σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeApproveHashLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.storage (ownersRef sender)) zeroAddr) =
      .ok (.bool true) := by
  have hstorage := safeApproveHashOwnerStorageEval (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hstorageAddrNe :
      AccountAddress.ofNat (safeApproveHashMaskedOwnerWord σ I).toNat ≠
        AccountAddress.ofNat 0 := by
    intro haddr
    exact hzero ((safeApproveHashAccountAddress_ofNat_zero_iff
      (solcAddrMask_result_canonical (safeApproveHashOwnerStorageWord σ I))).mp haddr)
  have hstorageBeq :
      (Value.address (AccountAddress.ofNat (safeApproveHashMaskedOwnerWord σ I).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false := by
    simp [BEq.beq, hstorageAddrNe]
  unfold neE
  simp [evalExpr?, zeroAddr, addrSt, castValue?, evalBinaryOp?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hstorage, hstorageBeq]

theorem safeApproveHashAssign {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := safeApproveHashLocals I } evm
        .storage (approvedHashesRef sender (.var "hashToApprove")) (.int 1) =
      .ok ({ contract := contract, locals := safeApproveHashLocals I },
        safeApproveHashPostState evm I) := by
  rw [assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := safeApproveHashLocals I })
    (evm := evm)
    (evm' := safeApproveHashPostState evm I)
    (slot := approvedHashesRef sender (.var "hashToApprove"))
    (er := safeApproveHashApprovedEvaledRef I)
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (safeApproveHashSlotFor I) (.int uint256Int))
    (n := 1)
    (hbase := by simp [approvedHashesRef, safeApproveHashLocals])
    (her := by
      have hlen : (safeApproveHashArgBytes I).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using safeApproveHashArgBytes_length (I := I) hsz36
      simp [safeApproveHashApprovedEvaledRef, safeApproveHashSourceKeyValue,
        safeApproveHashHashKeyValue, safeApproveHashValue, safeApproveHashArgBytes,
        safeApproveHashLocals, hlen, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, approvedHashesRef, sender, evalExpr?, envValue, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hsrc])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by
      simpa [safeApproveHashPostState] using
        storageLocStore_uint256 evm (safeApproveHashSlotFor I) (⟨1⟩ : UInt256))]

theorem safeApproveHashBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (howner : safeApproveHashMaskedOwnerWord σ I ≠ ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeApproveHashLocals I) approvehashTransition.body
      (.returned { contract := contract, locals := safeApproveHashLocals I }
        (safeApproveHashPostState (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (safeApproveHashOwnerNeZero_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ (safeApproveHashAssign (evm :=
    initState cA gh bl σ σ₀ g A I) (I := I) hsz36 (by simp [initState]))) ExecBlock.nil
  simp [evalExpr?, pure]

theorem safeApproveHashBodyReverts_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner : safeApproveHashMaskedOwnerWord σ I = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeApproveHashLocals I) approvehashTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeApproveHashOwnerNeZero_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) howner))

theorem safeApproveHashX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (howner : safeApproveHashMaskedOwnerWord σ I ≠ ⟨0⟩)
    (hsel : selIs I (safeSelBytes 2)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeApproveHashPostMap σ I) ByteArray.empty := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1315⟩ := safeReachApproveHashBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1328⟩ := safeGuardPeelOk (gt := ⟨1326⟩) h1315 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1341⟩ := safeApproveHashDecodeOk h1328 hsz36 hsmall hsize
  have h5195 := h1341.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨5195⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h5240⟩ := safeApproveHashOwnerGuardOk h5195 howner
  exact safeApproveHashStoreLog h5240 hperm hsz36

theorem safeApproveHashX_ownerRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (howner : safeApproveHashMaskedOwnerWord σ I = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 2)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1315⟩ := safeReachApproveHashBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1328⟩ := safeGuardPeelOk (gt := ⟨1326⟩) h1315 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1341⟩ := safeApproveHashDecodeOk h1328 hsz36 hsmall hsize
  have h5195 := h1341.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨5195⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  exact safeApproveHashOwnerGuardReverts h5195 howner

theorem safeApproveHashBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (howner : safeApproveHashMaskedOwnerWord σ_evm I ≠ ⟨0⟩)
    (hsel : selIs I (safeSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hownerWord :
      safeApproveHashOwnerStorageWord σ_evm I =
        safeApproveHashOwnerStorageWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeApproveHashOwnerSlotFor I) ⟨0⟩
  have hownerSolm : safeApproveHashMaskedOwnerWord σ_solm I ≠ ⟨0⟩ := by
    unfold safeApproveHashMaskedOwnerWord
    rw [← hownerWord]
    exact howner
  have hbody := safeApproveHashBodyReturns (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hwv hsz36 hownerSolm
  have hcreated :
      (cA, safeApproveHashPostMap σ_evm I).1 =
        (safeApproveHashPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).createdAccounts := by
    simp [safeApproveHashPostState, initState, storageStore_createdAccounts]
  have haccounts :
      accountMapEquiv (cA, safeApproveHashPostMap σ_evm I).2
        (safeApproveHashPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
    have hstore :=
      accountMapEquiv_sstoreAccountMap I.codeOwner (safeApproveHashSlotFor I) ⟨1⟩
        hAccounts
    simpa [safeApproveHashPostMap, safeApproveHashPostState, initState,
      storageStore_accountMap] using hstore
  have henc : returnEquiv ByteArray.empty none approvehashTransition.returnType := by
    rw [show approvehashTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact safeReEquivExecGen hcode
    (safeApproveHashX_ok (g := Sat256.ofUInt256 g) hcode hwv hperm hsz36 hsmall hsize
      howner hsel)
    (safeSelectorDispatchApproveHash hsel)
    (safeDecode_approveHash_ok hsz36 hsmall)
    hbody hcreated haccounts henc

theorem safeApproveHashBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) (hsel : selIs I (safeSelBytes 2)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1315⟩ := safeReachApproveHashBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h1328⟩ := safeGuardPeelOk (gt := ⟨1326⟩) h1315 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode (safeApproveHashDecodeReverts h1328 hlt)
    (safeSelectorDispatchApproveHash hsel)
    (safeDecode_approveHash_none_short hsz4 hshort)

theorem safeApproveHashBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 2)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1315⟩ := safeReachApproveHashBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h1328⟩ := safeGuardPeelOk (gt := ⟨1326⟩) h1315 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact safeReEquivDecodeFailed hcode (safeApproveHashDecodeReverts h1328 hlt)
    (safeSelectorDispatchApproveHash hsel)
    (safeDecode_approveHash_none_huge hbig)

theorem safeApproveHashBodyCoreRevert_owner
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (howner : safeApproveHashMaskedOwnerWord σ_evm I = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hownerWord :
      safeApproveHashOwnerStorageWord σ_evm I =
        safeApproveHashOwnerStorageWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeApproveHashOwnerSlotFor I) ⟨0⟩
  have hownerSolm : safeApproveHashMaskedOwnerWord σ_solm I = ⟨0⟩ := by
    unfold safeApproveHashMaskedOwnerWord
    rw [← hownerWord]
    exact howner
  exact safeReEquivExecRev hcode
    (safeApproveHashX_ownerRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36 hsmall hsize
      howner hsel)
    (safeSelectorDispatchApproveHash hsel)
    (safeDecode_approveHash_ok hsz36 hsmall)
    (safeApproveHashBodyReverts_owner (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hownerSolm)

theorem safeApproveHashBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 2) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases howner : safeApproveHashMaskedOwnerWord σ_evm I = ⟨0⟩
        · exact safeApproveHashBodyCoreRevert_owner hcode hsize hwv hsz36 hsmall
            howner hsel hAccounts
        · exact safeApproveHashBodyCoreOk hcode hsize hwv hperm hsz36 hsmall howner hsel
            hAccounts
      · exact safeApproveHashBodyCoreDecodeFailed_short hcode hsize hwv hsz4 (by omega)
          hsel
    · exact safeApproveHashBodyCoreDecodeFailed_huge hcode hsize hwv hsz4 (by omega) hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 2) (by native_decide) hsel
    obtain ⟨_, _, h1315⟩ := safeReachApproveHashBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1326⟩) h1315 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchApproveHash hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
