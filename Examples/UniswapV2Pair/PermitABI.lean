import Examples.UniswapV2Pair.PackedWordSource
import Examples.UniswapV2Pair.MutatorDispatch
import Examples.UniswapV2Pair.PermitDecode
import Examples.UniswapV2Pair.PermitRuntime
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

/-! ## `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)` source slice -/

/-- The raw ABI word for `permit`'s `owner` argument. -/
abbrev permitOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev permitOwnerMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (permitOwnerWord I)

/-- The raw ABI word for `permit`'s `spender` argument. -/
abbrev permitSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev permitSpenderMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (permitSpenderWord I)

/-- The raw ABI word for `permit`'s `value` argument. -/
abbrev permitValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

/-- The raw ABI word for `permit`'s `deadline` argument. -/
abbrev permitDeadlineWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

/-- The raw ABI word for `permit`'s `v` argument before solc's `uint8` mask. -/
abbrev permitVRawWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev permitVWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (permitVRawWord I) ⟨255⟩

/-- The raw ABI word for `permit`'s `r` argument. -/
abbrev permitRWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 164

/-- The raw ABI word for `permit`'s `s` argument. -/
abbrev permitSWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 196

abbrev permitArgBytes (I : ExecutionEnv) (offset : Nat) : List UInt8 :=
  ((I.calldata.toList.drop 4).drop offset).take 32

abbrev permitRBytes (I : ExecutionEnv) : List UInt8 :=
  permitArgBytes I 160

abbrev permitSBytes (I : ExecutionEnv) : List UInt8 :=
  permitArgBytes I 192

abbrev permitOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (permitOwnerWord I).toNat)

abbrev permitSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (permitSpenderWord I).toNat)

abbrev permitValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (permitValueWord I).toNat)

abbrev permitDeadlineValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (permitDeadlineWord I).toNat)

abbrev permitVValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (permitVWord I).toNat)

abbrev permitRValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (permitRBytes I)

abbrev permitSValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (permitSBytes I)

abbrev permitStore (I : ExecutionEnv) : Store :=
  let s0 : Store := ∅
  let s1 := s0.insert "owner" (permitOwnerValue I)
  let s2 := s1.insert "spender" (permitSpenderValue I)
  let s3 := s2.insert "value" (permitValueValue I)
  let s4 := s3.insert "deadline" (permitDeadlineValue I)
  let s5 := s4.insert "v" (permitVValue I)
  let s6 := s5.insert "r" (permitRValue I)
  s6.insert "s" (permitSValue I)

abbrev permitOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (permitOwnerWord I).toNat)

def permitNonceStorageSlot (I : ExecutionEnv) : UInt256 :=
  nonceSlot (permitOwnerKey I)

theorem permitNonceStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    permitNonceStorageSlot I = mapSlot (permitOwnerMaskedWord I) ⟨4⟩ := by
  unfold permitNonceStorageSlot nonceSlot permitOwnerKey permitOwnerMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

abbrev permitDomainSeparatorWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  codeOwnerStorageWord I σ ⟨3⟩

noncomputable abbrev permitNonceHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (permitOwnerMaskedWord I) ⟨4⟩ solcFreePtrMem

theorem permitNonceHashMem_size (I : ExecutionEnv) :
    (permitNonceHashMem I).size = 96 := by
  unfold permitNonceHashMem
  exact twoWordHashMem_size_96 (permitOwnerMaskedWord I) ⟨4⟩ solcFreePtrMem_size

theorem permitNonceHashMem_read64 (I : ExecutionEnv) :
    (permitNonceHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray (⟨128⟩ : UInt256) := by
  unfold permitNonceHashMem
  exact twoWordHashMem_read64 (permitOwnerMaskedWord I) ⟨4⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem permitNonceHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (permitNonceHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitNonceHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [permitNonceHashMem_size]; decide)
    (by native_decide)
    (permitNonceHashMem_read64 I)

theorem permitNonceKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((permitNonceHashMem I).readWithPadding 0 64))) =
      mapSlot (permitOwnerMaskedWord I) ⟨4⟩ := by
  rw [permitNonceHashMem, twoWordHashMem_read0_64 _ _ solcFreePtrMem_size]
  simpa [mapSlot, solcMappingSlot] using mappingSlot_single (permitOwnerMaskedWord I) ⟨4⟩

abbrev permitNonceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  codeOwnerStorageWord I σ (mapSlot (permitOwnerMaskedWord I) ⟨4⟩)

abbrev permitNonceNextWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  permitNonceWord σ I + ⟨1⟩

abbrev permitTypehashWord : UInt256 :=
  permitRuntimeTypehashWord

noncomputable def permitStructHashDataWrites (σ : AccountMap) (I : ExecutionEnv) :
    List (Nat × UInt256) :=
  permitRuntimeStructHashDataWrites (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
    (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)

noncomputable def permitStructHashDataMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  permitRuntimeStructHashDataMem (permitNonceHashMem I) (permitOwnerMaskedWord I)
    (permitSpenderMaskedWord I) (permitValueWord I) (permitNonceWord σ I)
    (permitDeadlineWord I)

noncomputable def permitStructHashLenMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  permitRuntimeStructHashLenMem (permitNonceHashMem I) (permitOwnerMaskedWord I)
    (permitSpenderMaskedWord I) (permitValueWord I) (permitNonceWord σ I)
    (permitDeadlineWord I)

noncomputable def permitStructHashMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  permitRuntimeStructHashMem (permitNonceHashMem I) (permitOwnerMaskedWord I)
    (permitSpenderMaskedWord I) (permitValueWord I) (permitNonceWord σ I)
    (permitDeadlineWord I)

noncomputable abbrev permitStructHashWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  permitRuntimeStructHashWord (permitNonceHashMem I) (permitOwnerMaskedWord I)
    (permitSpenderMaskedWord I) (permitValueWord I) (permitNonceWord σ I)
    (permitDeadlineWord I)

noncomputable abbrev permitStructHashValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  permitWordBytes32Value (permitStructHashWord σ I)

noncomputable abbrev permitDigestMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  permitRuntimeDigestMem (permitStructHashMem σ I) (permitDomainSeparatorWord σ I)
    (permitStructHashWord σ I)

noncomputable abbrev permitDigestWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  permitRuntimeDigestWord (permitStructHashMem σ I) (permitDomainSeparatorWord σ I)
    (permitStructHashWord σ I)

noncomputable abbrev permitDigestValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  permitWordBytes32Value (permitDigestWord σ I)

theorem permitStructHashMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (permitStructHashMem σ I).size = 352 := by
  simpa [permitStructHashMem] using
    permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
      (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
      (permitNonceHashMem_size I)

theorem permitDigestMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (permitDigestMem σ I).size = 450 := by
  simpa [permitDigestMem] using
    permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
      (permitStructHashMem_size σ I)

theorem permitStructHashMem_read160_192 (σ : AccountMap) (I : ExecutionEnv) :
    (permitStructHashMem σ I).readWithPadding 160 192 =
      UInt256.toByteArray permitTypehashWord ++ UInt256.toByteArray (permitOwnerMaskedWord I) ++
        UInt256.toByteArray (permitSpenderMaskedWord I) ++ UInt256.toByteArray (permitValueWord I) ++
          UInt256.toByteArray (permitNonceWord σ I) ++
            UInt256.toByteArray (permitDeadlineWord I) := by
  simpa [permitStructHashMem, permitTypehashWord] using
    permitRuntimeStructHashMem_read160_192 (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
      (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I) (permitNonceHashMem_size I)

theorem permitDigestMem_read384_66 (σ : AccountMap) (I : ExecutionEnv) :
    (permitDigestMem σ I).readWithPadding 384 66 =
      ByteArray.mk #[0x19, 0x01] ++ UInt256.toByteArray (permitDomainSeparatorWord σ I) ++
        UInt256.toByteArray (permitStructHashWord σ I) := by
  simpa [permitDigestMem] using
    permitRuntimeDigestMem_read384_66 (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
      (permitStructHashMem_size σ I)

noncomputable abbrev permitEcrecoverInputMem (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  permitRuntimeEcrecoverInputMem (permitDigestMem σ I) (permitDigestWord σ I)
    (permitVWord I) (permitRWord I) (permitSWord I)

noncomputable abbrev permitEcrecoverStaticcallMem
    (σ : AccountMap) (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  permitRuntimeEcrecoverStaticcallMem (permitDigestMem σ I) (permitDigestWord σ I)
    (permitVWord I) (permitRWord I) (permitSWord I) o

theorem permitEcrecoverInputMem_read482_128 (σ : AccountMap) (I : ExecutionEnv) :
    (permitEcrecoverInputMem σ I).readWithPadding 482 128 =
      UInt256.toByteArray (permitDigestWord σ I) ++ UInt256.toByteArray (permitVWord I) ++
        UInt256.toByteArray (permitRWord I) ++ UInt256.toByteArray (permitSWord I) := by
  simpa [permitEcrecoverInputMem] using
    permitRuntimeEcrecoverInputMem_read482_128 (permitDigestWord σ I) (permitVWord I)
      (permitRWord I) (permitSWord I) (permitDigestMem_size σ I)

abbrev permitAfterNonceAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (mapSlot (permitOwnerMaskedWord I) ⟨4⟩)
    (permitNonceNextWord σ I)

abbrev permitNonceLoadedWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (permitNonceStorageSlot I)

abbrev permitNonceLoadedValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (permitNonceLoadedWord evm I).toNat)

abbrev permitNonceNextLoadedWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  permitNonceLoadedWord evm I + ⟨1⟩

abbrev permitNonceNextLoadedValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (permitNonceNextLoadedWord evm I).toNat)

abbrev permitDomainSeparatorLoadedWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩

abbrev permitDomainSeparatorLoadedValue (evm : EVM.State) : Value :=
  permitWordBytes32Value (permitDomainSeparatorLoadedWord evm)

abbrev permitAfterDomainLoadStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (permitStore I).insert "domainSeparator" (permitDomainSeparatorLoadedValue evm)

abbrev permitAfterNonceLoadStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (permitAfterDomainLoadStore evm I).insert "nonce" (permitNonceLoadedValue evm I)

abbrev permitAfterStructHashStore (evm : EVM.State) (I : ExecutionEnv)
    (structHash : Value) : Store :=
  (permitAfterNonceLoadStore evm I).insert "structHash" structHash

abbrev permitAfterDigestStore (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) : Store :=
  (permitAfterStructHashStore evm I structHash).insert "digest" digest

abbrev permitAfterEcrecoverStore (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) : Store :=
  (permitAfterDigestStore evm I structHash digest).insert "recoveredAddress" recovered

abbrev permitSpenderKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (permitSpenderWord I).toNat)

abbrev permitApproveEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps := [.mindex (permitOwnerKey I), .mindex (permitSpenderKey I)] }

def permitApproveStorageSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (permitOwnerKey I) (permitSpenderKey I)

def permitApprovePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (permitApproveStorageSlot I)
    (permitValueWord I)

theorem permitApproveStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    permitApproveStorageSlot I =
      mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩) := by
  unfold permitApproveStorageSlot allowanceSlot allowanceOwnerSlot permitOwnerKey permitSpenderKey
    permitOwnerMaskedWord permitSpenderMaskedWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address_ofNat_mask]

theorem permitOwnerValue_masked (I : ExecutionEnv) :
    permitOwnerValue I =
      .address (AccountAddress.ofNat (permitOwnerMaskedWord I).toNat) := by
  simpa [permitOwnerValue, permitOwnerMaskedWord] using
    solcAddressValue_masked (permitOwnerWord I)

theorem permitSpenderValue_masked (I : ExecutionEnv) :
    permitSpenderValue I =
      .address (AccountAddress.ofNat (permitSpenderMaskedWord I).toNat) := by
  simpa [permitSpenderValue, permitSpenderMaskedWord] using
    solcAddressValue_masked (permitSpenderWord I)

theorem permitRecoveredAddress_masked {o : ByteArray}
    (ho32 : 32 ≤ o.size) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) =
      .address (AccountAddress.ofNat
        (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
          solcAddrMask).toNat) := by
  let recovered := fromByteArrayBigEndian (o.extract 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_extract0_32_lt ho32
  calc
    (.address (AccountAddress.ofNat recovered) : Value)
        = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
          rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
    _ = .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
          exact solcAddressValue_masked (UInt256.ofNat recovered)
    _ = .address (AccountAddress.ofNat
          (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat) := by
          rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)]

theorem permitRecoveredAddress_eq_owner_of_mask_eq {I : ExecutionEnv} {o : ByteArray}
    (ho32 : 32 ≤ o.size)
    (hmatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask =
        permitOwnerMaskedWord I) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) =
      permitOwnerValue I := by
  let recovered := fromByteArrayBigEndian (o.extract 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_extract0_32_lt ho32
  calc
    (.address (AccountAddress.ofNat recovered) : Value)
        = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
          rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
    _ = .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
          exact solcAddressValue_masked (UInt256.ofNat recovered)
    _ = .address (AccountAddress.ofNat (permitOwnerMaskedWord I).toNat) := by
          rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)]
          exact congrArg (fun w => (.address (AccountAddress.ofNat w.toNat) : Value)) hmatch
    _ = permitOwnerValue I := by
          exact (permitOwnerValue_masked I).symm

theorem permitRecoveredAddress_ne_zero_of_mask_ne_zero {o : ByteArray}
    (ho32 : 32 ≤ o.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) ≠
      .address (AccountAddress.ofNat 0) := by
  let recovered := fromByteArrayBigEndian (o.extract 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_extract0_32_lt ho32
  have hmasked :
      (.address (AccountAddress.ofNat recovered) : Value) =
        .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
    calc
      (.address (AccountAddress.ofNat recovered) : Value)
          = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
            rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
      _ = .address (AccountAddress.ofNat
            (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
            exact solcAddressValue_masked (UInt256.ofNat recovered)
  intro hzero
  apply hnz
  have hmaskedZero :
      (.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) : Value) =
        .address (AccountAddress.ofNat 0) := by
    rw [← hmasked]
    exact hzero
  injection hmaskedZero with haddr
  apply u256_inj
  have hcanon :
      (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat < AccountAddress.size := by
    simpa [AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (UInt256.ofNat recovered)
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  simp only [Fin.val_ofNat] at hval
  rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)] at hval
  rw [Nat.mod_eq_of_lt hcanon] at hval
  simpa using hval

theorem permitRecoveredAddress_eq_zero_of_mask_eq_zero {o : ByteArray}
    (ho32 : 32 ≤ o.size)
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask =
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) =
      .address (AccountAddress.ofNat 0) := by
  calc
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value)
        = .address (AccountAddress.ofNat
            (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
              solcAddrMask).toNat) := permitRecoveredAddress_masked ho32
    _ = .address (AccountAddress.ofNat 0) := by
          rw [hzero]
          simp

theorem permitRecoveredAddress_ne_owner_of_mask_ne {I : ExecutionEnv} {o : ByteArray}
    (ho32 : 32 ≤ o.size)
    (hne :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        permitOwnerMaskedWord I) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) ≠
      permitOwnerValue I := by
  intro heq
  apply hne
  let recovered := fromByteArrayBigEndian (o.extract 0 32)
  have hmaskedEq :
      (.address (AccountAddress.ofNat
          (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat) : Value) =
        .address (AccountAddress.ofNat (permitOwnerMaskedWord I).toNat) := by
    rw [← permitRecoveredAddress_masked (o := o) ho32, ← permitOwnerValue_masked I]
    exact heq
  injection hmaskedEq with haddr
  apply u256_inj
  have hcanonRecovered :
      (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat < AccountAddress.size := by
    simpa [AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (UInt256.ofNat recovered)
  have hcanonOwner :
      (permitOwnerMaskedWord I).toNat < AccountAddress.size := by
    simpa [permitOwnerMaskedWord, u256_land_comm, AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  simp only [Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt hcanonRecovered, Nat.mod_eq_of_lt hcanonOwner] at hval
  exact hval

theorem fromByteArrayBigEndian_readWithPadding0_32_lt (o : ByteArray) :
    fromByteArrayBigEndian (o.readWithPadding 0 32) < UInt256.size := by
  unfold fromByteArrayBigEndian fromBytesBigEndian
  have h := EVM.fromBytes'_le (bs := (o.readWithPadding 0 32).toList.reverse)
  rw [List.length_reverse] at h
  have hlen : (o.readWithPadding 0 32).toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (o.readWithPadding 0 32).size = 32
    unfold ByteArray.readWithPadding
    rw [if_neg (by norm_num : ¬ (32 ≥ 2 ^ 64))]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    have hreadLe : (o.readWithoutPadding 0 32).size ≤ 32 := by
      unfold ByteArray.readWithoutPadding
      by_cases h : 0 ≥ o.size
      · rw [if_pos h]
        simp
      · rw [if_neg h]
        rw [ByteArray.size_extract]
        omega
    omega
  rw [hlen] at h
  simpa [UInt256.size] using h

theorem permitRecoveredPaddedAddress_masked {o : ByteArray} :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) =
      .address (AccountAddress.ofNat
        (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask).toNat) := by
  let recovered := fromByteArrayBigEndian (o.readWithPadding 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_readWithPadding0_32_lt o
  calc
    (.address (AccountAddress.ofNat recovered) : Value)
        = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
          rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
    _ = .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
          exact solcAddressValue_masked (UInt256.ofNat recovered)
    _ = .address (AccountAddress.ofNat
          (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat) := by
          rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)]

theorem permitRecoveredPaddedAddress_eq_owner_of_mask_eq {I : ExecutionEnv} {o : ByteArray}
    (hmatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask =
        permitOwnerMaskedWord I) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) =
      permitOwnerValue I := by
  let recovered := fromByteArrayBigEndian (o.readWithPadding 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_readWithPadding0_32_lt o
  calc
    (.address (AccountAddress.ofNat recovered) : Value)
        = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
          rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
    _ = .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
          exact solcAddressValue_masked (UInt256.ofNat recovered)
    _ = .address (AccountAddress.ofNat (permitOwnerMaskedWord I).toNat) := by
          rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)]
          exact congrArg (fun w => (.address (AccountAddress.ofNat w.toNat) : Value)) hmatch
    _ = permitOwnerValue I := by
          exact (permitOwnerValue_masked I).symm

theorem permitRecoveredPaddedAddress_ne_zero_of_mask_ne_zero {o : ByteArray}
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) ≠
      .address (AccountAddress.ofNat 0) := by
  let recovered := fromByteArrayBigEndian (o.readWithPadding 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_readWithPadding0_32_lt o
  have hmasked :
      (.address (AccountAddress.ofNat recovered) : Value) =
        .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
    calc
      (.address (AccountAddress.ofNat recovered) : Value)
          = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
            rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
      _ = .address (AccountAddress.ofNat
            (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
            exact solcAddressValue_masked (UInt256.ofNat recovered)
  intro hzero
  apply hnz
  have hmaskedZero :
      (.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) : Value) =
        .address (AccountAddress.ofNat 0) := by
    rw [← hmasked]
    exact hzero
  injection hmaskedZero with haddr
  apply u256_inj
  have hcanon :
      (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat < AccountAddress.size := by
    simpa [AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (UInt256.ofNat recovered)
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  simp only [Fin.val_ofNat] at hval
  rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)] at hval
  rw [Nat.mod_eq_of_lt hcanon] at hval
  simpa using hval

theorem permitRecoveredPaddedAddress_eq_zero_of_mask_eq_zero {o : ByteArray}
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask =
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) =
      .address (AccountAddress.ofNat 0) := by
  calc
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value)
        = .address (AccountAddress.ofNat
            (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
              solcAddrMask).toNat) := permitRecoveredPaddedAddress_masked
    _ = .address (AccountAddress.ofNat 0) := by
          rw [hzero]
          simp

theorem permitRecoveredPaddedAddress_ne_owner_of_mask_ne {I : ExecutionEnv} {o : ByteArray}
    (hne :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        permitOwnerMaskedWord I) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) ≠
      permitOwnerValue I := by
  intro heq
  apply hne
  let recovered := fromByteArrayBigEndian (o.readWithPadding 0 32)
  have hmaskedEq :
      (.address (AccountAddress.ofNat
          (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat) : Value) =
        .address (AccountAddress.ofNat (permitOwnerMaskedWord I).toNat) := by
    rw [← permitRecoveredPaddedAddress_masked (o := o), ← permitOwnerValue_masked I]
    exact heq
  injection hmaskedEq with haddr
  apply u256_inj
  have hcanonRecovered :
      (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat < AccountAddress.size := by
    simpa [AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (UInt256.ofNat recovered)
  have hcanonOwner :
      (permitOwnerMaskedWord I).toNat < AccountAddress.size := by
    simpa [permitOwnerMaskedWord, u256_land_comm, AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  simp only [Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt hcanonRecovered, Nat.mod_eq_of_lt hcanonOwner] at hval
  exact hval

theorem permitApprovePostState_createdAccounts (evm : EVM.State) (I : ExecutionEnv) :
    (permitApprovePostState evm I).createdAccounts = evm.createdAccounts := by
  simp [permitApprovePostState, storageStore_createdAccounts]

theorem permitApprovePostState_accountMap_equiv {evm : EVM.State} {I : ExecutionEnv}
    {σ : AccountMap}
    (henv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ
        (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
        (permitValueWord I))
      (permitApprovePostState evm I).accountMap := by
  unfold permitApprovePostState
  rw [storageStore_accountMap]
  rw [show evm.executionEnv.codeOwner = I.codeOwner by rw [henv]]
  rw [permitApproveStorageSlot_eq_mapSlot_masked]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner
    (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
    (permitValueWord I) hAccounts

abbrev permitApproveCallStore (I : ExecutionEnv) : Store :=
  let s0 : Store := ∅
  let s1 := s0.insert "value" (permitValueValue I)
  let s2 := s1.insert "spender" (permitSpenderValue I)
  s2.insert "owner" (permitOwnerValue I)

abbrev permitAfterApproveStore (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) : Store :=
  (permitAfterEcrecoverStore evm I structHash digest recovered).insert "_approveResult" .unit

def permitAfterNonceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (permitNonceStorageSlot I)
    (permitNonceNextLoadedWord evm I)

theorem permitStorageStore_sigma0 (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem permitStorageStore_genesisBlockHeader (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem permitStorageStore_blocks (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).blocks = evm.blocks := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

abbrev permitNonceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "nonces", steps := [.mindex (permitOwnerKey I)] }

theorem permitVWord_toNat (I : ExecutionEnv) :
    (permitVWord I).toNat = (permitVRawWord I).toNat % EVM.twoPow 8 := by
  unfold permitVWord
  rw [uland_toNat]
  have hmask : (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 := by native_decide
  rw [hmask]
  change Nat.land (permitVRawWord I).toNat (2 ^ 8 - 1) =
    (permitVRawWord I).toNat % EVM.twoPow 8
  rw [nat_land_mask_eq_mod]
  rfl

theorem permitVWord_mask_left (I : ExecutionEnv) :
    UInt256.land (⟨255⟩ : UInt256) (permitVWord I) = permitVWord I := by
  rw [u256_land_comm]
  apply u256_inj
  rw [u256_land_toNat, permitVWord_toNat]
  have hmask : (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 := by
    native_decide
  rw [hmask]
  change Nat.land ((permitVRawWord I).toNat % EVM.twoPow 8) (2 ^ 8 - 1) %
      UInt256.size =
    (permitVRawWord I).toNat % EVM.twoPow 8
  rw [nat_land_mask_eq_mod]
  norm_num [EVM.twoPow]
  exact Nat.mod_eq_of_lt (by
    have hlt := Nat.mod_lt (permitVRawWord I).toNat (by norm_num : 0 < 256)
    norm_num [UInt256.size]
    omega)

theorem permitVWord_lt_uint8 (I : ExecutionEnv) :
    (permitVWord I).toNat < EVM.twoPow 8 := by
  rw [permitVWord_toNat]
  exact Nat.mod_lt _ (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 8)

theorem permitRBytes_eq_toBytesBE (I : ExecutionEnv) (hsz228 : 228 ≤ I.calldata.size) :
    permitRBytes I = EVM.Word.toBytesBE (permitRWord I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (((I.calldata.toList.drop 4).drop 160).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 160).take 32) =
      permitRWord I := by
    simpa [permitRWord, List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 164 (by omega) (by norm_num)
  have hbytes := toBytesBE_bytesToWord_of_length
    (bs := ((I.calldata.toList.drop 4).drop 160).take 32) hlen
  rw [hword] at hbytes
  simpa [permitRBytes, permitArgBytes] using hbytes.symm

theorem permitSBytes_eq_toBytesBE (I : ExecutionEnv) (hsz228 : 228 ≤ I.calldata.size) :
    permitSBytes I = EVM.Word.toBytesBE (permitSWord I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (((I.calldata.toList.drop 4).drop 192).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 192).take 32) =
      permitSWord I := by
    simpa [permitSWord, List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 196 (by omega) (by norm_num)
  have hbytes := toBytesBE_bytesToWord_of_length
    (bs := ((I.calldata.toList.drop 4).drop 192).take 32) hlen
  rw [hword] at hbytes
  simpa [permitSBytes, permitArgBytes] using hbytes.symm

theorem permitRValue_eq_wordBytes (I : ExecutionEnv) (hsz228 : 228 ≤ I.calldata.size) :
    permitRValue I = permitWordBytes32Value (permitRWord I) := by
  simp [permitRValue, permitWordBytes32Value, permitRBytes_eq_toBytesBE I hsz228]

theorem permitSValue_eq_wordBytes (I : ExecutionEnv) (hsz228 : 228 ≤ I.calldata.size) :
    permitSValue I = permitWordBytes32Value (permitSWord I) := by
  simp [permitSValue, permitWordBytes32Value, permitSBytes_eq_toBytesBE I hsz228]

theorem uniswapEcrecoverEncode_eq (σ : AccountMap) (I : ExecutionEnv)
    (hsz228 : 228 ≤ I.calldata.size) :
    config.externalABI.encode? "ecrecover"
        [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I] =
      some ((permitEcrecoverInputMem σ I).readWithPadding 482 128) := by
  have hv8 : (permitVWord I).toNat < EVM.twoPow 8 := permitVWord_lt_uint8 I
  have hword : EVM.word (permitVWord I).toNat = permitVWord I := by
    show UInt256.ofNat (permitVWord I).toNat = permitVWord I
    exact u256_ofNat_toNat (permitVWord I)
  have hdlen : (EVM.Word.toBytesBE (permitDigestWord σ I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (permitDigestWord σ I)
  have hrlen : (EVM.Word.toBytesBE (permitRWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (permitRWord I)
  have hslen : (EVM.Word.toBytesBE (permitSWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (permitSWord I)
  rw [permitEcrecoverInputMem_read482_128]
  change uniswapExternalABI.encode? "ecrecover" _ = _
  simp [uniswapExternalABI, encodeEcrecoverInput?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    permitDigestValue, permitWordBytes32Value, permitVValue,
    permitRValue_eq_wordBytes I hsz228, permitSValue_eq_wordBytes I hsz228,
    bytes32, bytes32Width, uint8, uint8Int, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, hdlen, hrlen, hslen, hv8, hword,
    zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

theorem permitDomainSeparatorWord_equiv {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    permitDomainSeparatorWord σ_evm I = permitDomainSeparatorWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩

theorem permitNonceWord_equiv {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    permitNonceWord σ_evm I = permitNonceWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (mapSlot (permitOwnerMaskedWord I) ⟨4⟩) ⟨0⟩

theorem permitStructHashWord_equiv {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    permitStructHashWord σ_evm I = permitStructHashWord σ_solm I := by
  have hnonce : permitNonceWord σ_evm I = permitNonceWord σ_solm I :=
    permitNonceWord_equiv hAccounts
  simp [permitStructHashWord, hnonce]

theorem permitStructHashMem_equiv {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    permitStructHashMem σ_evm I = permitStructHashMem σ_solm I := by
  have hnonce : permitNonceWord σ_evm I = permitNonceWord σ_solm I :=
    permitNonceWord_equiv hAccounts
  simp [permitStructHashMem, hnonce]

theorem permitDigestWord_equiv {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    permitDigestWord σ_evm I = permitDigestWord σ_solm I := by
  have hdomain : permitDomainSeparatorWord σ_evm I = permitDomainSeparatorWord σ_solm I :=
    permitDomainSeparatorWord_equiv hAccounts
  have hstruct : permitStructHashWord σ_evm I = permitStructHashWord σ_solm I :=
    permitStructHashWord_equiv hAccounts
  have hstructMem : permitStructHashMem σ_evm I = permitStructHashMem σ_solm I :=
    permitStructHashMem_equiv hAccounts
  simp [permitDigestWord, hdomain, hstruct, hstructMem]

theorem permitDecodeABIValue_legacyAddress_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? (.elem .address) bytes start DecodeMode.legacySolc05 =
      some (.address (AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) :=
  permitDecodeABIValue_legacyAddress_ok_core hlen

theorem permitDecodeABIValue_uint256_legacy_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint256 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
        start + 32) :=
  permitDecodeABIValue_uint256_legacy_ok_core hlen

theorem permitDecodeABIValue_uint8_legacy_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint8 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat
          ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat % EVM.twoPow 8)),
        start + 32) :=
  permitDecodeABIValue_uint8_legacy_ok_core hlen

theorem permitDecodeABIValue_bytes32_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? bytes32 bytes start DecodeMode.legacySolc05 =
      some (.fixedBytes bytes32Width ((bytes.drop start).take 32), start + 32) :=
  permitDecodeABIValue_bytes32_ok_core hlen

-- LIBRARY CANDIDATE: legacy solc return decoder for `address`.
theorem permitDecodeReturnValue_legacyAddress_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 addr returndata =
      some (.address (AccountAddress.ofNat
        (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [addr].length)
    (by decide) (by simp)]
  simp [addr, decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok
    (bytes := returndata.toList) (start := 0) (by simpa [List.drop_zero] using htake0)]
  simp [hword, UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

-- LIBRARY CANDIDATE: legacy solc return decoder short-input failure for `address`.
theorem permitDecodeReturnValue_legacyAddress_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 addr returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0n : ¬ ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [addr].length)
    (by decide) (by simp)]
  simp [addr, decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_none_short
    (bytes := returndata.toList) (start := 0) (by simpa [List.drop_zero] using htake0n)]
  rfl

theorem uniswapEcrecoverDecode_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    config.externalABI.decode? "ecrecover" returndata =
      some [.address (AccountAddress.ofNat
        (fromByteArrayBigEndian (returndata.extract 0 32)))] := by
  change uniswapExternalABI.decode? "ecrecover" returndata = _
  simp [uniswapExternalABI, decodeEcrecoverOutput?]
  rw [readWithPadding_eq_extract returndata 0 hlo]

theorem uniswapEcrecoverDecode_padded (returndata : ByteArray) :
    config.externalABI.decode? "ecrecover" returndata =
      some [.address (AccountAddress.ofNat
        (fromByteArrayBigEndian (returndata.readWithPadding 0 32)))] := by
  change uniswapExternalABI.decode? "ecrecover" returndata = _
  simp [uniswapExternalABI, decodeEcrecoverOutput?]

theorem permitDecodeABIValues_ok {I : ExecutionEnv} (hsz228 : 228 ≤ I.calldata.size) :
    decodeABIValues? [legacyAddr, legacyAddr, uint256, uint256, uint8, bytes32, bytes32]
      (I.calldata.toList.drop 4) 0 0 224 224 DecodeMode.legacySolc05 =
      some ([.address (AccountAddress.ofNat
          (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32)).toNat),
        .int (Int.ofNat
          ((ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32)).toNat %
            EVM.twoPow 8)),
        .fixedBytes bytes32Width (((I.calldata.toList.drop 4).drop 160).take 32),
        .fixedBytes bytes32Width (((I.calldata.toList.drop 4).drop 192).take 32)], 224) :=
  permitDecodeABIValues_ok_core hsz228

theorem uniswapDecode_permit_ok {I : ExecutionEnv} (hsz228 : 228 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (permitTransition.params.map Param.name)
      (transitionSignature permitTransition).paramTypes I.calldata = some (permitStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05
    ["owner", "spender", "value", "deadline", "v", "r", "s"]
    [legacyAddr, legacyAddr, uint256, uint256, uint8, bytes32, bytes32] I.calldata = _
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
      calldataWord I.calldata 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32) =
      calldataWord I.calldata 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32) =
      calldataWord I.calldata 100 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 100 (by omega) (by norm_num)
  have hword132 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32) =
      calldataWord I.calldata 132 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 132 (by omega) (by norm_num)
  have hvals0 := permitDecodeABIValues_ok (I := I) hsz228
  have hvals : decodeABIValues?
      [ABIType.elem ElemType.address, ABIType.elem ElemType.address,
        ABIType.elem (ElemType.int (IntType.uint ⟨256, by decide⟩)),
        ABIType.elem (ElemType.int (IntType.uint ⟨256, by decide⟩)),
        ABIType.elem (ElemType.int (IntType.uint ⟨8, by decide⟩)),
        ABIType.elem (ElemType.bytes 31), ABIType.elem (ElemType.bytes 31)]
      (I.calldata.toList.drop 4) 0 0 224 224 DecodeMode.legacySolc05 =
      some ([.address (AccountAddress.ofNat
          (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32)).toNat),
        .int (Int.ofNat
          ((ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32)).toNat %
            EVM.twoPow 8)),
        .fixedBytes bytes32Width (((I.calldata.toList.drop 4).drop 160).take 32),
        .fixedBytes bytes32Width (((I.calldata.toList.drop 4).drop 192).take 32)], 224) := by
    simpa [legacyAddr, addr, uint256, uint8, bytes32, bytes32Width, uint256Int, uint8Int]
      using hvals0
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  unfold decodeCalldata.decodeArgs
  simp [legacyAddr, addr, uint256, uint8, bytes32, bytes32Width, uint256Int, uint8Int,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, isDynamicABIType,
    List.length_drop, htlen]
  rw [if_neg (by omega : ¬ I.calldata.size - 4 < 224)]
  rw [hvals]
  change decodeCalldata.insertValues ["owner", "spender", "value", "deadline", "v", "r", "s"]
      [.address (AccountAddress.ofNat
          (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32)).toNat),
        .int (Int.ofNat
          ((ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32)).toNat %
            EVM.twoPow 8)),
        .fixedBytes bytes32Width (((I.calldata.toList.drop 4).drop 160).take 32),
        .fixedBytes bytes32Width (((I.calldata.toList.drop 4).drop 192).take 32)] ∅ =
    some (permitStore I)
  rw [hword4, hword36, hword68, hword100, hword132]
  simp [decodeCalldata.insertValues, permitStore, permitOwnerValue, permitSpenderValue,
    permitValueValue, permitDeadlineValue, permitVValue, permitRValue, permitSValue,
    permitOwnerWord, permitSpenderWord, permitValueWord, permitDeadlineWord, permitVWord,
    permitVRawWord, permitVWord_toNat, permitRBytes, permitSBytes, permitArgBytes]

theorem uniswapDecode_permit_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 228) :
    decodeCalldataWithMode config.abiDecodeMode (permitTransition.params.map Param.name)
      (transitionSignature permitTransition).paramTypes I.calldata = none :=
  uniswapDecode_permit_none_short_core hsz4 hshort

/-! ## EVM wrapper prefix -/

/-- Short-calldata path for `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)`.

This covers calldata with a selector present but fewer than the seven static ABI words expected by
the optimized external wrapper. -/
theorem uniswapPermitX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 228)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1340⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨224⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := uniswapV2PairBytecode) (entry := ⟨1340⟩) (ret := ⟨570⟩)
    (decoded := ⟨1362⟩) (need := ⟨224⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

/-- The optimized external wrapper for `permit` decodes the seven static ABI words and jumps to
the shared permit routine at pc 5473. Legacy address words are masked before the jump. -/
theorem uniswapPermitX_decoded_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz228 : 228 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1340⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5473⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨224⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz228) hsize
  obtain ⟨_, _, rd1362⟩ := RD.solcExternalStaticArgsLenOk
    (code := uniswapV2PairBytecode) (entry := ⟨1340⟩) (ret := ⟨570⟩)
    (decoded := ⟨1362⟩) (need := ⟨224⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hlt
  have rd5473 := evm_run rd1362 with [
    jumpdest, pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2,
    calldataload, dup2, and, swap2, push1 ⟨32⟩, dup2, add, calldataload, swap1,
    swap2, and, swap1, push1 ⟨64⟩, dup2, add, calldataload, swap1, push1 ⟨96⟩,
    dup2, add, calldataload, swap1, push1 ⟨255⟩, push1 ⟨128⟩, dup3, add,
    calldataload, and, swap1, push1 ⟨160⟩, dup2, add, calldataload, swap1,
    push1 ⟨192⟩, add, calldataload, push2 ⟨5473⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [permitOwnerWord, permitOwnerMaskedWord, permitSpenderWord, permitSpenderMaskedWord,
      permitValueWord, permitDeadlineWord, permitVRawWord, permitVWord, permitRWord,
      permitSWord] using rd5473⟩

end UniswapV2Pair
