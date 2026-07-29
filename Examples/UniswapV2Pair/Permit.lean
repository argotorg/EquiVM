import Examples.UniswapV2Pair.EcrecoverTheta
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

abbrev permitWordBytes32Value (w : UInt256) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE w)

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
  simp [uniswapExternalABI, permitDecodeReturnValue_legacyAddress_ok hlo]

-- Short returndata fails the legacy `address` decode.  Only `o.size = 0` is reachable here:
-- the ecrecover precompile returns 0 or 32 bytes (`staticcallTheta_ecrecover_output_size`).
theorem uniswapEcrecoverDecode_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    config.externalABI.decode? "ecrecover" returndata = none := by
  change uniswapExternalABI.decode? "ecrecover" returndata = _
  simp [uniswapExternalABI, permitDecodeReturnValue_legacyAddress_none_short hshort]

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

theorem permitStore_owner (I : ExecutionEnv) :
    (permitStore I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_spender (I : ExecutionEnv) :
    (permitStore I).get? "spender" = some (permitSpenderValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_value (I : ExecutionEnv) :
    (permitStore I).get? "value" = some (permitValueValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_deadline (I : ExecutionEnv) :
    (permitStore I).get? "deadline" = some (permitDeadlineValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_v (I : ExecutionEnv) :
    (permitStore I).get? "v" = some (permitVValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_r (I : ExecutionEnv) :
    (permitStore I).get? "r" = some (permitRValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_s (I : ExecutionEnv) :
    (permitStore I).get? "s" = some (permitSValue I) := by
  rw [permitStore, store_get_self]

theorem permitStore_balanceOf (I : ExecutionEnv) :
    (permitStore I).get? "balanceOf" = none := by
  rw [permitStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem permitStore_nonces (I : ExecutionEnv) :
    (permitStore I).get? "nonces" = none := by
  rw [permitStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem permitStore_domainSeparatorRef (I : ExecutionEnv) :
    (permitStore I).get? domainSeparatorRef.base = none := by
  rw [domainSeparatorRef]
  change (permitStore I).get? "DOMAIN_SEPARATOR" = none
  rw [permitStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem permitAfterDomainLoadStore_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterDomainLoadStore evm I).get? "domainSeparator" =
      some (permitDomainSeparatorLoadedValue evm) := by
  rw [permitAfterDomainLoadStore, store_get_self]

theorem permitAfterDomainLoadStore_owner (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterDomainLoadStore evm I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_owner]

theorem permitAfterDomainLoadStore_nonces (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterDomainLoadStore evm I).get? "nonces" = none := by
  rw [permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_nonces]

theorem permitAfterNonceLoadStore_nonce (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "nonce" =
      some (permitNonceLoadedValue evm I) := by
  rw [permitAfterNonceLoadStore, store_get_self]

theorem permitAfterNonceLoadStore_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "domainSeparator" =
      some (permitDomainSeparatorLoadedValue evm) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore_domainSeparator]

theorem permitAfterNonceLoadStore_owner (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore_owner]

theorem permitAfterNonceLoadStore_spender (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "spender" = some (permitSpenderValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_spender]

theorem permitAfterNonceLoadStore_value (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "value" = some (permitValueValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_value]

theorem permitAfterNonceLoadStore_deadline (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "deadline" = some (permitDeadlineValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_deadline]

theorem permitAfterNonceLoadStore_v (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "v" = some (permitVValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_v]

theorem permitAfterNonceLoadStore_r (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "r" = some (permitRValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_r]

theorem permitAfterNonceLoadStore_s (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "s" = some (permitSValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_s]

theorem permitAfterNonceLoadStore_nonces (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "nonces" = none := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore_nonces]

theorem permitAfterDigestStore_digest (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "digest" = some digest := by
  rw [permitAfterDigestStore, store_get_self]

theorem permitAfterDigestStore_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "owner" =
      some (permitOwnerValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_owner]

theorem permitAfterDigestStore_spender (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "spender" =
      some (permitSpenderValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_spender]

theorem permitAfterDigestStore_value (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "value" =
      some (permitValueValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_value]

theorem permitAfterDigestStore_v (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "v" =
      some (permitVValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_v]

theorem permitAfterDigestStore_r (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "r" =
      some (permitRValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_r]

theorem permitAfterDigestStore_s (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "s" =
      some (permitSValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_s]

theorem permitAfterEcrecoverStore_recovered (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "recoveredAddress" =
      some recovered := by
  rw [permitAfterEcrecoverStore, store_get_self]

theorem permitAfterEcrecoverStore_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "owner" =
      some (permitOwnerValue I) := by
  rw [permitAfterEcrecoverStore, store_get_ne _ _ (by decide),
    permitAfterDigestStore_owner]

theorem permitAfterEcrecoverStore_spender (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "spender" =
      some (permitSpenderValue I) := by
  rw [permitAfterEcrecoverStore, store_get_ne _ _ (by decide),
    permitAfterDigestStore_spender]

theorem permitAfterEcrecoverStore_value (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "value" =
      some (permitValueValue I) := by
  rw [permitAfterEcrecoverStore, store_get_ne _ _ (by decide),
    permitAfterDigestStore_value]

theorem permitApproveCallStore_owner (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitApproveCallStore, store_get_self]

theorem permitApproveCallStore_spender (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "spender" = some (permitSpenderValue I) := by
  rw [permitApproveCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem permitApproveCallStore_value (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "value" = some (permitValueValue I) := by
  rw [permitApproveCallStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem permitApproveCallStore_allowance (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "allowance" = none := by
  rw [permitApproveCallStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_permit_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitStore_owner]

theorem evalExpr_permit_afterNonce_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_owner]

theorem evalExpr_permit_afterDomain_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDomainLoadStore_owner]

theorem evalExpr_permit_afterNonce_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_spender]

theorem evalExpr_permit_afterNonce_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_value]

theorem evalExpr_permit_afterNonce_deadline (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "deadline") = .ok (permitDeadlineValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_deadline]

theorem evalExpr_permit_afterNonce_v (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "v") = .ok (permitVValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_v]

theorem evalExpr_permit_afterNonce_r (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "r") = .ok (permitRValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_r]

theorem evalExpr_permit_afterNonce_s (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "s") = .ok (permitSValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_s]

theorem permitTypehashBytes_eq_toBytesBE :
    permitTypehashBytes = EVM.Word.toBytesBE permitTypehashWord := by
  native_decide

theorem byteArray_mk_toList_toArray (b : ByteArray) :
    ByteArray.mk b.toList.toArray = b := by
  apply ByteArray.ext
  rw [byteArray_toList_eq]

theorem byteArray_toList_append (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList_eq, byteArray_toList_eq, byteArray_toList_eq]
  simp [ByteArray.data_append]

theorem word_toBytesBE_eq_toByteArray_toList (w : UInt256) :
    EVM.Word.toBytesBE w = (UInt256.toByteArray w).toList := by
  have h := congrArg ByteArray.toList (word_toBytesBE_toByteArray_eq_toByteArray w)
  simpa [byteArray_toList_eq] using h

theorem permitDigestPrefix_toList :
    (ByteArray.mk #[0x19, 0x01]).toList = [0x19, 0x01] := by
  native_decide

theorem permitEncodePacked_uint256 (w : UInt256) :
    encodePackedValue? uint256 (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  have hlt : w.toNat < EVM.twoPow 256 := by
    change w.val.val < EVM.twoPow 256
    exact w.val.isLt
  simp [encodePackedValue?, uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem permitEncodePacked_bytes32 (w : UInt256) :
    encodePackedValue? bytes32 (permitWordBytes32Value w) =
      some (EVM.Word.toBytesBE w) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [encodePackedValue?, bytes32, bytes32Width, permitWordBytes32Value,
    fixedBytesSize, hlen]

theorem permitEncodePacked_typehash :
    encodePackedValue? bytes32 (.fixedBytes bytes32Width permitTypehashBytes) =
      some (EVM.Word.toBytesBE permitTypehashWord) := by
  have hlen : permitTypehashBytes.length = fixedBytesSize bytes32Width := by
    native_decide
  have hbytes : permitTypehashBytes = EVM.Word.toBytesBE permitTypehashWord :=
    permitTypehashBytes_eq_toBytesBE
  have hwordLen : (EVM.Word.toBytesBE permitTypehashWord).length =
      fixedBytesSize bytes32Width := by
    simpa [← hbytes] using hlen
  simp [encodePackedValue?, bytes32, bytes32Width, hbytes, hwordLen]

theorem permitEncodePacked_bytes2 :
    encodePackedValue? bytes2 (.fixedBytes bytes2Width [0x19, 0x01]) =
      some [0x19, 0x01] := by
  simp [encodePackedValue?, bytes2, bytes2Width, fixedBytesSize]

theorem permitEvalPackedArgs_cons {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head tailBytes : List UInt8}
    {rest : List (ABIType × Expr)}
    (he : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head)
    (htail : evalPackedArgs? cfg solm evm rest = .ok tailBytes) :
    evalPackedArgs? cfg solm evm ((ty, e) :: rest) = .ok (head ++ tailBytes) := by
  rw [evalPackedArgs?]
  simp only [he, henc, htail, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem permitEvalPackedArgs_single {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head : List UInt8}
    (he : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head) :
    evalPackedArgs? cfg solm evm [(ty, e)] = .ok head := by
  simp [evalPackedArgs?, he, henc, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem permitAddress_toNat_mask (w : UInt256) :
    (AccountAddress.ofNat w.toNat).toNat = (UInt256.land solcAddrMask w).toNat := by
  have hkey := keyValueToWord_address_ofNat_mask w
  rw [keyValueToWord_address] at hkey
  have hto := congrArg UInt256.toNat hkey
  have hleft : (UInt256.ofNat (AccountAddress.ofNat w.toNat).val).toNat =
      (AccountAddress.ofNat w.toNat).val := by
    exact UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le (AccountAddress.ofNat w.toNat).isLt (by decide))
  rw [hleft] at hto
  exact hto

theorem permitCast_addressAsUint256 (w : UInt256) :
    castValue? (.address (AccountAddress.ofNat w.toNat)) uint256St =
      some (.int (Int.ofNat (UInt256.land solcAddrMask w).toNat)) := by
  have haddr : (AccountAddress.ofNat w.toNat).toNat =
      (UInt256.land solcAddrMask w).toNat := permitAddress_toNat_mask w
  have hlt : (AccountAddress.ofNat w.toNat).toNat < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (AccountAddress.ofNat w.toNat).isLt (by decide)
  simp only [castValue?, uint256St, uint256Int]
  rw [if_pos hlt]
  rw [haddr]

theorem permitAfterStructHashStore_structHash (evm : EVM.State) (I : ExecutionEnv)
    (structHash : Value) :
    (permitAfterStructHashStore evm I structHash).get? "structHash" = some structHash := by
  rw [permitAfterStructHashStore, store_get_self]

theorem permitAfterStructHashStore_domainSeparator (evm : EVM.State) (I : ExecutionEnv)
    (structHash : Value) :
    (permitAfterStructHashStore evm I structHash).get? "domainSeparator" =
      some (permitDomainSeparatorLoadedValue evm) := by
  rw [permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_domainSeparator]

theorem evalExpr_permit_afterNonce_owner_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_owner]

theorem evalExpr_permit_afterNonce_spender_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_spender]

theorem evalExpr_permit_afterNonce_value_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_value]

theorem evalExpr_permit_afterNonce_nonce_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "nonce") = .ok (permitNonceLoadedValue base I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_nonce]

theorem evalExpr_permit_afterNonce_deadline_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "deadline") = .ok (permitDeadlineValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_deadline]

theorem evalExpr_permit_afterNonce_owner_uint256_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (addressAsUint256 (.var "owner")) =
        .ok (.int (Int.ofNat (permitOwnerMaskedWord I).toNat)) := by
  rw [addressAsUint256, evalExpr?]
  simp only [evalExpr_permit_afterNonce_owner_at base cur I, EvalResult.bind, bind]
  simp [permitOwnerValue, permitOwnerMaskedWord, EvalResult.ofOption,
    permitCast_addressAsUint256]

theorem evalExpr_permit_afterNonce_spender_uint256_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (addressAsUint256 (.var "spender")) =
        .ok (.int (Int.ofNat (permitSpenderMaskedWord I).toNat)) := by
  rw [addressAsUint256, evalExpr?]
  simp only [evalExpr_permit_afterNonce_spender_at base cur I, EvalResult.bind, bind]
  simp [permitSpenderValue, permitSpenderMaskedWord, EvalResult.ofOption,
    permitCast_addressAsUint256]

theorem evalExpr_permit_afterStructHash_structHash_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash : Value) :
    evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
      cur (.var "structHash") = .ok structHash := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterStructHashStore_structHash]

theorem evalExpr_permit_afterStructHash_domainSeparator_at
    (base cur : EVM.State) (I : ExecutionEnv) (structHash : Value) :
    evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
      cur (.var "domainSeparator") = .ok (permitDomainSeparatorLoadedValue base) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterStructHashStore_domainSeparator]

theorem permitDomainSeparatorLoadedWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitDomainSeparatorLoadedWord (initState cA gh bl σ σ₀ g A I) =
      permitDomainSeparatorWord σ I := by
  simpa [permitDomainSeparatorLoadedWord, permitDomainSeparatorWord, initState] using
    (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := ⟨3⟩))

theorem permitNonceLoadedWord_initState_for_hash {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitNonceLoadedWord (initState cA gh bl σ σ₀ g A I) I = permitNonceWord σ I := by
  unfold permitNonceLoadedWord permitNonceWord
  rw [permitNonceStorageSlot_eq_mapSlot_masked]
  simpa [initState] using
    (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (slot := mapSlot (permitOwnerMaskedWord I) ⟨4⟩))

theorem evalPackedArgs_permit_structHash_at {cA gh bl σ σ₀ A I} {g : Sat256}
    (cur : EVM.State) :
    evalPackedArgs? config
      { contract := contract,
        locals := permitAfterNonceLoadStore (initState cA gh bl σ σ₀ g A I) I }
      cur
      [ (bytes32, permitTypehashExpr),
        (uint256, addressAsUint256 (.var "owner")),
        (uint256, addressAsUint256 (.var "spender")),
        (uint256, .var "value"),
        (uint256, .var "nonce"),
        (uint256, .var "deadline") ] =
      .ok (((permitStructHashMem σ I).readWithPadding 160 192).toList) := by
  rw [permitStructHashMem_read160_192]
  simp only [byteArray_toList_append, List.append_assoc]
  refine permitEvalPackedArgs_cons
    (v := .fixedBytes bytes32Width permitTypehashBytes)
    (head := permitTypehashWord.toByteArray.toList)
    (tailBytes :=
      (permitOwnerMaskedWord I).toByteArray.toList ++
        ((permitSpenderMaskedWord I).toByteArray.toList ++
          ((permitValueWord I).toByteArray.toList ++
            ((permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList)))) ?_ ?_ ?_
  · simp [permitTypehashExpr, evalExpr?, pure]
  · simpa [word_toBytesBE_eq_toByteArray_toList] using permitEncodePacked_typehash
  · refine permitEvalPackedArgs_cons
      (v := .int (Int.ofNat (permitOwnerMaskedWord I).toNat))
      (head := (permitOwnerMaskedWord I).toByteArray.toList)
      (tailBytes :=
        (permitSpenderMaskedWord I).toByteArray.toList ++
          ((permitValueWord I).toByteArray.toList ++
            ((permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList))) ?_ ?_ ?_
    · exact evalExpr_permit_afterNonce_owner_uint256_at _ cur I
    · simpa [word_toBytesBE_eq_toByteArray_toList] using
        permitEncodePacked_uint256 (permitOwnerMaskedWord I)
    · refine permitEvalPackedArgs_cons
        (v := .int (Int.ofNat (permitSpenderMaskedWord I).toNat))
        (head := (permitSpenderMaskedWord I).toByteArray.toList)
        (tailBytes :=
          (permitValueWord I).toByteArray.toList ++
            ((permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList)) ?_ ?_ ?_
      · exact evalExpr_permit_afterNonce_spender_uint256_at _ cur I
      · simpa [word_toBytesBE_eq_toByteArray_toList] using
          permitEncodePacked_uint256 (permitSpenderMaskedWord I)
      · refine permitEvalPackedArgs_cons
          (v := .int (Int.ofNat (permitValueWord I).toNat))
          (head := (permitValueWord I).toByteArray.toList)
          (tailBytes :=
            (permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList) ?_ ?_ ?_
        · exact evalExpr_permit_afterNonce_value_at _ cur I
        · simpa [word_toBytesBE_eq_toByteArray_toList] using
            permitEncodePacked_uint256 (permitValueWord I)
        · refine permitEvalPackedArgs_cons
            (v := .int (Int.ofNat (permitNonceWord σ I).toNat))
            (head := (permitNonceWord σ I).toByteArray.toList)
            (tailBytes := (permitDeadlineWord I).toByteArray.toList) ?_ ?_ ?_
          · rw [evalExpr_permit_afterNonce_nonce_at]
            simp [permitNonceLoadedValue, permitNonceLoadedWord_initState_for_hash]
          · simpa [word_toBytesBE_eq_toByteArray_toList] using
              permitEncodePacked_uint256 (permitNonceWord σ I)
          · exact permitEvalPackedArgs_single
              (evalExpr_permit_afterNonce_deadline_at _ cur I)
              (by
                simpa [word_toBytesBE_eq_toByteArray_toList] using
                  permitEncodePacked_uint256 (permitDeadlineWord I))

theorem evalExpr_permit_structHash_at {cA gh bl σ σ₀ A I} {g : Sat256}
    (cur : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := permitAfterNonceLoadStore (initState cA gh bl σ σ₀ g A I) I }
      cur permitStructHashExpr = .ok (permitStructHashValue σ I) := by
  rw [permitStructHashExpr, evalExpr?, evalExpr?]
  simp only [evalPackedArgs_permit_structHash_at cur, EvalResult.bind, bind,
    byteArray_mk_toList_toArray]
  simp only [permitStructHashValue, permitWordBytes32Value, permitStructHashWord,
    permitRuntimeStructHashWord]
  rw [keccakSlot_eq, toBytesBE_keccak_uInt256OfByteArray]
  rfl

theorem evalExpr_permit_domainSeparator_afterNonce_at {cA gh bl σ σ₀ A I} {g : Sat256}
    (hne : (⟨3⟩ : UInt256) ≠ mapSlot (permitOwnerMaskedWord I) ⟨4⟩) :
    evalExpr? config
      { contract := contract,
        locals := permitAfterStructHashStore (initState cA gh bl σ σ₀ g A I) I
          (permitStructHashValue σ I) }
      (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I)
      (.storage domainSeparatorRef) =
        .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I)) := by
  let evmS := initState cA gh bl σ σ₀ g A I
  let evmNonceS := permitAfterNonceState evmS I
  have hbase :
      (permitAfterStructHashStore evmS I (permitStructHashValue σ I)).get?
        domainSeparatorRef.base = none := by
    rw [domainSeparatorRef]
    change (permitAfterStructHashStore evmS I (permitStructHashValue σ I)).get?
      "DOMAIN_SEPARATOR" = none
    rw [permitAfterStructHashStore, store_get_ne _ _ (by decide)]
    rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide)]
    rw [permitAfterDomainLoadStore, store_get_ne _ _ (by decide)]
    exact permitStore_domainSeparatorRef I
  have her :
      evalStorageRef config
        { contract := contract,
          locals := permitAfterStructHashStore evmS I (permitStructHashValue σ I) }
        evmNonceS domainSeparatorRef =
        .ok ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, domainSeparatorRef, EvalResult.bind, pure, bind]
  have hslotNe : (⟨3⟩ : UInt256) ≠ permitNonceStorageSlot I := by
    rw [permitNonceStorageSlot_eq_mapSlot_masked]
    exact hne
  have hloadInit :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩ =
        permitDomainSeparatorWord σ I := by
    simpa [evmS, permitDomainSeparatorWord] using
      (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := ⟨3⟩))
  have hloadNonce :
      Solm.EVM.storageLoad evmNonceS evmNonceS.executionEnv.codeOwner ⟨3⟩ =
        permitDomainSeparatorWord σ I := by
    have hneLoad := storageLoad_storageStore_ne evmS evmS.executionEnv.codeOwner
      (readSlot := ⟨3⟩) (writeSlot := permitNonceStorageSlot I)
      (val := permitNonceNextLoadedWord evmS I) hslotNe
    simpa [evmNonceS, permitAfterNonceState, storageStore_executionEnv, hloadInit] using hneLoad
  have hread :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore evmS I (permitStructHashValue σ I) }
        evmNonceS (.storage domainSeparatorRef) =
          .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I)) := by
    exact evalExpr_storage_scalar_value
      (t := .bytes bytes32Width)
      (loc := bytes32Loc ⟨3⟩)
      (hbase := hbase)
      (her := her)
      (hty := by
        simp [storageTypeAt?, contract, storageDecls, bytes32St])
      (hloc := by rfl)
      (hload := by
        rw [uniswapStorageLocLoad_bytes32, hloadNonce]
        simp [permitWordBytes32Value, bytes32Width])
  simpa [evmS, evmNonceS] using hread

theorem evalPackedArgs_permit_digest_at {base cur : EVM.State} {σ I}
    (hdomain :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
        cur (.var "domainSeparator") =
        .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I))) :
    evalPackedArgs? config
      { contract := contract,
        locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
      cur
      [ (bytes2, .fixedBytesLit bytes2Width [0x19, 0x01]),
        (bytes32, .var "domainSeparator"),
        (bytes32, .var "structHash") ] =
      .ok (((permitDigestMem σ I).readWithPadding 384 66).toList) := by
  rw [permitDigestMem_read384_66]
  simp only [byteArray_toList_append, permitDigestPrefix_toList, List.append_assoc]
  refine permitEvalPackedArgs_cons
    (v := .fixedBytes bytes2Width [0x19, 0x01])
    (head := [0x19, 0x01])
      (tailBytes :=
      (permitDomainSeparatorWord σ I).toByteArray.toList ++
        (permitStructHashWord σ I).toByteArray.toList) ?_ ?_ ?_
  · simp [evalExpr?, pure]
  · exact permitEncodePacked_bytes2
  · refine permitEvalPackedArgs_cons
      (v := permitWordBytes32Value (permitDomainSeparatorWord σ I))
      (head := (permitDomainSeparatorWord σ I).toByteArray.toList)
      (tailBytes := (permitStructHashWord σ I).toByteArray.toList) ?_ ?_ ?_
    · exact hdomain
    · simpa [word_toBytesBE_eq_toByteArray_toList] using
        permitEncodePacked_bytes32 (permitDomainSeparatorWord σ I)
    · exact permitEvalPackedArgs_single
        (evalExpr_permit_afterStructHash_structHash_at base cur I (permitStructHashValue σ I))
        (by
          simpa [word_toBytesBE_eq_toByteArray_toList] using
            permitEncodePacked_bytes32 (permitStructHashWord σ I))

theorem evalExpr_permit_digest_at {base cur : EVM.State} {σ I}
    (hdomain :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
        cur (.var "domainSeparator") =
        .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I))) :
    evalExpr? config
      { contract := contract,
        locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
      cur permitDigestExpr = .ok (permitDigestValue σ I) := by
  rw [permitDigestExpr, evalExpr?, evalExpr?]
  simp only [evalPackedArgs_permit_digest_at hdomain, EvalResult.bind, bind,
    byteArray_mk_toList_toArray]
  simp only [permitDigestValue, permitWordBytes32Value, permitDigestWord, permitRuntimeDigestWord]
  rw [keccakSlot_eq, toBytesBE_keccak_uInt256OfByteArray]
  rfl

theorem evalExpr_permit_digest_afterNonce_at {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config
      { contract := contract,
        locals := permitAfterStructHashStore (initState cA gh bl σ σ₀ g A I) I
          (permitStructHashValue σ I) }
      (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I)
      permitDigestExpr = .ok (permitDigestValue σ I) := by
  exact evalExpr_permit_digest_at (by
    rw [evalExpr_permit_afterStructHash_domainSeparator_at]
    simp [permitDomainSeparatorLoadedValue, permitWordBytes32Value,
      permitDomainSeparatorLoadedWord_initState])

theorem evalExpr_permit_afterDigest_digest (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "digest") = .ok digest := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_digest]

theorem evalExpr_permit_afterDigest_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_owner]

theorem evalExpr_permit_afterDigest_spender (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_spender]

theorem evalExpr_permit_afterDigest_value (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_value]

theorem evalExpr_permit_afterDigest_v (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "v") = .ok (permitVValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_v]

theorem evalExpr_permit_afterDigest_r (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "r") = .ok (permitRValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_r]

theorem evalExpr_permit_afterDigest_s (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "s") = .ok (permitSValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_s]

theorem evalExpr_permit_afterDigest_digest_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "digest") = .ok digest := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_digest]

theorem evalExpr_permit_afterDigest_v_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "v") = .ok (permitVValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_v]

theorem evalExpr_permit_afterDigest_r_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "r") = .ok (permitRValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_r]

theorem evalExpr_permit_afterDigest_s_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "s") = .ok (permitSValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_s]

theorem evalExprs_permit_ecrecover_args (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExprs? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm [.var "digest", .var "v", .var "r", .var "s"] =
      .ok [digest, permitVValue I, permitRValue I, permitSValue I] := by
  simp [evalExprs?, evalExpr_permit_afterDigest_digest,
    evalExpr_permit_afterDigest_v, evalExpr_permit_afterDigest_r,
    evalExpr_permit_afterDigest_s, EvalResult.bind, bind, pure]

theorem evalExprs_permit_ecrecover_args_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExprs? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur [.var "digest", .var "v", .var "r", .var "s"] =
      .ok [digest, permitVValue I, permitRValue I, permitSValue I] := by
  simp [evalExprs?, evalExpr_permit_afterDigest_digest_at,
    evalExpr_permit_afterDigest_v_at, evalExpr_permit_afterDigest_r_at,
    evalExpr_permit_afterDigest_s_at, EvalResult.bind, bind, pure]

theorem evalExpr_permit_afterEcrecover_recovered (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore evm I structHash digest recovered }
      evm (.var "recoveredAddress") = .ok recovered := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_recovered]

theorem evalExpr_permit_afterEcrecover_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore evm I structHash digest recovered }
      evm (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_owner]

theorem evalExpr_permit_afterEcrecover_recovered_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "recoveredAddress") = .ok recovered := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_recovered]

theorem evalExpr_permit_afterEcrecover_owner_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_owner]

theorem evalExpr_permit_afterEcrecover_spender_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_spender]

theorem evalExpr_permit_afterEcrecover_value_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_value]

theorem evalExprs_permit_approve_args_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExprs? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur [.var "owner", .var "spender", .var "value"] =
      .ok [permitOwnerValue I, permitSpenderValue I, permitValueValue I] := by
  simp [evalExprs?, evalExpr_permit_afterEcrecover_owner_at,
    evalExpr_permit_afterEcrecover_spender_at, evalExpr_permit_afterEcrecover_value_at,
    EvalResult.bind, bind, pure]

theorem evalExpr_permit_approve_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitApproveCallStore I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitApproveCallStore_owner]

theorem evalExpr_permit_approve_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitApproveCallStore I } evm
      (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitApproveCallStore_spender]

theorem evalExpr_permit_approve_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitApproveCallStore I } evm
      (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitApproveCallStore_value]

theorem evalStorageRef_permit_approve_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := permitApproveCallStore I } evm
      (allowanceRef (.var "owner") (.var "spender")) = .ok (permitApproveEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
    evalExpr_permit_approve_owner, evalExpr_permit_approve_spender, permitApproveEvaledRef,
    permitOwnerValue, permitSpenderValue, permitOwnerKey, permitSpenderKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem permitApproveAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := permitApproveCallStore I } evm
      .storage (allowanceRef (.var "owner") (.var "spender")) (permitValueValue I) =
        .ok ({ contract := contract, locals := permitApproveCallStore I },
          permitApprovePostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := permitApproveCallStore_allowance I)
      (her := evalStorageRef_permit_approve_allowance evm I)
      (hty := by
        simp [storageTypeAt?, contract, storageDecls, uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [permitApprovePostState, permitApproveStorageSlot]

theorem uniswapLookupApproveFunction :
    lookupCallable? contract "_approve" = some approveFunction.toCallable := by
  rfl

theorem bindParams_permit_approve_call (I : ExecutionEnv) :
    bindParams? approveFunction.params
      [permitOwnerValue I, permitSpenderValue I, permitValueValue I] =
      some (permitApproveCallStore I) := by
  simp [bindParams?, approveFunction, permitApproveCallStore]

theorem uniswapPermitApproveFunctionBody (evm : EVM.State) (I : ExecutionEnv) :
    ExecFuncBody config { contract := contract, locals := permitApproveCallStore I } evm
      approveFunction.body
      (.returned { contract := contract, locals := permitApproveCallStore I }
        (permitApprovePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config { contract := contract, locals := permitApproveCallStore I } evm
    [ .assign .storage (allowanceRef (.var "owner") (.var "spender")) (.var "value") ]
    (.ok { contract := contract, locals := permitApproveCallStore I }
      (permitApprovePostState evm I))
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_permit_approve_value evm I) (permitApproveAssign evm I))
    ExecBlock.nil

theorem uniswapPermitApproveCallSuccessAt {base cur : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} :
    ExecBlock config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      [ .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
          "_approveResult" ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterApproveStore base I structHash digest recovered })
        (permitApprovePostState cur I)) := by
  have hstmt :
      ExecStmt config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }
        cur
        (.internalCall "_approve" [.var "owner", .var "spender", .var "value"]
          "_approveResult")
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore base I structHash digest recovered })
          (permitApprovePostState cur I)) := by
    simpa [permitAfterApproveStore, resumeAfterInternalCall] using
      (internalCallFunctionReturn
      (cfg := config)
      (caller :=
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered })
      (evm := cur) (calleeEvm := permitApprovePostState cur I)
      (name := "_approve") (retVar := "_approveResult")
      (args := [.var "owner", .var "spender", .var "value"])
      (argVals := [permitOwnerValue I, permitSpenderValue I, permitValueValue I])
      (callee := approveFunction)
      (locals := permitApproveCallStore I)
      (calleeSolm := { contract := contract, locals := permitApproveCallStore I })
      (value := none)
      (evalExprs_permit_approve_args_at base cur I structHash digest recovered)
      uniswapLookupApproveFunction
      (bindParams_permit_approve_call I)
      (uniswapPermitApproveFunctionBody cur I))
  exact ExecBlock.consNormal hstmt ExecBlock.nil

theorem evalExpr_permit_zeroAddr (solm : Frame) (evm : EVM.State) :
    evalExpr? config solm evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
  simp only [zeroAddr, evalExpr?, castValue?, addrSt, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  norm_num

theorem evalExpr_permit_afterEcrecover_require_true (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value)
    (hnz : recovered ≠ .address (AccountAddress.ofNat 0))
    (heq : recovered = permitOwnerValue I) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))) =
      .ok (.bool true) := by
  have hownerNz :
      AccountAddress.ofNat (permitOwnerWord I).toNat ≠ AccountAddress.ofNat 0 := by
    intro h
    apply hnz
    rw [heq]
    simp [permitOwnerValue, h]
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [permitAfterEcrecoverStore_owner]
  have hzero :
      (Value.address (AccountAddress.ofNat (Int.toNat 0))) =
        (Value.address (AccountAddress.ofNat 0)) := by
    norm_num
  rw [hzero]
  simp [evalBinaryOp?, heq, hownerNz]
  have hbeqFalse :
      (permitOwnerValue I == Value.address (AccountAddress.ofNat 0)) = false := by
    simp [permitOwnerValue, hownerNz]
  rw [hbeqFalse]
  rfl

theorem evalExpr_permit_afterEcrecover_require_false_zero
    (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value)
    (hzero : recovered = .address (AccountAddress.ofNat 0)) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))) =
      .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [permitAfterEcrecoverStore_recovered, hzero, permitAfterEcrecoverStore_owner]
  have hzeroVal :
      (Value.address (AccountAddress.ofNat (Int.toNat 0))) =
        (Value.address (AccountAddress.ofNat 0)) := by
    norm_num
  rw [hzeroVal]
  simp [evalBinaryOp?]

theorem evalExpr_permit_afterEcrecover_require_false_mismatch
    (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) (recoveredAddr : AccountAddress)
    (haddr : recovered = .address recoveredAddr)
    (hnz : recoveredAddr ≠ AccountAddress.ofNat 0)
    (hne : .address recoveredAddr ≠ permitOwnerValue I) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))) =
      .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [permitAfterEcrecoverStore_recovered, permitAfterEcrecoverStore_owner, haddr]
  have hzeroVal :
      (Value.address (AccountAddress.ofNat (Int.toNat 0))) =
        (Value.address (AccountAddress.ofNat 0)) := by
    norm_num
  rw [hzeroVal]
  have hneZeroBeq :
      (Value.address recoveredAddr == Value.address (AccountAddress.ofNat 0)) = false := by
    apply beq_false_of_ne
    intro h
    apply hnz
    injection h
  have hneOwnerBeq : (Value.address recoveredAddr == permitOwnerValue I) = false := by
    exact beq_false_of_ne hne
  simp [evalBinaryOp?, hneZeroBeq, hneOwnerBeq]

theorem evalExpr_permit_ecrecover_receiver (solm : Frame) (evm : EVM.State) :
    evalExpr? config solm evm (.cast (.intLit 1) addrSt) =
      .ok (.address (AccountAddress.ofNat 1)) := by
  simp only [evalExpr?, castValue?, addrSt, EvalResult.ofOption, EvalResult.bind, bind, pure]
  norm_num

theorem evalExpr_permit_ecrecover_value (solm : Frame) (evm : EVM.State) :
    evalExpr? config solm evm (.intLit 0) = .ok (.int 0) := by
  simp only [evalExpr?, pure]

theorem uniswapPermitEcrecoverCallSuccess {evm evm' : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, evm', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered]) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore evm I structHash digest recovered }) evm') := by
  simpa [permitAfterEcrecoverStore, collapseReturns] using
    (Reasoning.Theory.externalCallSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := permitAfterDigestStore evm I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false)
      (value := [recovered]) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm)
      (evalExprs_permit_ecrecover_args evm I structHash digest)
      hcall hdec)

theorem uniswapPermitEcrecoverCallSuccessAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered]) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }) cur') := by
  simpa [permitAfterEcrecoverStore, collapseReturns] using
    (Reasoning.Theory.externalCallSuccess
      (cfg := config) (C := contract) (evm := cur) (evm' := cur')
      (locals := permitAfterDigestStore base I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false)
      (value := [recovered]) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur)
      (evalExprs_permit_ecrecover_args_at base cur I structHash digest)
      hcall hdec)

theorem uniswapPermitEcrecoverCallFailure {evm evm' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, evm', out) false) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := permitAfterDigestStore evm I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm)
      (evalExprs_permit_ecrecover_args evm I structHash digest)
      hcall)

theorem uniswapPermitEcrecoverCallFailureAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, cur', out) false) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallFailure
      (cfg := config) (C := contract) (evm := cur) (evm' := cur')
      (locals := permitAfterDigestStore base I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur)
      (evalExprs_permit_ecrecover_args_at base cur I structHash digest)
      hcall)

theorem uniswapPermitEcrecoverCallDecodeRevert {evm evm' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, evm', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := permitAfterDigestStore evm I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm)
      (evalExprs_permit_ecrecover_args evm I structHash digest)
      hcall hdec)

theorem uniswapPermitEcrecoverCallDecodeRevertAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallDecodeRevert
      (cfg := config) (C := contract) (evm := cur) (evm' := cur')
      (locals := permitAfterDigestStore base I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur)
      (evalExprs_permit_ecrecover_args_at base cur I structHash digest)
      hcall hdec)

theorem evalStorageRef_permit_nonce (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := permitStore I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, noncesRef,
    evalExpr_permit_owner, permitNonceEvaledRef, permitOwnerValue, permitOwnerKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_permit_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := permitStore I } evm
      domainSeparatorRef = .ok ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, domainSeparatorRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_permit_afterDomain_nonce (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, noncesRef,
    evalExpr_permit_afterDomain_owner, permitNonceEvaledRef, permitOwnerValue,
    permitOwnerKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_permit_afterNonce_nonce (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, noncesRef,
    evalExpr_permit_afterNonce_owner, permitNonceEvaledRef, permitOwnerValue, permitOwnerKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem storageTypeAt_permit_nonce (I : ExecutionEnv) :
    storageTypeAt? contract.storage (permitNonceEvaledRef I) = some uint256St := by
  simp [storageTypeAt?, contract, storageDecls, uint256St, storageTypeStep?]

theorem storageTypeAt_permit_domainSeparator :
    storageTypeAt? contract.storage
      ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) = some bytes32St := by
  simp [storageTypeAt?, contract, storageDecls, bytes32St]

theorem storageLayout_permit_nonce (I : ExecutionEnv) :
    config.storage.layout (permitNonceEvaledRef I) =
      fun _ => some (wordLoc (permitNonceStorageSlot I)) := by
  rfl

theorem storageLayout_permit_domainSeparator :
    config.storage.layout ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) =
      fun _ => some (bytes32Loc ⟨3⟩) := by
  rfl

theorem resolveStorageRef_permit_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config { contract := contract, locals := permitStore I } evm
      domainSeparatorRef =
        .ok (({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef), bytes32St) := by
  exact resolveStorageRef?_ok
    (permitStore_domainSeparatorRef I)
    (evalStorageRef_permit_domainSeparator evm I)
    storageTypeAt_permit_domainSeparator

theorem resolveStorageRef_permit_afterNonce_nonce (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I, uint256St) := by
  exact resolveStorageRef?_ok
    (permitAfterNonceLoadStore_nonces evm I)
    (evalStorageRef_permit_afterNonce_nonce evm I)
    (storageTypeAt_permit_nonce I)

theorem resolveStorageRef_permit_afterDomain_nonce (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config
      { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I, uint256St) := by
  exact resolveStorageRef?_ok
    (permitAfterDomainLoadStore_nonces evm I)
    (evalStorageRef_permit_afterDomain_nonce evm I)
    (storageTypeAt_permit_nonce I)

theorem evalExpr_permit_domainSeparator_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.storage domainSeparatorRef) = .ok (permitDomainSeparatorLoadedValue evm) := by
  exact evalExpr_storage_scalar_value
      (er := ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef))
      (t := .bytes bytes32Width)
      (loc := bytes32Loc ⟨3⟩)
      (hbase := permitStore_domainSeparatorRef I)
      (her := evalStorageRef_permit_domainSeparator evm I)
      (hty := storageTypeAt_permit_domainSeparator)
      (hloc := storageLayout_permit_domainSeparator)
      (hload := by
        rw [uniswapStorageLocLoad_bytes32]
        simp [permitDomainSeparatorLoadedValue, permitWordBytes32Value, bytes32Width])

theorem evalExpr_permit_nonce_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.storage (noncesRef (.var "owner"))) = .ok (permitNonceLoadedValue evm I) := by
  exact evalExpr_storage_scalar_value
      (er := permitNonceEvaledRef I) (t := .int uint256Int)
      (loc := wordLoc (permitNonceStorageSlot I))
      (hbase := permitStore_nonces I)
      (her := evalStorageRef_permit_nonce evm I)
      (hty := storageTypeAt_permit_nonce I)
      (hloc := storageLayout_permit_nonce I)
      (hload := by
        rw [uniswapStorageLocLoad_uint256])

theorem evalExpr_permit_afterDomain_nonce_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (.storage (noncesRef (.var "owner"))) = .ok (permitNonceLoadedValue evm I) := by
  exact evalExpr_storage_scalar_value
      (er := permitNonceEvaledRef I) (t := .int uint256Int)
      (loc := wordLoc (permitNonceStorageSlot I))
      (hbase := permitAfterDomainLoadStore_nonces evm I)
      (her := evalStorageRef_permit_afterDomain_nonce evm I)
      (hty := storageTypeAt_permit_nonce I)
      (hloc := storageLayout_permit_nonce I)
      (hload := by
        rw [uniswapStorageLocLoad_uint256])

theorem evalExpr_permit_nonce_next (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (wrapU256 (.binary .add (.var "nonce") (.intLit 1))) =
        .ok (permitNonceNextLoadedValue evm I) := by
  have hone : (⟨1⟩ : UInt256).toNat = 1 := by native_decide
  unfold wrapU256 permitNonceNextLoadedValue permitNonceNextLoadedWord permitNonceLoadedWord
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [permitAfterNonceLoadStore_nonce]
  simp only [evalBinaryOp?]
  rw [uadd_toNat, hone]
  simp [twoPow256, UInt256.size]

theorem permitAssignNonce (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      .storage (noncesRef (.var "owner")) (permitNonceNextLoadedValue evm I) =
        .ok ({ contract := contract, locals := permitAfterNonceLoadStore evm I },
          permitAfterNonceState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_permit_afterNonce_nonce, EvalResult.bind, bind,
    EvalResult.ofOption, storageLayout_permit_nonce I, pure]
  rw [uniswapStorageLocStore_uint256]
  simp [permitAfterNonceState]

theorem permitNonceLoadedWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitNonceLoadedWord (initState cA gh bl σ σ₀ g A I) I = permitNonceWord σ I := by
  unfold permitNonceLoadedWord permitNonceWord
  rw [permitNonceStorageSlot_eq_mapSlot_masked]
  simpa [initState] using
    (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (slot := mapSlot (permitOwnerMaskedWord I) ⟨4⟩))

theorem permitNonceNextLoadedWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitNonceNextLoadedWord (initState cA gh bl σ σ₀ g A I) I =
      permitNonceNextWord σ I := by
  simp [permitNonceNextLoadedWord, permitNonceNextWord, permitNonceLoadedWord_initState]

theorem permitAfterNonceState_init_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
      permitAfterNonceAccountMap σ I := by
  unfold permitAfterNonceState permitAfterNonceAccountMap
  rw [storageStore_accountMap]
  rw [permitNonceStorageSlot_eq_mapSlot_masked]
  rw [permitNonceNextLoadedWord_initState]
  simp [initState]

theorem permitAfterNonceState_init_createdAccounts {cA gh bl σ σ₀ A I} {g : Sat256} :
    (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I).createdAccounts = cA := by
  simp [permitAfterNonceState, storageStore_createdAccounts, initState]

theorem permitAfterNonceAccountMap_equiv {σ_evm σ_solm I}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (permitAfterNonceAccountMap σ_evm I)
      (permitAfterNonceAccountMap σ_solm I) := by
  have hword : permitNonceWord σ_evm I = permitNonceWord σ_solm I := by
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (mapSlot (permitOwnerMaskedWord I) ⟨4⟩) ⟨0⟩
  have hnext : permitNonceNextWord σ_evm I = permitNonceNextWord σ_solm I := by
    simp [permitNonceNextWord, hword]
  rw [permitAfterNonceAccountMap, permitAfterNonceAccountMap, hnext]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner (mapSlot (permitOwnerMaskedWord I) ⟨4⟩)
    (permitNonceNextWord σ_solm I) hAccounts

theorem evalExpr_permit_deadline_ge_now_false (evm : EVM.State) (I : ExecutionEnv)
    (hexpired : (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.binary .ge (.var "deadline") now) = .ok (.bool false) := by
  have hltInt :
      Int.ofNat (permitDeadlineWord I).toNat <
        Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    exact Int.ofNat_lt.mpr hexpired
  have hnot :
      ¬ Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        Int.ofNat (permitDeadlineWord I).toNat :=
    not_le_of_gt hltInt
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [permitStore_deadline]
  simpa [permitDeadlineValue, now, evalExpr?, pure, envValue, evalBinaryOp?] using hnot

theorem evalExpr_permit_deadline_ge_now_true (evm : EVM.State) (I : ExecutionEnv)
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.binary .ge (.var "deadline") now) = .ok (.bool true) := by
  have hleNat :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (permitDeadlineWord I).toNat := by
    omega
  have hleInt :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        Int.ofNat (permitDeadlineWord I).toNat :=
    Int.ofNat_le.mpr hleNat
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [permitStore_deadline]
  simpa [permitDeadlineValue, now, evalExpr?, pure, envValue, evalBinaryOp?] using hleInt

abbrev permitDeadlinePrefixBody : List Stmt :=
  nonpayable ++
    [ .require (.binary .ge (.var "deadline") now) ]

abbrev permitAfterDeadlineBody : List Stmt :=
  [ .letDecl "domainSeparator" (some bytes32) (.storage domainSeparatorRef),
    .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
    .assign .storage (noncesRef (.var "owner"))
      (wrapU256 (.binary .add (.var "nonce") (.intLit 1))),
    .letDecl "structHash" (some bytes32) permitStructHashExpr,
    .letDecl "digest" (some bytes32) permitDigestExpr,
    .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
      [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
    .require (.binary .and
      (.binary .ne (.var "recoveredAddress") zeroAddr)
      (.binary .eq (.var "recoveredAddress") (.var "owner"))),
    .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
      "_approveResult" ]

abbrev permitNonceStorePrefixBody : List Stmt :=
  [ .letDecl "domainSeparator" (some bytes32) (.storage domainSeparatorRef),
    .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
    .assign .storage (noncesRef (.var "owner"))
      (wrapU256 (.binary .add (.var "nonce") (.intLit 1))) ]

abbrev permitAfterNonceBody : List Stmt :=
  [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
    .letDecl "digest" (some bytes32) permitDigestExpr,
    .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
      [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
    .require (.binary .and
      (.binary .ne (.var "recoveredAddress") zeroAddr)
      (.binary .eq (.var "recoveredAddress") (.var "owner"))),
    .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
      "_approveResult" ]

theorem execBlock_reverted_append {cfg : Config} {s2 : List Stmt} :
    ∀ {f e s1}, ExecBlock cfg f e s1 .reverted →
      ExecBlock cfg f e (s1 ++ s2) .reverted := by
  intro f e s1
  induction s1 generalizing f e with
  | nil =>
      intro h
      cases h
  | cons stmt rest ih =>
      intro h
      cases h with
      | consNormal hstmt htail =>
          exact ExecBlock.consNormal hstmt (ih htail)
      | consRevert hstmt =>
          exact ExecBlock.consRevert hstmt

theorem uniswapPermitHashPrefixAt {base cur : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr ]
      (.ok { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl hstruct) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl hdigest) ExecBlock.nil

theorem uniswapPermitHashEcrecoverSuccessAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered]) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }) cur') := by
  have hhash := uniswapPermitHashPrefixAt (base := base) (cur := cur)
    (I := I) hstruct hdigest
  have hecrecover := uniswapPermitEcrecoverCallSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hcall hdec
  have hblock := execBlock_append hhash hecrecover
  simpa using hblock

theorem uniswapPermitHashEcrecoverFailureAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, cur', out) false) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  have hhash := uniswapPermitHashPrefixAt (base := base) (cur := cur)
    (I := I) hstruct hdigest
  have hecrecover := uniswapPermitEcrecoverCallFailureAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hcall
  have hblock := execBlock_append hhash hecrecover
  simpa using hblock

theorem uniswapPermitHashEcrecoverDecodeRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  have hhash := uniswapPermitHashPrefixAt (base := base) (cur := cur)
    (I := I) hstruct hdigest
  have hecrecover := uniswapPermitEcrecoverCallDecodeRevertAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hcall hdec
  have hblock := execBlock_append hhash hecrecover
  simpa using hblock

theorem uniswapPermitHashEcrecoverRequireSuccessAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hnz : recovered ≠ .address (AccountAddress.ofNat 0))
    (heq : recovered = permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
        .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }) cur') := by
  have hprefix := uniswapPermitHashEcrecoverSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec
  have hrequire :
      ExecBlock config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered } cur'
        [ .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
        (.ok
          { contract := contract,
            locals := permitAfterEcrecoverStore base I structHash digest recovered } cur') := by
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_permit_afterEcrecover_require_true base cur' I structHash digest recovered
          hnz heq))
      ExecBlock.nil
  have hblock := execBlock_append hprefix hrequire
  simpa using hblock

theorem uniswapPermitHashEcrecoverRequireZeroRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hzero : recovered = .address (AccountAddress.ofNat 0)) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
        .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
      .reverted := by
  have hprefix := uniswapPermitHashEcrecoverSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec
  have hrequire :
      ExecBlock config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered } cur'
        [ .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_permit_afterEcrecover_require_false_zero base cur' I structHash digest
          recovered hzero))
  have hblock := execBlock_append hprefix hrequire
  simpa using hblock

theorem uniswapPermitHashEcrecoverRequireMismatchRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    {recoveredAddr : AccountAddress}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (haddr : recovered = .address recoveredAddr)
    (hnz : recoveredAddr ≠ AccountAddress.ofNat 0)
    (hne : .address recoveredAddr ≠ permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
        .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
      .reverted := by
  have hprefix := uniswapPermitHashEcrecoverSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec
  have hrequire :
      ExecBlock config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered } cur'
        [ .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_permit_afterEcrecover_require_false_mismatch base cur' I structHash digest
          recovered recoveredAddr haddr hnz hne))
  have hblock := execBlock_append hprefix hrequire
  simpa using hblock

theorem uniswapPermitAfterNonceSuccessAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hnz : recovered ≠ .address (AccountAddress.ofNat 0))
    (heq : recovered = permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterApproveStore base I structHash digest recovered })
        (permitApprovePostState cur' I)) := by
  have hprefix := uniswapPermitHashEcrecoverRequireSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec hnz heq
  have happ := uniswapPermitApproveCallSuccessAt (base := base) (cur := cur')
    (I := I) (structHash := structHash) (digest := digest) (recovered := recovered)
  have hblock := execBlock_append hprefix happ
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceEcrecoverFailureAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, cur', out) false) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverFailureAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hstruct hdigest hcall
  have hblock := execBlock_reverted_append
    (s2 := [
      .require (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))),
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceEcrecoverDecodeRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverDecodeRevertAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hstruct hdigest hcall hdec
  have hblock := execBlock_reverted_append
    (s2 := [
      .require (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))),
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceRequireZeroRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hzero : recovered = .address (AccountAddress.ofNat 0)) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverRequireZeroRevertAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec hzero
  have hblock := execBlock_reverted_append
    (s2 := [
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceRequireMismatchRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    {recoveredAddr : AccountAddress}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (haddr : recovered = .address recoveredAddr)
    (hnz : recoveredAddr ≠ AccountAddress.ofNat 0)
    (hne : .address recoveredAddr ≠ permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverRequireMismatchRevertAt (base := base)
    (cur := cur) (cur' := cur') (I := I) (structHash := structHash)
    (digest := digest) (recovered := recovered) (out := out)
    (recoveredAddr := recoveredAddr) hstruct hdigest hcall hdec haddr hnz hne
  have hblock := execBlock_reverted_append
    (s2 := [
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitNonceStorePrefix (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitNonceStorePrefixBody
      (.ok { contract := contract, locals := permitAfterNonceLoadStore evm I }
        (permitAfterNonceState evm I)) := by
  change ExecBlock config { contract := contract, locals := permitStore I } evm
    [ .letDecl "domainSeparator" (some bytes32) (.storage domainSeparatorRef),
      .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
      .assign .storage (noncesRef (.var "owner"))
        (wrapU256 (.binary .add (.var "nonce") (.intLit 1))) ]
    (.ok { contract := contract, locals := permitAfterNonceLoadStore evm I }
      (permitAfterNonceState evm I))
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_permit_domainSeparator_storage evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_permit_afterDomain_nonce_storage evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_permit_nonce_next evm I) (permitAssignNonce evm I))
    ExecBlock.nil

theorem uniswapPermitBlockAfterNonce {evm : EVM.State} {I : ExecutionEnv} {result}
    (hrest : ExecBlock config
      { contract := contract, locals := permitAfterNonceLoadStore evm I }
      (permitAfterNonceState evm I) permitAfterNonceBody result) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitAfterDeadlineBody result := by
  have hblock := execBlock_append (uniswapPermitNonceStorePrefix evm I) hrest
  simpa [permitAfterDeadlineBody, permitNonceStorePrefixBody, permitAfterNonceBody] using hblock

theorem uniswapPermitDeadlinePrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitDeadlinePrefixBody
      (.ok { contract := contract, locals := permitStore I } evm) := by
  change ExecBlock config { contract := contract, locals := permitStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .ge (.var "deadline") now) ]
    (.ok { contract := contract, locals := permitStore I } evm)
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_permit_deadline_ge_now_true evm I hnotExpired))
    ExecBlock.nil

theorem uniswapPermitBlockAfterDeadline {evm : EVM.State} {I : ExecutionEnv} {result}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hrest : ExecBlock config { contract := contract, locals := permitStore I } evm
      permitAfterDeadlineBody result) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitTransition.body result := by
  have hblock := execBlock_append
    (uniswapPermitDeadlinePrefix evm I hwv hnotExpired) hrest
  simpa [permitTransition, permitDeadlinePrefixBody, permitAfterDeadlineBody] using hblock

theorem uniswapPermitX_expired {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hexpired : (permitDeadlineWord I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5473⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5473⟩ := hdecoded
  have hlt :
      UInt256.lt (permitDeadlineWord I) (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    exact ult_one hexpired
  have rd5477₀ := evm_run rd5473 with [jumpdest, timestamp, dup5, lt]
  have rd5477 := rd5477₀
  rw [hlt] at rd5477
  have rd5482 := evm_run rd5477 with [iszero, push2 ⟨5547⟩, jumpiNT (by decide)]
  exact RD.solcErrorStringRevertTail
    (pc := ⟨5482⟩) (len := ⟨18⟩)
    (rawWord := (⟨1860528883258986746185044576161230704906577⟩ : UInt256))
    (shift := ⟨114⟩)
    (word := UInt256.shiftLeft
      (⟨1860528883258986746185044576161230704906577⟩ : UInt256) ⟨114⟩)
    (op := .PUSH18) (width := 18)
    rd5482
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapPermitX_deadlineOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5473⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5547⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd5473⟩ := hdecoded
  have hle : (UInt256.ofNat I.header.timestamp).toNat ≤ (permitDeadlineWord I).toNat := by
    omega
  have hlt : UInt256.lt (permitDeadlineWord I) (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    exact ult_zero hle
  have rd5477₀ := evm_run rd5473 with [jumpdest, timestamp, dup5, lt]
  have rd5477 := rd5477₀
  rw [hlt] at rd5477
  have rd5547 := evm_run rd5477 with [iszero, push2 ⟨5547⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, rd5547⟩

theorem uniswapPermitX_nonceStored {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hdeadlineOk : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5547⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5589⟩
      [permitNonceWord σ I, ⟨1⟩, ⟨64⟩, ⟨32⟩, ⟨0⟩, permitOwnerMaskedWord I,
        solcAddrMask, permitDomainSeparatorWord σ I, permitSWord I, permitRWord I,
        permitVWord I, permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitNonceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C := by
  obtain ⟨_, _, rd5547⟩ := hdeadlineOk
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hownerMask :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have rd5550 := evm_run rd5547 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd5551⟩ := rd5550.sload (by decide) (by evm_ov)
  have rd5561₀ := evm_run rd5551 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup10, and]
  have rd5561 := rd5561₀
  rw [hmask, hownerMask] at rd5561
  have rd5579 := evm_run rd5561 with [
    push1 ⟨0⟩, dup2, dup2,
    raw mstore 0 (wordAt0Mem (permitOwnerMaskedWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (permitNonceHashMem I)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (mapSlot (permitOwnerMaskedWord I) ⟨4⟩)
      (UInt256.ofNat 3) (by decide) mem_cost
      (permitNonceKeccakSlot I) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd5581⟩ := rd5579.sload (by decide) (by evm_ov)
  have rd5588 := evm_run rd5581 with [push1 ⟨1⟩, dup1, dup3, add, swap1, swap3]
  obtain ⟨_, _, rd5589⟩ := rd5588.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [permitDomainSeparatorWord, permitNonceWord, permitNonceNextWord,
      permitAfterNonceAccountMap, codeOwnerStorageWord] using rd5589⟩

theorem uniswapPermitX_structHashed {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hnonceEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5589⟩
      [permitNonceWord σ I, ⟨1⟩, ⟨64⟩, ⟨32⟩, ⟨0⟩, permitOwnerMaskedWord I,
        solcAddrMask, permitDomainSeparatorWord σ I, permitSWord I, permitRWord I,
        permitVWord I, permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitNonceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5688⟩
      [permitStructHashWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩,
        permitDomainSeparatorWord σ I, permitSWord I, permitRWord I, permitVWord I,
        permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitStructHashMem σ I) (UInt256.ofNat 11) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C := by
  obtain ⟨_, _, rd5589⟩ := hnonceEvm
  have hspenderMask :
      UInt256.land (permitSpenderMaskedWord I) solcAddrMask = permitSpenderMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitSpenderMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitSpenderWord I)
  obtain ⟨_, _, rd5688⟩ := RD.uniswapPermitStructHash
    (nonce := permitNonceWord σ I) (owner := permitOwnerMaskedWord I)
    (spender := permitSpenderMaskedWord I) (value := permitValueWord I)
    (deadline := permitDeadlineWord I) (domain := permitDomainSeparatorWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5589
    (permitNonceHashMem_size I) (permitNonceHashMem_read64 I) hspenderMask
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [permitStructHashWord, permitStructHashMem, permitStructHashLenMem,
      permitStructHashDataMem, permitStructHashDataWrites, permitTypehashWord] using rd5688⟩

theorem uniswapPermitX_digestHashed {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hstructEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5688⟩
      [permitStructHashWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩,
        permitDomainSeparatorWord σ I, permitSWord I, permitRWord I, permitVWord I,
        permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitStructHashMem σ I) (UInt256.ofNat 11) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5746⟩
      [permitDigestWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨450⟩,
        permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitDigestMem σ I) (UInt256.ofNat 15) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C := by
  obtain ⟨_, _, rd5688⟩ := hstructEvm
  have hbaseSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseRead64 :
      (permitStructHashMem σ I).readWithPadding 64 32 =
        UInt256.toByteArray (⟨352⟩ : UInt256) := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_read64 (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  obtain ⟨_, _, rd5746⟩ := RD.uniswapPermitDigestHash
    (structHash := permitStructHashWord σ I) (domain := permitDomainSeparatorWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5688 hbaseSize hbaseRead64
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [permitDigestWord, permitDigestMem] using rd5746⟩

theorem uniswapPermitX_ecrecoverStaticcallMade
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdigestEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5746⟩
      [permitDigestWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨450⟩,
        permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitDigestMem σ I) (UInt256.ofNat 15) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k C
      ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd5746⟩ := hdigestEvm
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ :=
    RD.uniswapPermitEcrecoverStaticcallMade
      (digest := permitDigestWord σ I) (s := permitSWord I) (r := permitRWord I)
      (v := permitVWord I) (deadline := permitDeadlineWord I)
      (value := permitValueWord I) (spender := permitSpenderMaskedWord I)
      (owner := permitOwnerMaskedWord I) (ret := ⟨570⟩) (R := [sel])
      rd5746 hbaseSize (permitVWord_mask_left I) hdepth
      (by simp only [List.length_singleton]; omega)
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, ?_, ?_, hoSize⟩
  · simpa [initState, permitEcrecoverInputMem] using hΘ
  · simpa [permitEcrecoverInputMem, permitEcrecoverStaticcallMem] using rd5814

theorem uniswapPermitX_ecrecoverStaticcallDepthReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdigestEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5746⟩
      [permitDigestWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨450⟩,
        permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitDigestMem σ I) (UInt256.ofNat 15) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C)
    (hdepth : I.depth = 1024) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5746⟩ := hdigestEvm
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  exact RD.uniswapPermitEcrecoverStaticcallDepthReverts
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5746 hbaseSize (permitVWord_mask_left I) hdepth
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverStatusAndReturnDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hstatic : ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k C
      ∧ o.size < UInt256.size) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ (z = false →
        RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I))
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
            permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
            permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
            permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ := hstatic
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, ?_, hoSize⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz ho32
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd5832⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨5830⟩) rd5814 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
      simpa [permitStructHashMem] using
        permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
          (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
          (permitNonceHashMem_size I)
    have hbaseSize : (permitDigestMem σ I).size = 450 := by
      simpa [permitDigestMem] using
        permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
          hstructMemSize
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecoded
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize ho32 hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩

theorem uniswapPermitX_ecrecoverStatusAndReturnDecodedAll
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hstatic : ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k C
      ∧ o.size < UInt256.size) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ (z = false →
        RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I))
      ∧ (z = true → o.size < 32 →
        ∃ k' C', RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
            permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
            permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
            permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k' C')
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
            permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
            permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
            permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ := hstatic
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  have hguardOk : z = true → ∃ k' C', RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: permitDigestWord σ I :: permitSWord I ::
        permitRWord I :: permitVWord I :: permitDeadlineWord I :: permitValueWord I ::
        permitSpenderMaskedWord I :: permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k' C' := by
    intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    exact RD.solcCallSuccessGuardOk (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, ?_, ?_, hoSize⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz hshort
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecodedShort
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize hshort hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩
  · intro hz ho32
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecoded
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize ho32 hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩

theorem uniswapPermitX_ecrecoverStatusAndReturnDecodedAllAt
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {k C : ℕ}
    (rd5814 : RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
      [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
        permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
        permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hoSize : o.size < UInt256.size) :
    (z = false →
      RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I))
    ∧ (z = true → o.size < 32 →
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
        (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
          permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
          permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
          permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
        (permitEcrecoverStaticcallMem σ I o)
        (UInt256.ofNat 20) o (cA', σ') k' C')
    ∧ (z = true → 32 ≤ o.size →
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
        (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
          permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
          permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
          permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
        (permitEcrecoverStaticcallMem σ I o)
        (UInt256.ofNat 20) o (cA', σ') k' C') := by
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  have hguardOk : z = true → ∃ k' C', RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: permitDigestWord σ I :: permitSWord I ::
        permitRWord I :: permitVWord I :: permitDeadlineWord I :: permitValueWord I ::
        permitSpenderMaskedWord I :: permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k' C' := by
    intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    exact RD.solcCallSuccessGuardOk (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz hshort
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecodedShort
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize hshort hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩
  · intro hz ho32
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecoded
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize ho32 hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩

theorem uniswapPermitEcrecoverTypedCall_source
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth.val < 1024)
    (hsz228 : 228 ≤ I.calldata.size)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (cA', σ', g'', A'_evm, z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
        (permitAfterNonceAccountMap σ_evm I) σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
        (toExecute (permitAfterNonceAccountMap σ_evm I)
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128)
        (I.depth + 1) I.header false) :
    ∃ evmCallS : EVM.State,
      typedCallViaEVM config
        (permitAfterNonceState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        (AccountAddress.ofNat 1) "ecrecover" 0
        [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
        (z, evmCallS, o) false ∧
      accountMapEquiv σ' evmCallS.accountMap ∧
      evmCallS.createdAccounts = cA' ∧
      evmCallS.σ₀ = σ₀ ∧
      evmCallS.genesisBlockHeader = gh ∧
      evmCallS.blocks = bl ∧
      evmCallS.executionEnv = I := by
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let evmE : EVM.State :=
    { evmNonceS with
      accountMap := permitAfterNonceAccountMap σ_evm I
      createdAccounts := cA
      σ₀ := σ₀
      genesisBlockHeader := gh
      blocks := bl
      executionEnv := I }
  have hdepthE : evmE.executionEnv.depth.val < 1024 := by
    simpa [evmE] using hdepth
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepthE
    exact absurd hdepthE (by decide)
  have hdigestEq : permitDigestWord σ_evm I = permitDigestWord σ_solm I :=
    permitDigestWord_equiv hAccounts
  have hreadEq :
      (permitEcrecoverInputMem σ_solm I).readWithPadding 482 128 =
        (permitEcrecoverInputMem σ_evm I).readWithPadding 482 128 := by
    rw [permitEcrecoverInputMem_read482_128, permitEcrecoverInputMem_read482_128,
      hdigestEq]
  have hcdE :
      config.externalABI.encode? "ecrecover"
          [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I] =
        some ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128) := by
    have hcd := uniswapEcrecoverEncode_eq σ_solm I hsz228
    rwa [hreadEq] at hcd
  have hΘE :
      (cA', σ', g'', A'_evm, z, o) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
          evmE.createdAccounts evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header false := by
    simpa [evmE] using hΘeq
  have hStateAccounts : accountMapEquiv evmE.accountMap evmNonceS.accountMap := by
    rw [show evmNonceS.accountMap = permitAfterNonceAccountMap σ_solm I from by
      simpa [evmNonceS, evmS] using
        (permitAfterNonceState_init_accountMap
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g))]
    simpa [evmE] using permitAfterNonceAccountMap_equiv hAccounts
  obtain ⟨σS, AS, hcallSolm, hPost⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmNonceS)
      (tgt := AccountAddress.ofNat 1) (targetWord := (⟨1⟩ : UInt256))
      (name := "ecrecover")
      (args := [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I])
      (cA' := cA') (σ' := σ') (A' := A'_evm) (A_in := A_in)
      (z := z) (out := o) (g'' := g'') (callGas := callGas)
      (mem := permitEcrecoverInputMem σ_evm I) (inOff := ⟨482⟩) (inSize := ⟨128⟩)
      (callPerm := false)
      hdepthNe rfl hcdE hΘE
      hStateAccounts
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_sigma0,
        initState])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState_init_createdAccounts])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState,
        permitStorageStore_genesisBlockHeader, initState])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_blocks,
        initState])
      (by simp [evmE])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState, storageStore_executionEnv,
        initState])
  let evmCallS : EVM.State :=
    { evmNonceS with accountMap := σS, substate := AS, createdAccounts := cA' }
  refine ⟨evmCallS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [evmCallS] using hcallSolm
  · simpa [evmCallS] using hPost
  · simp [evmCallS]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_sigma0,
      initState]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState,
      permitStorageStore_genesisBlockHeader, initState]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_blocks,
      initState]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState, storageStore_executionEnv,
      initState]

theorem uniswapPermitEcrecoverStaticcallTyped_source
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth.val < 1024)
    (hsz228 : 228 ≤ I.calldata.size)
    (hstatic : ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ_evm I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ_evm I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ_evm I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ_evm I o)
          (UInt256.ofNat 20) o (cA', σ') k C
  ∧ o.size < UInt256.size) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (k C : ℕ) (evmCallS : EVM.State),
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5814⟩
        [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
          permitDigestWord σ_evm I, permitSWord I, permitRWord I, permitVWord I,
          permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
          permitOwnerMaskedWord I, ⟨570⟩, sel]
        (permitEcrecoverStaticcallMem σ_evm I o)
        (UInt256.ofNat 20) o (cA', σ') k C
      ∧ typedCallViaEVM config
          (permitAfterNonceState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
          (AccountAddress.ofNat 1) "ecrecover" 0
          [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
          (z, evmCallS, o) false
      ∧ accountMapEquiv σ' evmCallS.accountMap
      ∧ evmCallS.createdAccounts = cA'
      ∧ evmCallS.σ₀ = σ₀
      ∧ evmCallS.genesisBlockHeader = gh
      ∧ evmCallS.blocks = bl
      ∧ evmCallS.executionEnv = I
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ := hstatic
  obtain ⟨evmCallS, hcall, hPost, hcreated, hσ0, hgenesis, hblocks, henv⟩ :=
    uniswapPermitEcrecoverTypedCall_source (g := g) hAccounts hdepth hsz228 hΘ
  exact ⟨cA', σ', z, o, k, C, evmCallS, rd5814, hcall, hPost,
    hcreated, hσ0, hgenesis, hblocks, henv, hoSize⟩

theorem uniswapPermitX_ecrecoverSignatureGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmatch : UInt256.land recovered solcAddrMask = permitOwnerMaskedWord I) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5965⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  have hownerClean :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hmatchRuntime :
      UInt256.land recovered solcAddrMask =
        UInt256.land (permitOwnerMaskedWord I) solcAddrMask := by
    rw [hownerClean]
    exact hmatch
  obtain ⟨k', C', rd5965⟩ :=
    RD.uniswapPermitEcrecoverSignatureGuardOk
      (digest := permitDigestWord σ I)
      (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
      (deadline := permitDeadlineWord I) (value := permitValueWord I)
      (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
      (ret := ⟨570⟩) (R := [sel]) rd5844 hnz hmatchRuntime
      (by simp only [List.length_singleton]; omega)
  exact ⟨k', C', by
    simpa [permitEcrecoverStaticcallMem] using rd5965⟩

theorem uniswapPermitX_approveAndReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hok : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5965⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hperm : I.perm = true)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner σ'
        (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
        (permitValueWord I))
      ByteArray.empty := by
  obtain ⟨_, _, rd5965⟩ := hok
  have hmem :
      514 ≤ (permitEcrecoverStaticcallMem σ I o).size := by
    have hs := permitRuntimeEcrecoverStaticcallMem_size_of_size_ge
      (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
      (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
      (permitDigestMem_size σ I) ho32 hoSize
    rw [permitEcrecoverStaticcallMem, hs]
    omega
  have hfree :
      (permitEcrecoverStaticcallMem σ I o).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [permitEcrecoverStaticcallMem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_ge
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
        (permitDigestMem_size σ I) ho32 hoSize
  have hcanonOwner : (permitOwnerMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hcanonSpender : (permitSpenderMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitSpenderMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitSpenderWord I)
  exact _root_.UniswapV2Pair.RD.uniswapPermitApproveAndReturn20
    (recovered := recovered) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (R := [sel]) rd5965 hmem hfree hperm hcanonOwner hcanonSpender
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_approveAndReturnShort
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hok : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5965⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hperm : I.perm = true)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner σ'
        (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
        (permitValueWord I))
      ByteArray.empty := by
  obtain ⟨_, _, rd5965⟩ := hok
  have hmem :
      514 ≤ (permitEcrecoverStaticcallMem σ I o).size := by
    have hs := permitRuntimeEcrecoverStaticcallMem_size_of_size_lt
      (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
      (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
      (permitDigestMem_size σ I) hshort hoSize
    rw [permitEcrecoverStaticcallMem, hs]
    omega
  have hfree :
      (permitEcrecoverStaticcallMem σ I o).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [permitEcrecoverStaticcallMem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_lt
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
        (permitDigestMem_size σ I) hshort hoSize
  have hcanonOwner : (permitOwnerMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hcanonSpender : (permitSpenderMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitSpenderMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitSpenderWord I)
  exact _root_.UniswapV2Pair.RD.uniswapPermitApproveAndReturn20
    (recovered := recovered) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (R := [sel]) rd5965 hmem hfree hperm hcanonOwner hcanonSpender
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardZeroReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  exact RD.uniswapPermitEcrecoverSignatureGuardZeroReverts
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hzero (permitDigestMem_size σ I) ho32 hoSize
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardZeroRevertsShort
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  exact RD.uniswapPermitEcrecoverSignatureGuardZeroRevertsShort
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hzero (permitDigestMem_size σ I) hshort hoSize
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardMismatchReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ permitOwnerMaskedWord I)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  have hownerClean :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hmismatchRuntime :
      UInt256.land recovered solcAddrMask ≠
        UInt256.land (permitOwnerMaskedWord I) solcAddrMask := by
    intro hsame
    apply hmismatch
    rwa [hownerClean] at hsame
  exact RD.uniswapPermitEcrecoverSignatureGuardMismatchReverts
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hnz hmismatchRuntime
    (permitDigestMem_size σ I) ho32 hoSize
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardMismatchRevertsShort
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ permitOwnerMaskedWord I)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  have hownerClean :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hmismatchRuntime :
      UInt256.land recovered solcAddrMask ≠
        UInt256.land (permitOwnerMaskedWord I) solcAddrMask := by
    intro hsame
    apply hmismatch
    rwa [hownerClean] at hsame
  exact RD.uniswapPermitEcrecoverSignatureGuardMismatchRevertsShort
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hnz hmismatchRuntime
    (permitDigestMem_size σ I) hshort hoSize
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitBodyCoreOk_afterNonce
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ_solm I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ_solm I) }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ_solm I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
        permitDigestWord σ_evm I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ_evm I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hAccountsCall : accountMapEquiv σ' evmCallS.accountMap)
    (hcreatedCall : evmCallS.createdAccounts = cA')
    (henvCall : evmCallS.executionEnv = I)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        ⟨0⟩)
    (hmatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask =
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_ok (returndata := o) ho32
  have hnzSource : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredAddress_ne_zero_of_mask_ne_zero ho32 hnz
  have hmatchSource : recoveredValue = permitOwnerValue I := by
    simpa [recoveredValue] using permitRecoveredAddress_eq_owner_of_mask_eq ho32 hmatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitAfterNonceSuccessAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ_solm I)
      (digest := permitDigestValue σ_solm I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hnzSource hmatchSource
  have hafterNonce :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitAfterDeadlineBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterNonce (evm := evmS) (I := I) hrest
  have hblock :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitTransition.body
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterDeadline (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hafterNonce
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (permitStore I)
        permitTransition.body
        (.returned (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I) none) := by
    simpa [evmS, ExecTransitionBody] using ExecFuncBody.execBlockOK hblock
  have hok := uniswapPermitX_ecrecoverSignatureGuardOk
    (g := Sat256.ofUInt256 g) hdecoded hnz hmatch
  have rdRet := uniswapPermitX_approveAndReturn
    (g := Sat256.ofUInt256 g) hok hperm ho32 hoSize
  have hcreated :
      (cA', sstoreAccountMap I.codeOwner σ'
        (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
        (permitValueWord I)).1 =
        (permitApprovePostState evmCallS I).createdAccounts := by
    simp [permitApprovePostState_createdAccounts, hcreatedCall]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ'
          (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
          (permitValueWord I))
        (permitApprovePostState evmCallS I).accountMap :=
    permitApprovePostState_accountMap_equiv (evm := evmCallS) (I := I) (σ := σ')
      henvCall hAccountsCall
  exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
    (uniswapDecode_permit_ok hsz228) hbody hcreated hAccountsPost
    (returnEquiv.fallthrough rfl rfl (by native_decide))

theorem uniswapPermitBodyCoreOk_afterNonce_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ_solm I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ_solm I) }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ_solm I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        permitDigestWord σ_evm I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ_evm I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hAccountsCall : accountMapEquiv σ' evmCallS.accountMap)
    (hcreatedCall : evmCallS.createdAccounts = cA')
    (henvCall : evmCallS.executionEnv = I)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hmatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask =
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_padded (returndata := o)
  have hnzSource : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredPaddedAddress_ne_zero_of_mask_ne_zero hnz
  have hmatchSource : recoveredValue = permitOwnerValue I := by
    simpa [recoveredValue] using permitRecoveredPaddedAddress_eq_owner_of_mask_eq hmatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitAfterNonceSuccessAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ_solm I)
      (digest := permitDigestValue σ_solm I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hnzSource hmatchSource
  have hafterNonce :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitAfterDeadlineBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterNonce (evm := evmS) (I := I) hrest
  have hblock :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitTransition.body
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterDeadline (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hafterNonce
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (permitStore I)
        permitTransition.body
        (.returned (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ_solm I) (permitDigestValue σ_solm I) recoveredValue })
          (permitApprovePostState evmCallS I) none) := by
    simpa [evmS, ExecTransitionBody] using ExecFuncBody.execBlockOK hblock
  have hok := uniswapPermitX_ecrecoverSignatureGuardOk
    (g := Sat256.ofUInt256 g) hdecoded hnz hmatch
  have rdRet := uniswapPermitX_approveAndReturnShort
    (g := Sat256.ofUInt256 g) hok hperm hshort hoSize
  have hcreated :
      (cA', sstoreAccountMap I.codeOwner σ'
        (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
        (permitValueWord I)).1 =
        (permitApprovePostState evmCallS I).createdAccounts := by
    simp [permitApprovePostState_createdAccounts, hcreatedCall]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ'
          (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
          (permitValueWord I))
        (permitApprovePostState evmCallS I).accountMap :=
    permitApprovePostState_accountMap_equiv (evm := evmCallS) (I := I) (σ := σ')
      henvCall hAccountsCall
  exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
    (uniswapDecode_permit_ok hsz228) hbody hcreated hAccountsPost
    (returnEquiv.fallthrough rfl rfl (by native_decide))

theorem uniswapPermitBodyRevertsAfterNonce {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hrest : ExecBlock config
      { contract := contract, locals := permitAfterNonceLoadStore evm I }
      (permitAfterNonceState evm I) permitAfterNonceBody .reverted) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  have hafterNonce := uniswapPermitBlockAfterNonce (evm := evm) (I := I) hrest
  have hblock := uniswapPermitBlockAfterDeadline (evm := evm) (I := I)
    hwv hnotExpired hafterNonce
  exact ExecFuncBody.execBlockRevert hblock

theorem uniswapPermitBodyCoreRevert_ecrecoverFailure_afterNonce
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hrev : RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ_solm I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ_solm I) }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ_solm I))
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
      (false, evmCallS, o) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceEcrecoverFailureAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ_solm I)
      (digest := permitDigestValue σ_solm I) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_zero_afterNonce
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ_solm I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ_solm I) }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ_solm I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
        permitDigestWord σ_evm I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ_evm I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask =
        ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_ok (returndata := o) ho32
  have hzeroSource : recoveredValue = .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredAddress_eq_zero_of_mask_eq_zero ho32 hzero
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireZeroRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ_solm I)
      (digest := permitDigestValue σ_solm I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hzeroSource
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardZeroReverts
    (g := Sat256.ofUInt256 g) hdecoded hzero ho32 hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_mismatch_afterNonce
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ_solm I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ_solm I) }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ_solm I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
        permitDigestWord σ_evm I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ_evm I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        ⟨0⟩)
    (hmismatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredAddr := AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  let recoveredValue : Value := .address recoveredAddr
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue, recoveredAddr] using uniswapEcrecoverDecode_ok (returndata := o) ho32
  have hnzValue : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredAddress_ne_zero_of_mask_ne_zero ho32 hnz
  have hnzAddr : recoveredAddr ≠ AccountAddress.ofNat 0 := by
    intro haddr
    apply hnzValue
    simp [recoveredValue, haddr]
  have hneValue : recoveredValue ≠ permitOwnerValue I := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredAddress_ne_owner_of_mask_ne ho32 hmismatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireMismatchRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ_solm I)
      (digest := permitDigestValue σ_solm I) (recovered := recoveredValue) (out := o)
      (recoveredAddr := recoveredAddr)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec rfl hnzAddr hneValue
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardMismatchReverts
    (g := Sat256.ofUInt256 g) hdecoded hnz hmismatch ho32 hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_zero_afterNonce_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ_solm I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ_solm I) }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ_solm I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        permitDigestWord σ_evm I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ_evm I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask =
        ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_padded (returndata := o)
  have hzeroSource : recoveredValue = .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredPaddedAddress_eq_zero_of_mask_eq_zero hzero
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireZeroRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ_solm I)
      (digest := permitDigestValue σ_solm I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hzeroSource
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardZeroRevertsShort
    (g := Sat256.ofUInt256 g) hdecoded hzero hshort hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_mismatch_afterNonce_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ_solm I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ_solm I) }
        (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ_solm I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        permitDigestWord σ_evm I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ_evm I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hmismatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredAddr := AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))
  let recoveredValue : Value := .address recoveredAddr
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue, recoveredAddr] using uniswapEcrecoverDecode_padded (returndata := o)
  have hnzValue : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredPaddedAddress_ne_zero_of_mask_ne_zero hnz
  have hnzAddr : recoveredAddr ≠ AccountAddress.ofNat 0 := by
    intro haddr
    apply hnzValue
    simp [recoveredValue, haddr]
  have hneValue : recoveredValue ≠ permitOwnerValue I := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredPaddedAddress_ne_owner_of_mask_ne hmismatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireMismatchRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ_solm I)
      (digest := permitDigestValue σ_solm I) (recovered := recoveredValue) (out := o)
      (recoveredAddr := recoveredAddr)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec rfl hnzAddr hneValue
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardMismatchRevertsShort
    (g := Sat256.ofUInt256 g) hdecoded hnz hmismatch hshort hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyReverts_expired (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hexpired : (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [permitTransition] using
    (nonpayableSecondRequireReverts
      (cfg := config) (solm := { contract := contract, locals := permitStore I })
      (evm := evm)
      hwv
      (evalExpr_permit_deadline_ge_now_false evm I hexpired))

theorem uniswapPermitBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 228)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_permit_none_short (I := I) hsz4 hshort
  exact (uniswapPermitX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapPermitBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hshort : I.calldata.size < 228)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
  exact uniswapPermitBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapPermitBodyCoreRevert_expired
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz228 : 228 ≤ I.calldata.size)
    (hexpired : (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmS (permitStore I) permitTransition.body .reverted := by
    exact uniswapPermitBodyReverts_expired evmS I
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hexpired)
  exact (uniswapPermitX_expired (g := Sat256.ofUInt256 g) hexpired
      (uniswapPermitX_decoded_masked (g := Sat256.ofUInt256 g) hsz228 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228) hbody

theorem uniswapPermitBodyRevert_expired
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hexpired : (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
  exact uniswapPermitBodyCoreRevert_expired hcode hsize hwv hsz228 hexpired hdispatch
    (uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapPermitBody_depthOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth.val < 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz228 : 228 ≤ I.calldata.size
  · by_cases hexpired :
      (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat
    · exact uniswapPermitBodyRevert_expired hcode hsize hwv hsel hsz228 hexpired hdispatch
    · have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ_evm) k C :=
        uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      have hdecoded := uniswapPermitX_decoded_masked (g := Sat256.ofUInt256 g)
        hsz228 hsize hreach
      have hdeadlineOk := uniswapPermitX_deadlineOk (g := Sat256.ofUInt256 g)
        hexpired hdecoded
      have hnonceEvm := uniswapPermitX_nonceStored (g := Sat256.ofUInt256 g)
        hperm hdeadlineOk
      have hstructEvm := uniswapPermitX_structHashed (g := Sat256.ofUInt256 g)
        hnonceEvm
      have hdigestEvm := uniswapPermitX_digestHashed (g := Sat256.ofUInt256 g)
        hstructEvm
      obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ :=
        uniswapPermitX_ecrecoverStaticcallMade (g := Sat256.ofUInt256 g) hdigestEvm hdepth
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hstructSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterNonceLoadStore evmS I }
            (permitAfterNonceState evmS I)
            permitStructHashExpr = .ok (permitStructHashValue σ_solm I) := by
        simpa [evmS] using
          (evalExpr_permit_structHash_at
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            (cur := permitAfterNonceState evmS I))
      have hdigestSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterStructHashStore evmS I (permitStructHashValue σ_solm I) }
            (permitAfterNonceState evmS I)
            permitDigestExpr = .ok (permitDigestValue σ_solm I) := by
        simpa [evmS] using
          (evalExpr_permit_digest_afterNonce_at
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g))
      obtain ⟨evmCallS, hcall, hAccountsCall, hcreatedCall, _hσ0, _hgenesis, _hblocks, henv⟩ :=
        uniswapPermitEcrecoverTypedCall_source (g := g) hAccounts hdepth hsz228 hΘ
      obtain ⟨hfailure, hshortDecoded, hlongDecoded⟩ :=
        uniswapPermitX_ecrecoverStatusAndReturnDecodedAllAt rd5814 hoSize
      by_cases hz : z = false
      · have hcallFalse : typedCallViaEVM config
            (permitAfterNonceState evmS I)
            (AccountAddress.ofNat 1) "ecrecover" 0
            [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
            (false, evmCallS, o) false := by
          simpa [evmS, hz] using hcall
        exact uniswapPermitBodyCoreRevert_ecrecoverFailure_afterNonce
          hcode hwv hsz228 hexpired hdispatch (hfailure hz)
          (by simpa [evmS] using hstructSource)
          (by simpa [evmS] using hdigestSource)
          hcallFalse
      · have hzTrue : z = true := by
          cases z <;> simp at hz ⊢
        have hcallTrue : typedCallViaEVM config
            (permitAfterNonceState evmS I)
            (AccountAddress.ofNat 1) "ecrecover" 0
            [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
            (true, evmCallS, o) false := by
          simpa [evmS, hzTrue] using hcall
        by_cases hshort : o.size < 32
        · have hdecodedShort := hshortDecoded hzTrue hshort
          let recovered :=
            UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))
          by_cases hzero : UInt256.land recovered solcAddrMask = ⟨0⟩
          · exact uniswapPermitBodyCoreRevert_zero_afterNonce_short
              hcode hwv hsz228 hexpired hdispatch
              (by simpa [evmS] using hstructSource)
              (by simpa [evmS] using hdigestSource)
              (by simpa [recovered] using hdecodedShort)
              hcallTrue hshort hoSize
              (by simpa [recovered] using hzero)
          · by_cases hmatch : UInt256.land recovered solcAddrMask = permitOwnerMaskedWord I
            · exact uniswapPermitBodyCoreOk_afterNonce_short
                hcode hperm hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedShort)
                hcallTrue hAccountsCall hcreatedCall henv hshort hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
            · exact uniswapPermitBodyCoreRevert_mismatch_afterNonce_short
                hcode hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedShort)
                hcallTrue hshort hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
        · have ho32 : 32 ≤ o.size := by omega
          have hdecodedLong := hlongDecoded hzTrue ho32
          let recovered := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
          by_cases hzero : UInt256.land recovered solcAddrMask = ⟨0⟩
          · exact uniswapPermitBodyCoreRevert_zero_afterNonce
              hcode hwv hsz228 hexpired hdispatch
              (by simpa [evmS] using hstructSource)
              (by simpa [evmS] using hdigestSource)
              (by simpa [recovered] using hdecodedLong)
              hcallTrue ho32 hoSize
              (by simpa [recovered] using hzero)
          · by_cases hmatch : UInt256.land recovered solcAddrMask = permitOwnerMaskedWord I
            · exact uniswapPermitBodyCoreOk_afterNonce
                hcode hperm hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedLong)
                hcallTrue hAccountsCall hcreatedCall henv ho32 hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
            · exact uniswapPermitBodyCoreRevert_mismatch_afterNonce
                hcode hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedLong)
                hcallTrue ho32 hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
  · exact uniswapPermitBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

theorem uniswapPermitBody_depthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hdepth : I.depth = 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz228 : 228 ≤ I.calldata.size
  · by_cases hexpired :
      (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat
    · exact uniswapPermitBodyRevert_expired hcode hsize hwv hsel hsz228 hexpired hdispatch
    · have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ_evm) k C :=
        uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      have hdecoded := uniswapPermitX_decoded_masked (g := Sat256.ofUInt256 g)
        hsz228 hsize hreach
      have hdeadlineOk := uniswapPermitX_deadlineOk (g := Sat256.ofUInt256 g)
        hexpired hdecoded
      have hnonceEvm := uniswapPermitX_nonceStored (g := Sat256.ofUInt256 g)
        hperm hdeadlineOk
      have hstructEvm := uniswapPermitX_structHashed (g := Sat256.ofUInt256 g)
        hnonceEvm
      have hdigestEvm := uniswapPermitX_digestHashed (g := Sat256.ofUInt256 g)
        hstructEvm
      have hrev := uniswapPermitX_ecrecoverStaticcallDepthReverts
        (g := Sat256.ofUInt256 g) hdigestEvm hdepth
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmNonceS := permitAfterNonceState evmS I
      have hstructSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterNonceLoadStore evmS I }
            evmNonceS permitStructHashExpr = .ok (permitStructHashValue σ_solm I) := by
        simpa [evmS, evmNonceS] using
          (evalExpr_permit_structHash_at
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            (cur := permitAfterNonceState evmS I))
      have hdigestSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterStructHashStore evmS I (permitStructHashValue σ_solm I) }
            evmNonceS permitDigestExpr = .ok (permitDigestValue σ_solm I) := by
        simpa [evmS, evmNonceS] using
          (evalExpr_permit_digest_afterNonce_at
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g))
      let evmCallS : EVM.State :=
        { evmNonceS with
          substate := (evmNonceS.addAccessedAccount (AccountAddress.ofNat 1)).substate }
      have hdepthSolm : evmNonceS.executionEnv.depth = 1024 := by
        simpa [evmNonceS, evmS, permitAfterNonceState, storageStore_executionEnv, initState]
          using hdepth
      have hcall : typedCallViaEVM config evmNonceS (AccountAddress.ofNat 1) "ecrecover" 0
          [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
          (false, evmCallS, ByteArray.empty) false := by
        simpa [evmCallS] using
          (callNotMade_depthLimit
            (cfg := config) (evm := evmNonceS) (tgt := AccountAddress.ofNat 1)
            (name := "ecrecover")
            (args := [permitDigestValue σ_solm I, permitVValue I, permitRValue I,
              permitSValue I])
            (callPerm := false)
            (uniswapEcrecoverEncode_eq σ_solm I hsz228)
            hdepthSolm)
      exact uniswapPermitBodyCoreRevert_ecrecoverFailure_afterNonce
        hcode hwv hsz228 hexpired hdispatch hrev
        (by simpa [evmS, evmNonceS] using hstructSource)
        (by simpa [evmS, evmNonceS] using hdigestSource)
        hcall
  · exact uniswapPermitBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

theorem uniswapPermitBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hdepth : I.depth.val < 1024
  · exact uniswapPermitBody_depthOk
      hcode hsize hperm hwv hsel hdispatch hAccounts hdepth
  · rw [not_lt] at hdepth
    have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
    exact uniswapPermitBody_depthLimit
      hcode hsize hperm hwv hsel hdispatch hdepth1024

end UniswapV2Pair
