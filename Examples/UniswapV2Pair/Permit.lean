import Examples.UniswapV2Pair.MutatorDispatch
import Examples.UniswapV2Pair.PermitRuntime
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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

abbrev permitAfterNonceLoadStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (permitStore I).insert "nonce" (permitNonceLoadedValue evm I)

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

theorem permitDecodeABIValue_legacyAddress_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? (.elem .address) bytes start DecodeMode.legacySolc05 =
      some (.address (AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := .elem .address) (bytes := bytes) (start := start) (by decide)]
  simpa [abiAddress] using
    (decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := start) hlen)

theorem permitDecodeABIValue_uint256_legacy_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint256 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
        start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := uint256) (bytes := bytes) (start := start) (by decide)]
  simpa [uint256, uint256Int, abiUInt256] using
    (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := bytes) (start := start) hlen)

theorem permitDecodeABIValue_uint8_legacy_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint8 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat
          ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat % EVM.twoPow 8)),
        start + 32) := by
  simpa [uint8, uint8Int, abiUInt8] using
    decodeABIValueWithMode_legacy_uint8_ok (bytes := bytes) (start := start) hlen

theorem permitDecodeABIValue_bytes32_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? bytes32 bytes start DecodeMode.legacySolc05 =
      some (.fixedBytes bytes32Width ((bytes.drop start).take 32), start + 32) := by
  simp only [bytes32, bytes32Width, decodeABIValue?, readBytes?, zeroPadding?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp

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
      some (.address (AccountAddress.ofNat
        (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  change uniswapExternalABI.decode? "ecrecover" returndata = _
  simp [uniswapExternalABI, permitDecodeReturnValue_legacyAddress_ok hlo]

theorem uniswapEcrecoverDecode_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    config.externalABI.decode? "ecrecover" returndata = none := by
  change uniswapExternalABI.decode? "ecrecover" returndata = none
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
        .fixedBytes bytes32Width (((I.calldata.toList.drop 4).drop 192).take 32)], 224) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]
    omega
  have htake32 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake64 : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake96 : (((I.calldata.toList.drop 4).drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake128 : (((I.calldata.toList.drop 4).drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake160 : (((I.calldata.toList.drop 4).drop 160).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake192 : (((I.calldata.toList.drop 4).drop 192).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdec0 : decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 0
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat), 0 + 32) := by
    simpa [List.drop_zero] using
      permitDecodeABIValue_legacyAddress_ok (bytes := I.calldata.toList.drop 4)
        (start := 0) htake0
  have hdec32 : decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 32
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        32 + 32) := by
    exact permitDecodeABIValue_legacyAddress_ok (bytes := I.calldata.toList.drop 4)
      (start := 32) htake32
  have hdec64 : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 64 DecodeMode.legacySolc05 =
        some (.int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
          64 + 32) := by
    simpa [uint256, uint256Int] using
      permitDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
        (start := 64) htake64
  have hdec96 : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 96 DecodeMode.legacySolc05 =
        some (.int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32)).toNat),
          96 + 32) := by
    simpa [uint256, uint256Int] using
      permitDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
        (start := 96) htake96
  have hdec128 : decodeABIValue? (.elem (.int (.uint ⟨8, by decide⟩)))
      (I.calldata.toList.drop 4) 128 DecodeMode.legacySolc05 =
        some (.int (Int.ofNat
          ((ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32)).toNat %
            EVM.twoPow 8)), 128 + 32) := by
    simpa [uint8, uint8Int] using
      permitDecodeABIValue_uint8_legacy_ok (bytes := I.calldata.toList.drop 4)
        (start := 128) htake128
  have hdec160 : decodeABIValue? (.elem (.bytes 31)) (I.calldata.toList.drop 4) 160
      DecodeMode.legacySolc05 = some (.fixedBytes bytes32Width
        (((I.calldata.toList.drop 4).drop 160).take 32), 160 + 32) := by
    simpa [bytes32, bytes32Width] using
      permitDecodeABIValue_bytes32_ok (bytes := I.calldata.toList.drop 4)
        (start := 160) htake160
  have hdec192 : decodeABIValue? (.elem (.bytes 31)) (I.calldata.toList.drop 4) 192
      DecodeMode.legacySolc05 = some (.fixedBytes bytes32Width
        (((I.calldata.toList.drop 4).drop 192).take 32), 192 + 32) := by
    simpa [bytes32, bytes32Width] using
      permitDecodeABIValue_bytes32_ok (bytes := I.calldata.toList.drop 4)
        (start := 192) htake192
  simp [decodeABIValues?, legacyAddr, addr, uint256, uint8, bytes32, bytes32Width,
    uint256Int, uint8Int, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind,
    hdec0, hdec32, hdec64, hdec96, hdec128, hdec160, hdec192]

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
      (transitionSignature permitTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05
    ["owner", "spender", "value", "deadline", "v", "r", "s"]
    [legacyAddr, legacyAddr, uint256, uint256, uint8, bytes32, bytes32] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  unfold decodeCalldata.decodeArgs
  simp [legacyAddr, addr, uint256, uint8, bytes32, bytes32Width, uint256Int, uint8Int,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, isDynamicABIType,
    List.length_drop, htlen]
  rw [if_pos (by omega : I.calldata.size - 4 < 224)]

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

theorem permitAfterNonceLoadStore_nonce (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "nonce" =
      some (permitNonceLoadedValue evm I) := by
  rw [permitAfterNonceLoadStore, store_get_self]

theorem permitAfterNonceLoadStore_owner (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_owner]

theorem permitAfterNonceLoadStore_spender (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "spender" = some (permitSpenderValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_spender]

theorem permitAfterNonceLoadStore_value (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "value" = some (permitValueValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_value]

theorem permitAfterNonceLoadStore_deadline (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "deadline" = some (permitDeadlineValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_deadline]

theorem permitAfterNonceLoadStore_v (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "v" = some (permitVValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_v]

theorem permitAfterNonceLoadStore_r (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "r" = some (permitRValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_r]

theorem permitAfterNonceLoadStore_s (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "s" = some (permitSValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_s]

theorem permitAfterNonceLoadStore_nonces (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "nonces" = none := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide), permitStore_nonces]

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
    (hdec : config.externalABI.decode? "ecrecover" out = some recovered) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore evm I structHash digest recovered }) evm') := by
  simpa [permitAfterEcrecoverStore] using
    (Reasoning.Theory.externalCallSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := permitAfterDigestStore evm I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false)
      (value := recovered) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm)
      (evalExprs_permit_ecrecover_args evm I structHash digest)
      hcall hdec)

theorem uniswapPermitEcrecoverCallSuccessAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some recovered) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }) cur') := by
  simpa [permitAfterEcrecoverStore] using
    (Reasoning.Theory.externalCallSuccess
      (cfg := config) (C := contract) (evm := cur) (evm' := cur')
      (locals := permitAfterDigestStore base I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false)
      (value := recovered) (out := out)
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

theorem storageLayout_permit_nonce (I : ExecutionEnv) :
    config.storage.layout (permitNonceEvaledRef I) =
      fun _ => some (wordLoc (permitNonceStorageSlot I)) := by
  rfl

theorem resolveStorageRef_permit_afterNonce_nonce (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I, uint256St) := by
  exact resolveStorageRef?_ok
    (permitAfterNonceLoadStore_nonces evm I)
    (evalStorageRef_permit_afterNonce_nonce evm I)
    (storageTypeAt_permit_nonce I)

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
  [ .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
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
  [ .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
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
    (hdec : config.externalABI.decode? "ecrecover" out = some recovered) :
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
    (hdec : config.externalABI.decode? "ecrecover" out = some recovered)
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
    (hdec : config.externalABI.decode? "ecrecover" out = some recovered)
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

theorem uniswapPermitNonceStorePrefix (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitNonceStorePrefixBody
      (.ok { contract := contract, locals := permitAfterNonceLoadStore evm I }
        (permitAfterNonceState evm I)) := by
  change ExecBlock config { contract := contract, locals := permitStore I } evm
    [ .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
      .assign .storage (noncesRef (.var "owner"))
        (wrapU256 (.binary .add (.var "nonce") (.intLit 1))) ]
    (.ok { contract := contract, locals := permitAfterNonceLoadStore evm I }
      (permitAfterNonceState evm I))
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_permit_nonce_storage evm I)) ?_
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

theorem uniswapPermitBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
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
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hnonceSource := uniswapPermitNonceStorePrefix evmS I
      have hcreatedNonce :
          (permitAfterNonceState evmS I).createdAccounts = cA := by
        simpa [evmS] using
          (permitAfterNonceState_init_createdAccounts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g))
      have haccountsNonce :
          accountMapEquiv (permitAfterNonceAccountMap σ_evm I)
            (permitAfterNonceState evmS I).accountMap := by
        rw [show (permitAfterNonceState evmS I).accountMap =
            permitAfterNonceAccountMap σ_solm I by
          simpa [evmS] using
            (permitAfterNonceState_init_accountMap
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g))]
        exact permitAfterNonceAccountMap_equiv (I := I) hAccounts
      sorry
  · exact uniswapPermitBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
