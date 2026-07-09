import Examples.UniswapV2Pair.MutatorDispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace UniswapV2Pair

/-! ## `permit` ABI decoding helpers -/

theorem permitDecodeABIValue_legacyAddress_ok_core {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? (.elem .address) bytes start DecodeMode.legacySolc05 =
      some (.address (AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := .elem .address) (bytes := bytes) (start := start) (by decide)]
  simpa [abiAddress] using
    (decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := start) hlen)

theorem permitDecodeABIValue_uint256_legacy_ok_core {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint256 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
        start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := uint256) (bytes := bytes) (start := start) (by decide)]
  simpa [uint256, uint256Int, abiUInt256] using
    (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := bytes) (start := start) hlen)

theorem permitDecodeABIValue_uint8_legacy_ok_core {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint8 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat
          ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat % EVM.twoPow 8)),
        start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := uint8) (bytes := bytes) (start := start) (by decide)]
  simp only [uint8, uint8Int, decodeScalarWordWithMode?, readWord?, readBytes?,
    decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  simp only
  rw [if_neg (show ¬ ((8 : Nat) = 0) from by decide)]
  rfl

theorem permitDecodeABIValue_bytes32_ok_core {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? bytes32 bytes start DecodeMode.legacySolc05 =
      some (.fixedBytes bytes32Width ((bytes.drop start).take 32), start + 32) := by
  simp only [bytes32, bytes32Width, decodeABIValue?, readBytes?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp

theorem permitDecodeABIValues_ok_core {I : ExecutionEnv} (hsz228 : 228 ≤ I.calldata.size) :
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
      permitDecodeABIValue_legacyAddress_ok_core (bytes := I.calldata.toList.drop 4)
        (start := 0) htake0
  have hdec32 : decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 32
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        32 + 32) := by
    exact permitDecodeABIValue_legacyAddress_ok_core (bytes := I.calldata.toList.drop 4)
      (start := 32) htake32
  have hdec64 : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 64 DecodeMode.legacySolc05 =
        some (.int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
          64 + 32) := by
    simpa [uint256, uint256Int] using
      permitDecodeABIValue_uint256_legacy_ok_core (bytes := I.calldata.toList.drop 4)
        (start := 64) htake64
  have hdec96 : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 96 DecodeMode.legacySolc05 =
        some (.int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32)).toNat),
          96 + 32) := by
    simpa [uint256, uint256Int] using
      permitDecodeABIValue_uint256_legacy_ok_core (bytes := I.calldata.toList.drop 4)
        (start := 96) htake96
  have hdec128 : decodeABIValue? (.elem (.int (.uint ⟨8, by decide⟩)))
      (I.calldata.toList.drop 4) 128 DecodeMode.legacySolc05 =
        some (.int (Int.ofNat
          ((ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32)).toNat %
            EVM.twoPow 8)), 128 + 32) := by
    simpa [uint8, uint8Int] using
      permitDecodeABIValue_uint8_legacy_ok_core (bytes := I.calldata.toList.drop 4)
        (start := 128) htake128
  have hdec160 : decodeABIValue? (.elem (.bytes 31)) (I.calldata.toList.drop 4) 160
      DecodeMode.legacySolc05 = some (.fixedBytes bytes32Width
        (((I.calldata.toList.drop 4).drop 160).take 32), 160 + 32) := by
    simpa [bytes32, bytes32Width] using
      permitDecodeABIValue_bytes32_ok_core (bytes := I.calldata.toList.drop 4)
        (start := 160) htake160
  have hdec192 : decodeABIValue? (.elem (.bytes 31)) (I.calldata.toList.drop 4) 192
      DecodeMode.legacySolc05 = some (.fixedBytes bytes32Width
        (((I.calldata.toList.drop 4).drop 192).take 32), 192 + 32) := by
    simpa [bytes32, bytes32Width] using
      permitDecodeABIValue_bytes32_ok_core (bytes := I.calldata.toList.drop 4)
        (start := 192) htake192
  simp [decodeABIValues?, legacyAddr, addr, uint256, uint8, bytes32, bytes32Width,
    uint256Int, uint8Int, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind,
    hdec0, hdec32, hdec64, hdec96, hdec128, hdec160, hdec192]

theorem uniswapDecode_permit_none_short_core {I : ExecutionEnv}
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

end UniswapV2Pair
