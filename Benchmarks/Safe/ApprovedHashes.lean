import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Routines

/-! # Safe `approvedHashes(address,bytes32)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeApprovedHashesOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeApprovedHashesMessageWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev safeApprovedHashesMessageBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev safeApprovedHashesOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeApprovedHashesOwnerWord I).toNat)

abbrev safeApprovedHashesMessageValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (safeApprovedHashesMessageBytes I)

abbrev safeApprovedHashesLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (safeApprovedHashesOwnerValue I)).insert "arg1"
    (safeApprovedHashesMessageValue I)

theorem safeApprovedHashesLocals_index_arg0 (I : ExecutionEnv) :
    (safeApprovedHashesLocals I)["arg0"] = safeApprovedHashesOwnerValue I := by
  unfold safeApprovedHashesLocals
  rw [Std.HashMap.getElem_insert]
  simp

abbrev safeApprovedHashesOwnerKeyValue (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (safeApprovedHashesOwnerWord I).toNat)

abbrev safeApprovedHashesMessageKeyValue (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (safeApprovedHashesMessageBytes I)

abbrev safeApprovedHashesEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "approvedHashes",
    steps := [.mindex (safeApprovedHashesOwnerKeyValue I),
      .mindex (safeApprovedHashesMessageKeyValue I)] }

abbrev safeApprovedHashesSlotFor (I : ExecutionEnv) : UInt256 :=
  approvedHashesSlot (safeApprovedHashesOwnerKeyValue I)
    (safeApprovedHashesMessageKeyValue I)

def safeApprovedHashesWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeApprovedHashesSlotFor I)

theorem decodeABIValues_address_bytes32_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [.elem .address, abiBytes32] bytes 0 0 64 64 =
      some ([.address (AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .fixedBytes abiBytes32Width ((bytes.drop 32).take 32)], 64) := by
  have hread0 : readBytes? bytes 0 32 = some (bytes.take 32) := by
    unfold readBytes?
    simp [hlen0]
  have hread32 : readBytes? bytes 32 32 = some ((bytes.drop 32).take 32) := by
    unfold readBytes?
    simp [hlen32]
  have hpad : zeroPadding? ((bytes.drop 32).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?
    simp
  have hcanonVal :
      ↑(ABI.bytesToWord (List.take 32 bytes)).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hcanon
  simp [decodeABIValues?, decodeABIValue?, readWord?, hread0, hread32, decodeABIWord?,
    hpad, hcanonVal, abiBytes32, abiBytes32Width, isDynamicABIType, staticABIEncodedSize?,
    UInt256.toNat]

theorem decodeABIValues_address_bytes32_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [.elem .address, abiBytes32] bytes 0 0 64 64 = none := by
  by_cases h32 : bytes.length < 32
  · have hread0 : readBytes? bytes 0 32 = none := by
      unfold readBytes?
      rw [if_neg]
      simp [List.length_take]
      omega
    simp [decodeABIValues?, decodeABIValue?, readWord?, hread0, abiBytes32,
      isDynamicABIType, staticABIEncodedSize?]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hread0 : readBytes? bytes 0 32 = some (bytes.take 32) := by
      unfold readBytes?
      simp [htake0]
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    have hread32 : readBytes? bytes 32 32 = none := by
      unfold readBytes?
      rw [if_neg htake32n]
    by_cases hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
    · have hcanonVal :
          ↑(ABI.bytesToWord (List.take 32 bytes)).val < EVM.addressModulus := by
        simpa [UInt256.toNat] using hcanon
      simp [decodeABIValues?, decodeABIValue?, readWord?, hread0, hread32, decodeABIWord?,
        hcanonVal, abiBytes32, isDynamicABIType, staticABIEncodedSize?]
    · have hncVal :
          ¬ ↑(ABI.bytesToWord (List.take 32 bytes)).val < EVM.addressModulus := by
        simpa [UInt256.toNat] using hcanon
      simp [decodeABIValues?, decodeABIValue?, readWord?, hread0, decodeABIWord?, hncVal,
        abiBytes32, isDynamicABIType, staticABIEncodedSize?]

theorem decodeABIValues_address_bytes32_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [.elem .address, abiBytes32] bytes 0 0 64 64 = none := by
  have hread0 : readBytes? bytes 0 32 = some (bytes.take 32) := by
    unfold readBytes?
    simp [hlen0]
  have hncVal :
      ¬ ↑(ABI.bytesToWord (List.take 32 bytes)).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hnc
  simp [decodeABIValues?, decodeABIValue?, readWord?, hread0, decodeABIWord?, hncVal,
    abiBytes32, isDynamicABIType, staticABIEncodedSize?]

theorem decodeCalldata_address_bytes32_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, abiBytes32] cd =
      some (((∅ : Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.fixedBytes abiBytes32Width ((cd.toList.drop 36).take 32))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [.elem .address, abiBytes32] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_address_bytes32_ok (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  change decodeCalldata.insertValues [x, y]
      [.address (AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .fixedBytes abiBytes32Width (((cd.toList.drop 4).drop 32).take 32)] ∅ =
    some (((∅ : Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.fixedBytes abiBytes32Width ((cd.toList.drop 36).take 32)))
  simp [decodeCalldata.insertValues]
  rw [hword4]

theorem decodeCalldata_address_bytes32_none_short {cd : ByteArray} {x y : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [.elem .address, abiBytes32] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [.elem .address, abiBytes32] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_address_bytes32_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]
  rw [if_pos (by rw [List.length_drop, htlen]; omega : (cd.toList.drop 4).length < 64)]

theorem decodeCalldata_address_bytes32_none_huge {cd : ByteArray} {x y : Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [.elem .address, abiBytes32] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem decodeCalldata_address_bytes32_none_noncanon {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, abiBytes32] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [.elem .address, abiBytes32] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_address_bytes32_none_noncanon (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]

theorem safeApprovedHashesMessageBytes_length {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    (safeApprovedHashesMessageBytes I).length = 32 := by
  simp [safeApprovedHashesMessageBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem safeApprovedHashesOwnerKeyValue_eq {I : ExecutionEnv}
    (hcanon : (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus) :
    keyValueToWord (safeApprovedHashesOwnerKeyValue I) = safeApprovedHashesOwnerWord I :=
  keyValueToWord_address_of_canonical (safeApprovedHashesOwnerWord I) hcanon

theorem safeApprovedHashesMessageKeyValue_eq {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    keyValueToWord (safeApprovedHashesMessageKeyValue I) =
      safeApprovedHashesMessageWord I := by
  have hword :
      ABI.bytesToWord (safeApprovedHashesMessageBytes I) = safeApprovedHashesMessageWord I := by
    simpa [safeApprovedHashesMessageBytes, safeApprovedHashesMessageWord] using
      decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hbytes :
      EVM.Word.toBytesBE (safeApprovedHashesMessageWord I) =
        safeApprovedHashesMessageBytes I := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length (safeApprovedHashesMessageBytes_length hsz68)
  rw [show safeApprovedHashesMessageKeyValue I =
      .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (safeApprovedHashesMessageWord I)) by
        simp [safeApprovedHashesMessageKeyValue, bytes32Width, hbytes]]
  exact keyValueToWord_fixedBytes32 (safeApprovedHashesMessageWord I)

theorem safeApprovedHashesSlotFor_eq {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus) :
    safeApprovedHashesSlotFor I =
      solcMappingSlot (solcMappingSlot ⟨8⟩ (safeApprovedHashesOwnerWord I))
        (safeApprovedHashesMessageWord I) := by
  unfold safeApprovedHashesSlotFor approvedHashesSlot approvedHashesOwnerSlot mapSlot
    solcMappingSlot
  rw [safeApprovedHashesOwnerKeyValue_eq hcanon, safeApprovedHashesMessageKeyValue_eq hsz68]

theorem safeDecode_approvedHashes_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (approvedhashesTransition.params.map Param.name)
      (transitionSignature approvedhashesTransition).paramTypes I.calldata =
        some (safeApprovedHashesLocals I) := by
  simpa [config, safeDecodeMode, approvedhashesTransition, safeApprovedHashesLocals,
    safeApprovedHashesOwnerValue, safeApprovedHashesMessageValue,
    safeApprovedHashesMessageBytes, safeApprovedHashesOwnerWord, bytes32, bytes32Width,
    addr] using
      (decodeCalldata_address_bytes32_ok (cd := I.calldata) (x := "arg0") (y := "arg1")
        hsz68 hsmall hcanon)

theorem safeDecode_approvedHashes_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (approvedhashesTransition.params.map Param.name)
      (transitionSignature approvedhashesTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, approvedhashesTransition, bytes32, bytes32Width, addr] using
    (decodeCalldata_address_bytes32_none_short (cd := I.calldata) (x := "arg0")
      (y := "arg1") hsz4 hshort)

theorem safeDecode_approvedHashes_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (approvedhashesTransition.params.map Param.name)
      (transitionSignature approvedhashesTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, approvedhashesTransition, bytes32, bytes32Width, addr] using
    (decodeCalldata_address_bytes32_none_huge (cd := I.calldata) (x := "arg0")
      (y := "arg1") hbig)

theorem safeDecode_approvedHashes_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (approvedhashesTransition.params.map Param.name)
      (transitionSignature approvedhashesTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, approvedhashesTransition, bytes32, bytes32Width, addr,
    safeApprovedHashesOwnerWord] using
    (decodeCalldata_address_bytes32_none_noncanon (cd := I.calldata) (x := "arg0")
      (y := "arg1") hsz68 hsmall hnc)

theorem safeApprovedHashesDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1082⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1095⟩
      [safeApprovedHashesMessageWord I, safeApprovedHashesOwnerWord I, ⟨974⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  have h9112 := h.push2 ⟨974⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1095⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9112⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9122 := h9112.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9122' := h9122
  rw [hlt] at h9122'
  have h9129 := h9122'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9129⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9129
  have h9130 := h9129.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076 := h9130.jumpdest (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨9140⟩ (by native_decide) (by evm_ov)
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
        safeApprovedHashesOwnerWord I from rfl,
    solcAddrCanon_eq hcanon] at h9088'
  have h6840 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  have h9140 := h6840.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9153 := h9140.jumpdest (by native_decide) (by evm_ov)
    |>.swap5 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [safeApprovedHashesOwnerWord, safeApprovedHashesMessageWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide]
      using h9153.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeApprovedHashesDecodeReverts_len {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1082⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9112 := h.push2 ⟨974⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1095⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9112⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9122 := h9112.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9122' := h9122
  rw [hlt] at h9122'
  have h9129 := h9122'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9129⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h9129
  have h9126 := h9129.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9126.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeApprovedHashesDecodeReverts_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1082⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  have heqZero :
      UInt256.eq (safeApprovedHashesOwnerWord I)
        (UInt256.land (safeApprovedHashesOwnerWord I) solcAddrMask) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnc (solcAddrCanonical_of_clean heq)
  have h9112 := h.push2 ⟨974⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1095⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9112⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9122 := h9112.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9122' := h9122
  rw [hlt] at h9122'
  have h9129 := h9122'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9129⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9129
  have h9130 := h9129.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076 := h9130.jumpdest (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨9140⟩ (by native_decide) (by evm_ov)
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
        safeApprovedHashesOwnerWord I from rfl,
    heqZero] at h9088'
  have h9093 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9093.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeApprovedHashesNestedMappingGetter {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD safeBytecode ee g s0 ⟨1095⟩ (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J safeBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD safeBytecode ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨8⟩ owner) spender) :: ret :: R)
      (solcNestedMappingHashMem ⟨8⟩ owner spender) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have rd1 := h.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd6 := rd5.swap1 (by native_decide) (by evm_ov)
  have rd7 := rd6.dup2 (by native_decide) (by evm_ov)
  have rd9 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨8⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd10 := rd9.push0 (by native_decide) (by evm_ov)
  have rd11 := rd10.swap3 (by native_decide) (by evm_ov)
  have rd12 := rd11.dup4 (by native_decide) (by evm_ov)
  have rd14 := rd12.mstore 0 (solcMappingHashMem ⟨8⟩ owner)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd15 := rd14.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd16 := rd15.dup1 (by native_decide) (by evm_ov)
  have rd17 := rd16.dup5 (by native_decide) (by evm_ov)
  have hinner := solcMappingKeccakSlot ⟨8⟩ owner
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨8⟩ owner)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hinner)
    (by native_decide) (by evm_ov)
  have rd19 := rd18.swap1 (by native_decide) (by evm_ov)
  have rd20 := rd19.swap2 (by native_decide) (by evm_ov)
  have rd21 := rd20.mstore 0 (solcNestedMappingOuterBaseMem ⟨8⟩ owner)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd22 := rd21.swap1 (by native_decide) (by evm_ov)
  have rd23 := rd22.dup3 (by native_decide) (by evm_ov)
  have rd24 := rd23.mstore 0 (solcNestedMappingHashMem ⟨8⟩ owner spender)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd25 := rd24.swap1 (by native_decide) (by evm_ov)
  have hslot := solcNestedMappingKeccakSlot ⟨8⟩ owner spender
  have rd26 := rd25.keccak256 0 (solcMappingSlot (solcMappingSlot ⟨8⟩ owner) spender)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd27⟩ := rd26.sload (by native_decide) (by evm_ov)
  have rd28 := rd27.dup2 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd28.jump (by native_decide) hret (by evm_ov)⟩

theorem safeApprovedHashesX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 3)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (safeApprovedHashesWord σ I)) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1069⟩ := safeReachApprovedHashesBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1082⟩ := safeGuardPeelOk (gt := ⟨1080⟩) h1069 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1095⟩ := safeApprovedHashesDecodeOk h1082 hsz68 hsmall hsize hcanon
  obtain ⟨_, _, h974⟩ := safeApprovedHashesNestedMappingGetter
    (owner := safeApprovedHashesOwnerWord I) (spender := safeApprovedHashesMessageWord I)
    (ret := ⟨974⟩) (R := [safeSelWord I]) h1095
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hval : solcSlotWord σ I
      (solcMappingSlot (solcMappingSlot ⟨8⟩ (safeApprovedHashesOwnerWord I))
        (safeApprovedHashesMessageWord I)) = safeApprovedHashesWord σ I := by
    unfold safeApprovedHashesWord solcSlotWord
    rw [safeApprovedHashesSlotFor_eq hsz68 hcanon]
  exact RD.safeReturnWordFromScratchMem974
    (by simpa [hval] using h974)
    (solcNestedMappingHashMem_size ⟨8⟩ (safeApprovedHashesOwnerWord I)
      (safeApprovedHashesMessageWord I))
    (solcNestedMappingHashMem_read64 ⟨8⟩ (safeApprovedHashesOwnerWord I)
      (safeApprovedHashesMessageWord I))
    (by simp)

theorem safeApprovedHashesBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeApprovedHashesLocals I) approvedhashesTransition.body
      (.returned { contract := contract, locals := safeApprovedHashesLocals I }
        (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat (safeApprovedHashesWord σ I).toNat))])) := by
  let locals : Store := safeApprovedHashesLocals I
  refine nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (by simp only [initState]; exact hwv) ?_
  show evalExpr? config { contract := contract, locals := locals }
    (initState cA gh bl σ σ₀ g A I)
      (.storage (approvedHashesRef (.var "arg0") (.var "arg1"))) =
      .ok (.int (Int.ofNat (safeApprovedHashesWord σ I).toNat))
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := approvedHashesRef (.var "arg0") (.var "arg1"))
    (er := safeApprovedHashesEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (safeApprovedHashesSlotFor I) (.int uint256Int))
    (value := .int (Int.ofNat (safeApprovedHashesWord σ I).toNat))
    (hbase := by simp [approvedHashesRef, locals, safeApprovedHashesLocals])
    (her := by
      have hlen : (safeApprovedHashesMessageBytes I).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using safeApprovedHashesMessageBytes_length (I := I) hsz68
      simp [safeApprovedHashesEvaledRef, safeApprovedHashesOwnerValue,
        safeApprovedHashesMessageValue, safeApprovedHashesOwnerKeyValue,
        safeApprovedHashesMessageKeyValue, safeApprovedHashesMessageBytes, locals,
        safeApprovedHashesLocals, hlen, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, approvedHashesRef, evalExpr?, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind, safeApprovedHashesLocals_index_arg0])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [safeApprovedHashesWord] using
        safeStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
          (safeApprovedHashesSlotFor I))]

theorem safeApprovedHashesBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : safeApprovedHashesWord σ_evm I = safeApprovedHashesWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeApprovedHashesSlotFor I) ⟨0⟩
  exact safeReEquivExecTransport hcode
    (safeApprovedHashesX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz68 hsmall hsize
      hcanon hsel)
    (safeSelectorDispatchApprovedHashes hsel)
    (safeDecode_approvedHashes_ok hsz68 hsmall hcanon)
    (safeApprovedHashesBodyReturns hwv hsz68) (by rw [← hword])
    hAccounts
    (returnEquiv_of_encode
      (by simpa [uint256] using
        uint256ReturnEncoding (safeApprovedHashesWord σ_evm I)))

theorem safeApprovedHashesBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68) (hsel : selIs I (safeSelBytes 3)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1069⟩ := safeReachApprovedHashesBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1082⟩ := safeGuardPeelOk (gt := ⟨1080⟩) h1069 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode (safeApprovedHashesDecodeReverts_len h1082 hlt)
    (safeSelectorDispatchApprovedHashes hsel)
    (safeDecode_approvedHashes_none_short hsz4 hshort)

theorem safeApprovedHashesBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 3)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1069⟩ := safeReachApprovedHashesBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1082⟩ := safeGuardPeelOk (gt := ⟨1080⟩) h1069 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact safeReEquivDecodeFailed hcode (safeApprovedHashesDecodeReverts_len h1082 hlt)
    (safeSelectorDispatchApprovedHashes hsel)
    (safeDecode_approvedHashes_none_huge hbig)

theorem safeApprovedHashesBodyCoreDecodeFailed_noncanon
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 3)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1069⟩ := safeReachApprovedHashesBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1082⟩ := safeGuardPeelOk (gt := ⟨1080⟩) h1069 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  exact safeReEquivDecodeFailed hcode
    (safeApprovedHashesDecodeReverts_noncanon h1082 hsz68 hsmall hsize hnc)
    (safeSelectorDispatchApprovedHashes hsel)
    (safeDecode_approvedHashes_none_noncanon hsz68 hsmall hnc)

theorem safeApprovedHashesBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 3) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz68 : 68 ≤ I.calldata.size
      · by_cases hcanon : (safeApprovedHashesOwnerWord I).toNat < EVM.addressModulus
        · exact safeApprovedHashesBodyCoreOk hcode hsize hwv hsz68 hsmall hcanon hsel
            hAccounts
        · exact safeApprovedHashesBodyCoreDecodeFailed_noncanon hcode hsize hwv hsz68
            hsmall hcanon hsel
      · exact safeApprovedHashesBodyCoreDecodeFailed_short hcode hsize hwv hsz4 (by omega)
          hsel
    · exact safeApprovedHashesBodyCoreDecodeFailed_huge hcode hsize hwv hsz4 (by omega) hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 3) (by native_decide) hsel
    obtain ⟨_, _, h1069⟩ := safeReachApprovedHashesBody (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1080⟩) h1069 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchApprovedHashes hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
