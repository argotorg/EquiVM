import Benchmarks.Dss.Jug.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

/-! ## `ilks(bytes32)` struct mapping getter -/

abbrev ilksArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev ilksArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev ilksArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksDutyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "duty"] }

abbrev ilksRhoEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "rho"] }

abbrev ilksDutySlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (ilksArgKey I)

abbrev ilksRhoSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksDutySlotFor I + ⟨1⟩

theorem decodeCalldataWithMode_legacyBytes32_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd =
      some ((∅ : Store).insert x (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hpad : zeroPadding? ((cd.toList.drop 4).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?
    simp
  have htake : List.take 32 ((cd.toList.drop 4).take 32) = (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, abiBytes32,
    ABI.decodeABIValues?, ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?,
    abiTupleHeadSize?, hread, abiBytes32Width, htake, hnotArgShort]

theorem decodeCalldataWithMode_legacyBytes32_none_short {cd : ByteArray} {x : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, abiBytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem jugDecode_ilks_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (ilksArgValue I)) := by
  simpa [config, ilksTransition, ilksArgValue, ilksArgBytes, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem jugDecode_ilks_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata = none := by
  simpa [config, ilksTransition, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_none_short (cd := I.calldata) (x := "arg0")
      hsz4 hshort)

theorem ilksArgBytes_len {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (ilksArgBytes I).length = bytes32Width.val + 1 := by
  unfold ilksArgBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem ilksArgBytes_len_min {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem keyValueToWord_ilksArgKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (ilksArgKey I) = ilksArgWord I := by
  have hlen32 : (ilksArgBytes I).length = 32 := by
    have hlen := ilksArgBytes_len (I := I) hsz36
    simpa [bytes32Width] using hlen
  have hword : ABI.bytesToWord (ilksArgBytes I) = ilksArgWord I := by
    simpa [ilksArgBytes, ilksArgWord] using
      (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
  have hbytes : ilksArgBytes I = EVM.Word.toBytesBE (ilksArgWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := ilksArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [ilksArgKey, bytes32Width, hbytes] using keyValueToWord_fixedBytes32 (ilksArgWord I)

theorem keyValueToWord_ilksArgValue {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (ilksArgKey I) = ilksArgWord I := by
  exact keyValueToWord_ilksArgKey hsz36

theorem ilksArgBytes_len32 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (ilksArgBytes I).length = 32 := by
  have hlen := ilksArgBytes_len (I := I) hsz36
  simpa [bytes32Width] using hlen

/-! Compatibility-free slot equations for the getter proof. -/
theorem ilksDutySlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksDutySlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) := by
  unfold ilksDutySlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_ilksArgKey hsz36]

theorem ilksRhoSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksRhoSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) + ⟨1⟩ := by
  simp [ilksRhoSlotFor, ilksDutySlotFor_eq hsz36]

/-!
The following proof names were used during development and are kept out of the
public API; the slot lemmas above are the stable facts used below.
-/
private theorem keyValueToWord_ilksArgKey_aux {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (ilksArgKey I) = ilksArgWord I := by
  have hlen : (ilksArgBytes I).length = 32 := by
    unfold ilksArgBytes
    rw [List.length_take, List.length_drop]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    omega
  have hword : ABI.bytesToWord (ilksArgBytes I) = ilksArgWord I := by
    simpa [ilksArgBytes, ilksArgWord] using
      (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
  have hbytes : ilksArgBytes I = EVM.Word.toBytesBE (ilksArgWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := ilksArgBytes I) hlen
    rw [hword] at hto
    exact hto.symm
  simpa [ilksArgKey, bytes32Width, hbytes] using keyValueToWord_fixedBytes32 (ilksArgWord I)

noncomputable def solcScratchReturn2Mem
    (scratch : ByteArray) (first second : UInt256) : ByteArray :=
  (UInt256.toByteArray second).write 0 (solcScratchReturnMem scratch first) 160 32

theorem solcScratchReturn2Mem_size {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96) :
    (solcScratchReturn2Mem scratch first second).size = 192 := by
  unfold solcScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  exact toByteArray_write32_size_of_ge (solcScratchReturnMem scratch first) second 160 160 192
    hbase (by omega) (by norm_num) (by norm_num)

theorem solcScratchReturn2Mem_read64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcScratchReturn2Mem scratch first second).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  rw [toByteArray_write_read_below_of_gap second (solcScratchReturnMem scratch first) 160 64]
  exact solcScratchReturnMem_read64 first hscratch hread64
  · rw [hbase]; omega
  · omega
  · rw [hbase]; norm_num

theorem solcScratchReturn2Mem_mload64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcScratchReturn2Mem scratch first second).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcScratchReturn2Mem scratch first second).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcScratchReturn2Mem_size first second hscratch]; decide)
    (by decide) (solcScratchReturn2Mem_read64 first second hscratch hread64)

theorem solcScratchReturn2Mem_read128_64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96) :
    (solcScratchReturn2Mem scratch first second).readWithPadding 128 64 =
      UInt256.toByteArray first ++ UInt256.toByteArray second := by
  unfold solcScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  rw [show (160 : Nat) = (solcScratchReturnMem scratch first).size by rw [hbase]]
  rw [write_at_end_eq (UInt256.toByteArray second) (solcScratchReturnMem scratch first) 32
    (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all second]
  rw [readWithPadding_eq_extract' _ 128 64 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, hbase, toByteArray_size])]
  rw [extract_append_span _ _ _ _ (by rw [hbase]; omega) (by rw [hbase]; omega)]
  have hleft :
      (solcScratchReturnMem scratch first).extract 128
          (solcScratchReturnMem scratch first).size =
        UInt256.toByteArray first := by
    rw [hbase]
    rw [← readWithPadding_eq_extract _ 128 (by rw [hbase])]
    exact solcScratchReturnMem_read128 first hscratch
  rw [hleft]
  rw [hbase]
  norm_num
  rw [toByteArray_extract_all second]

@[reducible] def solcTwoWordReturnFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.SWAP3, .none)
  ∧ decode code p6 = some (.DUP4, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.DUP4, .none)
  ∧ decode code p11 = some (.ADD, .none)
  ∧ decode code p12 = some (.SWAP2, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.SWAP2, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.DUP1, .none)
  ∧ decode code p17 = some (.MLOAD, .none)
  ∧ decode code p18 = some (.SWAP2, .none)
  ∧ decode code p19 = some (.DUP3, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.SUB, .none)
  ∧ decode code p22 = some (.ADD, .none)
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.RETURN, .none)

theorem RD.solcTwoWordReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc first second ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (second :: first :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcTwoWordReturnFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hscratch : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray first ++ UInt256.toByteArray second) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd14,
      hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap3 hd5 (by evm_ov),
    raw dup4 hd6 (by evm_ov),
    raw mstore 6 (solcScratchReturnMem mem first) (UInt256.ofNat 5) hd7 mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd8 (by evm_ov),
    raw dup4 hd10 (by evm_ov),
    raw add hd11 (by evm_ov),
    raw swap2 hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap2 hd14 (by evm_ov),
    raw mstore 3 (solcScratchReturn2Mem mem first second) (UInt256.ofNat 6) hd15 mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup1 hd16 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) hd17 mem_cost
      (solcScratchReturn2Mem_mload64 first second hscratch hread64) (by decide) (by evm_ov),
    raw swap2 hd18 (by evm_ov),
    raw dup3 hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw sub hd21 (by evm_ov),
    raw add hd22 (by evm_ov),
    raw swap1 hd23 (by evm_ov),
    raw ret 0 (UInt256.toByteArray first ++ UInt256.toByteArray second) hd24 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rw [show (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨64⟩).toNat = 64
          from by decide]
        exact solcScratchReturn2Mem_read128_64 first second hscratch)
      (by evm_ov)]

@[reducible] def solcIlksStructGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p10 = some (.SWAP2, .none)
  ∧ decode code p11 = some (.DUP3, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p15 = some (.SWAP1, .none)
  ∧ decode code p16 = some (.SWAP2, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.DUP1, .none)
  ∧ decode code p19 = some (.SLOAD, .none)
  ∧ decode code p20 = some (.SWAP2, .none)
  ∧ decode code p21 = some (.ADD, .none)
  ∧ decode code p22 = some (.SLOAD, .none)
  ∧ decode code p23 = some (.DUP3, .none)
  ∧ decode code p24 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcIlksStructGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcIlksStructGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee ((solcMappingSlot ⟨1⟩ key) + ⟨1⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨1⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨1⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨1⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd10 := rd8.push1 ⟨0⟩ hd8 (by evm_ov)
  have rd11 := rd10.swap2 hd10 (by evm_ov)
  have rd12 := rd11.dup3 hd11 (by evm_ov)
  have rd13 := rd12.mstore 0 (solcMappingHashMem ⟨1⟩ key)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd15 := rd13.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.swap1 hd15 (by evm_ov)
  have rd17 := rd16.swap2 hd16 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨1⟩ key
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨1⟩ key)
    (UInt256.ofNat 3) hd17 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by decide +native) (by evm_ov)
  have rd19 := rd18.dup1 hd18 (by evm_ov)
  obtain ⟨_, _, rd20⟩ := rd19.sload hd19 (by evm_ov)
  have rd21 := rd20.swap2 hd20 (by evm_ov)
  have rd22 := rd21.add hd21 (by evm_ov)
  obtain ⟨_, _, rd23⟩ := rd22.sload hd22 (by evm_ov)
  have rd24 := rd23.dup3 hd23 (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_add_comm] using rd24.jump hd24 hret (by evm_ov)⟩

theorem uint256PairReturnEncoding (first second : UInt256) :
    encodeReturnValues? [uint256, uint256]
      [.int (Int.ofNat first.toNat), .int (Int.ofNat second.toNat)] =
        some (UInt256.toByteArray first ++ UInt256.toByteArray second) := by
  have hencFirst :
      encodeABIValue? uint256 (.int (Int.ofNat first.toNat)) =
        some (EVM.Word.toBytesBE first) := by
    have hword : EVM.word first.toNat = first := by
      show UInt256.ofNat first.toNat = first
      exact u256_ofNat_toNat first
    have hlt : first.toNat < EVM.twoPow 256 := by
      change first.val.val < EVM.twoPow 256
      exact first.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencSecond :
      encodeABIValue? uint256 (.int (Int.ofNat second.toNat)) =
        some (EVM.Word.toBytesBE second) := by
    have hword : EVM.word second.toNat = second := by
      show UInt256.ofNat second.toNat = second
      exact u256_ofNat_toNat second
    have hlt : second.toNat < EVM.twoPow 256 := by
      change second.val.val < EVM.twoPow 256
      exact second.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray first = (EVM.Word.toBytesBE first).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray first).symm]
  rw [show UInt256.toByteArray second = (EVM.Word.toBytesBE second).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray second).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [uint256, uint256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencFirst]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by decide +native]
  unfold encodeABIValuesFrom?
  rw [hencSecond]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by decide +native]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem jugIlksBodyReturns {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals = (∅ : Store).insert "arg0" (ilksArgValue I)) :
    ExecTransitionBody config contract evm locals ilksTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (jugSlotWord (ilksDutySlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (jugSlotWord (ilksRhoSlotFor I) evm.accountMap evm.executionEnv).toNat))])) := by
  subst locals
  let frame : Frame := { contract := contract, locals := (∅ : Store).insert "arg0" (ilksArgValue I) }
  have hduty :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "duty")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (ilksDutySlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "duty") (er := ilksDutyEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksDutySlotFor I))
      (value := .int (Int.ofNat
        (jugSlotWord (ilksDutySlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
        simp [frame, ilksDutyEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, IlkStructTy, uint256St])
      (by rfl)
      (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (ilksDutySlotFor I))
  have hrho :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "rho")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (ilksRhoSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "rho") (er := ilksRhoEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksRhoSlotFor I))
      (value := .int (Int.ofNat
        (jugSlotWord (ilksRhoSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
        simp [frame, ilksRhoEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, IlkStructTy, uint256St])
      (by rfl)
      (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (ilksRhoSlotFor I))
  have hreturns :
      evalExprs? config frame evm
        [.storage (ilksF (.var "arg0") "duty"), .storage (ilksF (.var "arg0") "rho")] =
          .ok
            [ .int (Int.ofNat
                (jugSlotWord (ilksDutySlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (jugSlotWord (ilksRhoSlotFor I) evm.accountMap evm.executionEnv).toNat) ] := by
    simp [evalExprs?, hduty, hrho, EvalResult.bind, bind, pure]
  simpa [ilksTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

theorem jugReachIlksBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 6)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨549⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0xd9638d36⟩ :=
    jugSelWord_eq_of_beq I hsz 0xd9 0x63 0x8d 0x36 ⟨0xd9638d36⟩
      (by decide +native) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc 5))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact jugReachHighBody 5 (by omega) ⟨549⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by decide +native)

theorem jugIlksBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
        (transitionSignature ilksTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (ilksArgValue I)))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨549⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let dutySlot := solcMappingSlot ⟨1⟩ (ilksArgWord I)
  let rhoSlot := dutySlot + ⟨1⟩
  let dutyWord := jugSlotWord dutySlot σ_evm I
  let rhoWord := jugSlotWord rhoSlot σ_evm I
  let locals : Store := (∅ : Store).insert "arg0" (ilksArgValue I)
  have hdutySlot : ilksDutySlotFor I = dutySlot := by
    simp [dutySlot, ilksDutySlotFor_eq hsz36]
  have hrhoSlot : ilksRhoSlotFor I = rhoSlot := by
    simp [rhoSlot, dutySlot, ilksRhoSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals ilksTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (jugSlotWord (ilksDutySlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (jugSlotWord (ilksRhoSlotFor I) σ_solm I).toNat))])) := by
    simpa [locals, initState] using
      jugIlksBodyReturns hsz36
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (by simp only [initState]; exact hwv) rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := jugBytecode) (sel := sel) (entry := ⟨549⟩) (ret := ⟨578⟩)
    (decoded := ⟨571⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have htoRoutine : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2106⟩
      (ilksArgWord I :: ⟨578⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    have rd572 := hdecoded.jumpdest (by decide +native) (by evm_ov)
    have rd573 := rd572.pop (by decide +native) (by evm_ov)
    have rd574 := rd573.calldataload (by decide +native) (by evm_ov)
    have rd577 := rd574.push2 ⟨2106⟩ (by decide +native) (by evm_ov)
    exact ⟨_, _, by
      simpa [ilksArgWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
        using rd577.jump (by decide +native) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, htoRoutineRd⟩ := htoRoutine
  obtain ⟨_, _, hretPc⟩ := RD.solcIlksStructGetter
    (code := jugBytecode) (pc := ⟨2106⟩) (key := ilksArgWord I) (ret := ⟨578⟩)
    (R := [sel]) (by simpa using htoRoutineRd)
    (by
      unfold solcIlksStructGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by simp)
  have hret :
      RDret jugBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray dutyWord ++ UInt256.toByteArray rhoWord) := by
    have hret' := RD.solcTwoWordReturnFromMem
      (pc := ⟨578⟩) (first := dutyWord) (second := rhoWord) (ret := ⟨578⟩)
      (R := [sel]) (mem := solcMappingHashMem ⟨1⟩ (ilksArgWord I))
      (by
        simpa [dutyWord, rhoWord, dutySlot, rhoSlot, jugSlotWord] using hretPc)
      (by
        unfold solcTwoWordReturnFromMemWf
        repeat' first | apply And.intro | decide +native)
      (solcMappingHashMem_mload64 ⟨1⟩ (ilksArgWord I))
      (solcMappingHashMem_size ⟨1⟩ (ilksArgWord I))
      (solcMappingHashMem_read64 ⟨1⟩ (ilksArgWord I))
      (by simp)
    simpa [dutyWord, rhoWord] using hret'
  have hdutyWord : jugSlotWord dutySlot σ_evm I = jugSlotWord dutySlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner dutySlot ⟨0⟩
  have hrhoWord : jugSlotWord rhoSlot σ_evm I = jugSlotWord rhoSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner rhoSlot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (jugSlotWord (ilksDutySlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (jugSlotWord (ilksRhoSlotFor I) σ_solm I).toNat)] =
      some [Value.int (Int.ofNat dutyWord.toNat), Value.int (Int.ofNat rhoWord.toNat)] := by
    rw [hdutySlot, hrhoSlot]
    simp [dutyWord, rhoWord, hdutyWord, hrhoWord]
  have henc :
      returnEquiv (UInt256.toByteArray dutyWord ++ UInt256.toByteArray rhoWord)
        (some [(.int (Int.ofNat dutyWord.toNat)), (.int (Int.ofNat rhoWord.toNat))])
        ilksTransition.returnType := by
    rw [show ilksTransition.returnType = [uint256, uint256] by rfl]
    exact returnEquiv.returned rfl (uint256PairReturnEncoding dutyWord rhoWord)
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem jugIlksBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨549⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := jugBytecode) (sel := sel) (entry := ⟨549⟩) (ret := ⟨578⟩)
    (decoded := ⟨571⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (jugDecode_ilks_none_short hsz4 hshort)

theorem jugIlksBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some ilksTransition :=
    jugDispatchIlks hsel
  have hreach := jugReachIlksBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact jugIlksBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (jugDecode_ilks_ok hsz36) hreach hAccounts
  · exact jugIlksBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Jug
