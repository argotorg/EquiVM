import Benchmarks.Dss.Cat.Common
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-! ## `ilks(bytes32)` struct getter — returns (flip : address, chop : uint256, dunk : uint256) -/

abbrev ilksArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev ilksArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev ilksArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksFlipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "flip"] }

abbrev ilksChopEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "chop"] }

abbrev ilksDunkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "dunk"] }

abbrev ilksFlipSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (ilksArgKey I)

abbrev ilksChopSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksFlipSlotFor I + ⟨1⟩

abbrev ilksDunkSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksFlipSlotFor I + ⟨2⟩

/-! ### bytes32 calldata decode (LIBRARY CANDIDATE: ported from Benchmarks/Dss/Jug/Ilks.lean) -/

theorem decodeCalldataWithMode_legacyBytes32_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd =
      some ((∅ : Store).insert x (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]; omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hpad : zeroPadding? ((cd.toList.drop 4).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?; simp
  have htake : List.take 32 ((cd.toList.drop 4).take 32) = (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]; omega
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
    rw [htlen]; omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, abiBytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem catDecode_ilks_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (ilksArgValue I)) := by
  simpa [config, ilksTransition, ilksArgValue, ilksArgBytes, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem catDecode_ilks_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata = none := by
  simpa [config, ilksTransition, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

/-! ### arg-word / slot equations (ported from Jug) -/

theorem ilksArgBytes_len {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (ilksArgBytes I).length = bytes32Width.val + 1 := by
  unfold ilksArgBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [htlen]; simp [bytes32Width]; omega

theorem ilksArgBytes_len_min {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [htlen]; simp [bytes32Width]; omega

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

theorem ilksFlipSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksFlipSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) := by
  unfold ilksFlipSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_ilksArgKey hsz36]

theorem ilksChopSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksChopSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) + ⟨1⟩ := by
  simp [ilksChopSlotFor, ilksFlipSlotFor_eq hsz36]

theorem ilksDunkSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksDunkSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) + ⟨2⟩ := by
  simp [ilksDunkSlotFor, ilksFlipSlotFor_eq hsz36]

/-! ### 3-word return scratch memory (extends Jug's 2-word scratch) -/

noncomputable def catScratchReturn2Mem (scratch : ByteArray) (first second : UInt256) : ByteArray :=
  (UInt256.toByteArray second).write 0 (solcScratchReturnMem scratch first) 160 32

noncomputable def catScratchReturn3Mem
    (scratch : ByteArray) (first second third : UInt256) : ByteArray :=
  (UInt256.toByteArray third).write 0 (catScratchReturn2Mem scratch first second) 192 32

theorem catScratchReturn2Mem_size {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96) :
    (catScratchReturn2Mem scratch first second).size = 192 := by
  unfold catScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  exact toByteArray_write32_size_of_ge (solcScratchReturnMem scratch first) second 160 160 192
    hbase (by omega) (by norm_num) (by norm_num)

theorem catScratchReturn3Mem_size {scratch : ByteArray} (first second third : UInt256)
    (hscratch : scratch.size = 96) :
    (catScratchReturn3Mem scratch first second third).size = 224 := by
  unfold catScratchReturn3Mem
  have hbase : (catScratchReturn2Mem scratch first second).size = 192 :=
    catScratchReturn2Mem_size first second hscratch
  exact toByteArray_write32_size_of_ge (catScratchReturn2Mem scratch first second) third 192 192 224
    hbase (by omega) (by norm_num) (by norm_num)

theorem catScratchReturn2Mem_read64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (catScratchReturn2Mem scratch first second).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold catScratchReturn2Mem
  have hbase : (solcScratchReturnMem scratch first).size = 160 :=
    solcScratchReturnMem_size first hscratch
  rw [toByteArray_write_read_below_of_gap second (solcScratchReturnMem scratch first) 160 64]
  exact solcScratchReturnMem_read64 first hscratch hread64
  · rw [hbase]; omega
  · omega
  · rw [hbase]; norm_num

theorem catScratchReturn3Mem_read64 {scratch : ByteArray} (first second third : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (catScratchReturn3Mem scratch first second third).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold catScratchReturn3Mem
  have hbase : (catScratchReturn2Mem scratch first second).size = 192 :=
    catScratchReturn2Mem_size first second hscratch
  rw [toByteArray_write_read_below_of_gap third (catScratchReturn2Mem scratch first second) 192 64]
  exact catScratchReturn2Mem_read64 first second hscratch hread64
  · rw [hbase]; omega
  · omega
  · rw [hbase]; norm_num

theorem catScratchReturn3Mem_mload64 {scratch : ByteArray} (first second third : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (catScratchReturn3Mem scratch first second third).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((catScratchReturn3Mem scratch first second third).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [catScratchReturn3Mem_size first second third hscratch]; decide)
    (by decide) (catScratchReturn3Mem_read64 first second third hscratch hread64)

theorem catScratchReturn2Mem_read128_64 {scratch : ByteArray} (first second : UInt256)
    (hscratch : scratch.size = 96) :
    (catScratchReturn2Mem scratch first second).readWithPadding 128 64 =
      UInt256.toByteArray first ++ UInt256.toByteArray second := by
  unfold catScratchReturn2Mem
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
  rw [hleft, hbase]
  norm_num
  rw [toByteArray_extract_all second]

theorem catScratchReturn3Mem_read128_96 {scratch : ByteArray} (first second third : UInt256)
    (hscratch : scratch.size = 96) :
    (catScratchReturn3Mem scratch first second third).readWithPadding 128 96 =
      UInt256.toByteArray first ++ UInt256.toByteArray second ++ UInt256.toByteArray third := by
  unfold catScratchReturn3Mem
  have hbase : (catScratchReturn2Mem scratch first second).size = 192 :=
    catScratchReturn2Mem_size first second hscratch
  rw [show (192 : Nat) = (catScratchReturn2Mem scratch first second).size by rw [hbase]]
  rw [write_at_end_eq (UInt256.toByteArray third) (catScratchReturn2Mem scratch first second) 32
    (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all third]
  rw [readWithPadding_eq_extract' _ 128 96 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, hbase, toByteArray_size])]
  rw [extract_append_span _ _ _ _ (by rw [hbase]; omega) (by rw [hbase]; omega)]
  have hleft :
      (catScratchReturn2Mem scratch first second).extract 128
          (catScratchReturn2Mem scratch first second).size =
        UInt256.toByteArray first ++ UInt256.toByteArray second := by
    have h2 : (catScratchReturn2Mem scratch first second).readWithPadding 128 64 =
        UInt256.toByteArray first ++ UInt256.toByteArray second :=
      catScratchReturn2Mem_read128_64 first second hscratch
    rw [readWithPadding_eq_extract' (catScratchReturn2Mem scratch first second) 128 64
      (by norm_num) (by norm_num)
      (by have := catScratchReturn2Mem_size first second hscratch; omega)] at h2
    rw [hbase]
    exact h2
  rw [hleft, hbase]
  norm_num
  rw [toByteArray_extract_all third]

/-! ### struct-load routine at pc 3215 (3 SLOADs + address mask on flip) -/

@[reducible] def catIlksStructGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p32 := p30 + UInt256.ofNat 2
  let p34 := p32 + UInt256.ofNat 2
  let p36 := p34 + UInt256.ofNat 2
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
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
  ∧ decode code p21 = some (.DUP2, .none)
  ∧ decode code p22 = some (.ADD, .none)
  ∧ decode code p23 = some (.SLOAD, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.SWAP2, .none)
  ∧ decode code p28 = some (.ADD, .none)
  ∧ decode code p29 = some (.SLOAD, .none)
  ∧ decode code p30 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p32 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p34 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p36 = some (.SHL, .none)
  ∧ decode code p37 = some (.SUB, .none)
  ∧ decode code p38 = some (.SWAP1, .none)
  ∧ decode code p39 = some (.SWAP3, .none)
  ∧ decode code p40 = some (.AND, .none)
  ∧ decode code p41 = some (.SWAP2, .none)
  ∧ decode code p42 = some (.DUP4, .none)
  ∧ decode code (p42 + ⟨1⟩) = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.catIlksStructGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : catIlksStructGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨2⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨1⟩) ::
        UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key)) solcAddrMask ::
        ret :: R)
      (solcMappingHashMem ⟨1⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16, hd17, hd18, hd19,
      hd20, hd21, hd22, hd23, hd24, hd26, hd27, hd28, hd29, hd30, hd32, hd34, hd36, hd37, hd38,
      hd39, hd40, hd41, hd42, hd43⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨1⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨1⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd10 := rd8.push1 ⟨0⟩ hd8 (by evm_ov)
  have rd11 := rd10.swap2 hd10 (by evm_ov)
  have rd12 := rd11.dup3 hd11 (by evm_ov)
  have rd13 := rd12.mstore 0 (solcMappingHashMem ⟨1⟩ key)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := rd13.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.swap1 hd15 (by evm_ov)
  have rd17 := rd16.swap2 hd16 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨1⟩ key
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨1⟩ key)
    (UInt256.ofNat 3) hd17 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  have rd19 := rd18.dup1 hd18 (by evm_ov)
  obtain ⟨_, _, rd20⟩ := rd19.sload hd19 (by evm_ov)
  have rd21 := rd20.swap2 hd20 (by evm_ov)
  have rd22 := rd21.dup2 hd21 (by evm_ov)
  have rd23 := rd22.add hd22 (by evm_ov)
  obtain ⟨_, _, rd24⟩ := rd23.sload hd23 (by evm_ov)
  have rd26 := rd24.push1 ⟨2⟩ hd24 (by evm_ov)
  have rd27 := rd26.swap1 hd26 (by evm_ov)
  have rd28 := rd27.swap2 hd27 (by evm_ov)
  have rd29 := rd28.add hd28 (by evm_ov)
  obtain ⟨_, _, rd30⟩ := rd29.sload hd29 (by evm_ov)
  have rd32 := rd30.push1 ⟨1⟩ hd30 (by evm_ov)
  have rd34 := rd32.push1 ⟨1⟩ hd32 (by evm_ov)
  have rd36 := rd34.push1 ⟨160⟩ hd34 (by evm_ov)
  have rd37 := rd36.shl hd36 (by evm_ov)
  have rd38 := rd37.sub hd37 (by evm_ov)
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by decide]
    at rd38
  have rd39 := rd38.swap1 hd38 (by evm_ov)
  have rd40 := rd39.swap3 hd39 (by evm_ov)
  have rd41 := rd40.and hd40 (by evm_ov)
  have rd42 := rd41.swap2 hd41 (by evm_ov)
  have rd43 := rd42.dup4 hd42 (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord] using rd43.jump hd43 hret (by evm_ov)⟩

/-! ### 3-word return encoder at pc 664 (masks flip, lays out [flip, chop, dunk], RETURNs 96 bytes) -/

@[reducible] def catIlksReturnFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p37 := p35 + UInt256.ofNat 2
  let p38 := p37 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p11 = some (.SHL, .none)
  ∧ decode code p12 = some (.SUB, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.SWAP5, .none)
  ∧ decode code p15 = some (.AND, .none)
  ∧ decode code p16 = some (.DUP5, .none)
  ∧ decode code p17 = some (.MSTORE, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p20 = some (.DUP5, .none)
  ∧ decode code p21 = some (.ADD, .none)
  ∧ decode code p22 = some (.SWAP3, .none)
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.SWAP3, .none)
  ∧ decode code p25 = some (.MSTORE, .none)
  ∧ decode code p26 = some (.DUP3, .none)
  ∧ decode code p27 = some (.DUP3, .none)
  ∧ decode code p28 = some (.ADD, .none)
  ∧ decode code p29 = some (.MSTORE, .none)
  ∧ decode code p30 = some (.MLOAD, .none)
  ∧ decode code p31 = some (.SWAP1, .none)
  ∧ decode code p32 = some (.DUP2, .none)
  ∧ decode code p33 = some (.SWAP1, .none)
  ∧ decode code p34 = some (.SUB, .none)
  ∧ decode code p35 = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code p37 = some (.ADD, .none)
  ∧ decode code p38 = some (.SWAP1, .none)
  ∧ decode code (p38 + ⟨1⟩) = some (.RETURN, .none)

set_option maxHeartbeats 1000000 in
theorem RD.catIlksReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc first second third ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (third :: second :: first :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : catIlksReturnFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hscratch : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land first solcAddrMask) ++
        UInt256.toByteArray second ++ UInt256.toByteArray third) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd20,
      hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29, hd30, hd31, hd32, hd33, hd34, hd35,
      hd37, hd38, hd39⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨64⟩ hd1 (by evm_ov)
  have rd4 := rd3.dup1 hd3 (by evm_ov)
  have rd5 := rd4.mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov)
  have rd7 := rd5.push1 ⟨1⟩ hd5 (by evm_ov)
  have rd9 := rd7.push1 ⟨1⟩ hd7 (by evm_ov)
  have rd11 := rd9.push1 ⟨160⟩ hd9 (by evm_ov)
  have rd12 := rd11.shl hd11 (by evm_ov)
  have rd13 := rd12.sub hd12 (by evm_ov)
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by decide]
    at rd13
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have rd15 := rd14.swap5 hd14 (by evm_ov)
  have rd16 := rd15.and hd15 (by evm_ov)
  have rd17 := rd16.dup5 hd16 (by evm_ov)
  have rd18 := rd17.mstore 6 (solcScratchReturnMem mem (UInt256.land first solcAddrMask))
    (UInt256.ofNat 5) hd17 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd20 := rd18.push1 ⟨32⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup5 hd20 (by evm_ov)
  have rd22 := rd21.add hd21 (by evm_ov)
  have rd23 := rd22.swap3 hd22 (by evm_ov)
  have rd24 := rd23.swap1 hd23 (by evm_ov)
  have rd25 := rd24.swap3 hd24 (by evm_ov)
  have rd26 := rd25.mstore 3
    (catScratchReturn2Mem mem (UInt256.land first solcAddrMask) second)
    (UInt256.ofNat 6) hd25 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd27 := rd26.dup3 hd26 (by evm_ov)
  have rd28 := rd27.dup3 hd27 (by evm_ov)
  have rd29 := rd28.add hd28 (by evm_ov)
  have rd30 := rd29.mstore 3
    (catScratchReturn3Mem mem (UInt256.land first solcAddrMask) second third)
    (UInt256.ofNat 7) hd29 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd31 := rd30.mload 0 ⟨128⟩ (UInt256.ofNat 7) hd30 mem_cost
    (catScratchReturn3Mem_mload64 (UInt256.land first solcAddrMask) second third hscratch hread64)
    (by decide) (by evm_ov)
  have rd32 := rd31.swap1 hd31 (by evm_ov)
  have rd33 := rd32.dup2 hd32 (by evm_ov)
  have rd34 := rd33.swap1 hd33 (by evm_ov)
  have rd35 := rd34.sub hd34 (by evm_ov)
  have rd37 := rd35.push1 ⟨96⟩ hd35 (by evm_ov)
  have rd38 := rd37.add hd37 (by evm_ov)
  have rd39 := rd38.swap1 hd38 (by evm_ov)
  refine rd39.ret 0
    (UInt256.toByteArray (UInt256.land first solcAddrMask) ++
      UInt256.toByteArray second ++ UInt256.toByteArray third) hd39 mem_cost ?_ (by evm_ov)
  have h96 := catScratchReturn3Mem_read128_96 (UInt256.land first solcAddrMask) second third hscratch
  convert h96 using 2

/-! ### return encoding for the `(address, uint256, uint256)` tuple -/

theorem catAddrUintUintReturnEncoding (w chop dunk : UInt256) :
    encodeReturnValues? [addr, uint256, uint256]
      [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat),
        .int (Int.ofNat chop.toNat), .int (Int.ofNat dunk.toNat)] =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask) ++
        UInt256.toByteArray chop ++ UInt256.toByteArray dunk) := by
  have hencFlip :
      encodeABIValue? addr (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land w solcAddrMask)) := by
    have hcanon := solcAddrMask_result_canonical w
    have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land w solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask :=
      u256_ofNat_toNat _
    simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]
  have hencChop :
      encodeABIValue? uint256 (.int (Int.ofNat chop.toNat)) =
        some (EVM.Word.toBytesBE chop) := by
    have hword : EVM.word chop.toNat = chop := u256_ofNat_toNat chop
    have hlt : chop.toNat < EVM.twoPow 256 := chop.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencDunk :
      encodeABIValue? uint256 (.int (Int.ofNat dunk.toNat)) =
        some (EVM.Word.toBytesBE dunk) := by
    have hword : EVM.word dunk.toNat = dunk := u256_ofNat_toNat dunk
    have hlt : dunk.toNat < EVM.twoPow 256 := dunk.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray (UInt256.land w solcAddrMask) =
      (EVM.Word.toBytesBE (UInt256.land w solcAddrMask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray (UInt256.land w solcAddrMask)).symm]
  rw [show UInt256.toByteArray chop = (EVM.Word.toBytesBE chop).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray chop).symm]
  rw [show UInt256.toByteArray dunk = (EVM.Word.toBytesBE dunk).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray dunk).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [addr, uint256, uint256] = some 96 by native_decide]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencFlip]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType addr = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencChop]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencDunk]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.append_assoc]

/-! ### dispatch + reach the ilks body at pc 635 -/

theorem catDispatch_ilks {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩) :
    dispatchMsg contract I.calldata = some ilksTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition])
    (post := [litterTransition, liveTransition, relyTransition, vatTransition, vowTransition,
      wardsTransition])
    (ti := ilksTransition)
    (htr := by rfl)
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes, fileIlkFlipSelectorBytes,
        fileIlkUintSelectorBytes, fileUintSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, ilksSelectorBytes]
    exact hsel

theorem catReachIlksBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨635⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : catSelWord I = ⟨3647180086⟩ :=
    catSelWord_eq_of_beq I hsz 0xd9 0x63 0x8d 0x36 ⟨3647180086⟩ (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc 1))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  exact catReachHighHighBody 1 (by omega) ⟨635⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

/-! ### Solm-side body execution -/

theorem catIlksBodyReturns {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals = (∅ : Store).insert "arg0" (ilksArgValue I)) :
    ExecTransitionBody config contract evm locals ilksTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
              (UInt256.land (catSlotWord (ilksFlipSlotFor I) evm.accountMap evm.executionEnv)
                solcAddrMask).toNat)),
          (.int (Int.ofNat
            (catSlotWord (ilksChopSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
            (catSlotWord (ilksDunkSlotFor I) evm.accountMap evm.executionEnv).toNat))])) := by
  subst locals
  let frame : Frame :=
    { contract := contract, locals := (∅ : Store).insert "arg0" (ilksArgValue I) }
  have hflip :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "flip")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land (catSlotWord (ilksFlipSlotFor I) evm.accountMap evm.executionEnv)
            solcAddrMask).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "flip") (er := ilksFlipEvaledRef I)
      (t := .address) (loc := addrLoc (ilksFlipSlotFor I))
      (value := .address (AccountAddress.ofNat
        (UInt256.land (catSlotWord (ilksFlipSlotFor I) evm.accountMap evm.executionEnv)
          solcAddrMask).toNat))
      (by simp [frame, ilksF])
      (by
        have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
        simp [frame, ilksFlipEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, IlkStructTy, addrSt, uint256St])
      (by rfl)
      (by simpa [catSlotWord] using catStorageLocLoad_address_offset0 evm (ilksFlipSlotFor I))
  have hchop :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "chop")) =
        .ok (.int (Int.ofNat
          (catSlotWord (ilksChopSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "chop") (er := ilksChopEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksChopSlotFor I))
      (value := .int (Int.ofNat
        (catSlotWord (ilksChopSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
        simp [frame, ilksChopEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, IlkStructTy, addrSt, uint256St])
      (by rfl)
      (by simpa [catSlotWord] using catStorageLocLoad_uint256 evm (ilksChopSlotFor I))
  have hdunk :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "dunk")) =
        .ok (.int (Int.ofNat
          (catSlotWord (ilksDunkSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "dunk") (er := ilksDunkEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksDunkSlotFor I))
      (value := .int (Int.ofNat
        (catSlotWord (ilksDunkSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
        simp [frame, ilksDunkEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, IlkStructTy, addrSt, uint256St])
      (by rfl)
      (by simpa [catSlotWord] using catStorageLocLoad_uint256 evm (ilksDunkSlotFor I))
  have hreturns :
      evalExprs? config frame evm
        [.storage (ilksF (.var "arg0") "flip"), .storage (ilksF (.var "arg0") "chop"),
          .storage (ilksF (.var "arg0") "dunk")] =
          .ok
            [ .address (AccountAddress.ofNat
                (UInt256.land (catSlotWord (ilksFlipSlotFor I) evm.accountMap evm.executionEnv)
                  solcAddrMask).toNat),
              .int (Int.ofNat
                (catSlotWord (ilksChopSlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (catSlotWord (ilksDunkSlotFor I) evm.accountMap evm.executionEnv).toNat) ] := by
    simp [evalExprs?, hflip, hchop, hdunk, EvalResult.bind, bind, pure]
  simpa [ilksTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

/-! ### body core (≥36 bytes calldata) and short-calldata revert -/

theorem catIlksBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
        (transitionSignature ilksTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (ilksArgValue I)))
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let flipSlot := solcMappingSlot ⟨1⟩ (ilksArgWord I)
  let chopSlot := flipSlot + ⟨1⟩
  let dunkSlot := flipSlot + ⟨2⟩
  let flipWord := catSlotWord flipSlot σ_evm I
  let chopWord := catSlotWord chopSlot σ_evm I
  let dunkWord := catSlotWord dunkSlot σ_evm I
  let locals : Store := (∅ : Store).insert "arg0" (ilksArgValue I)
  have hflipSlot : ilksFlipSlotFor I = flipSlot := by
    simp [flipSlot, ilksFlipSlotFor_eq hsz36]
  have hchopSlot : ilksChopSlotFor I = chopSlot := by
    simp [chopSlot, flipSlot, ilksChopSlotFor_eq hsz36]
  have hdunkSlot : ilksDunkSlotFor I = dunkSlot := by
    simp [dunkSlot, flipSlot, ilksDunkSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals ilksTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
                (UInt256.land (catSlotWord (ilksFlipSlotFor I) σ_solm I) solcAddrMask).toNat)),
            (.int (Int.ofNat (catSlotWord (ilksChopSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (catSlotWord (ilksDunkSlotFor I) σ_solm I).toNat))])) := by
    simpa [locals, initState, catSlotWord] using
      catIlksBodyReturns hsz36
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (by simp only [initState]; exact hwv) rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨635⟩) (ret := ⟨664⟩)
    (decoded := ⟨657⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have htoRoutine : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3215⟩
      (ilksArgWord I :: ⟨664⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    have rd658 := hdecoded.jumpdest (by native_decide) (by evm_ov)
    have rd659 := rd658.pop (by native_decide) (by evm_ov)
    have rd660 := rd659.calldataload (by native_decide) (by evm_ov)
    have rd663 := rd660.push2 ⟨3215⟩ (by native_decide) (by evm_ov)
    exact ⟨_, _, by
      simpa [ilksArgWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
        using rd663.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, htoRoutineRd⟩ := htoRoutine
  obtain ⟨_, _, hretPc⟩ := RD.catIlksStructGetter
    (code := catBytecode) (pc := ⟨3215⟩) (key := ilksArgWord I) (ret := ⟨664⟩)
    (R := [sel]) (by simpa using htoRoutineRd)
    (by
      unfold catIlksStructGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret catBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (UInt256.land flipWord solcAddrMask) ++
          UInt256.toByteArray chopWord ++ UInt256.toByteArray dunkWord) := by
    have hret' := RD.catIlksReturnFromMem
      (pc := ⟨664⟩) (first := UInt256.land flipWord solcAddrMask)
      (second := chopWord) (third := dunkWord) (ret := ⟨664⟩)
      (R := [sel]) (mem := solcMappingHashMem ⟨1⟩ (ilksArgWord I))
      (by
        simpa [flipWord, chopWord, dunkWord, flipSlot, chopSlot, dunkSlot, catSlotWord] using hretPc)
      (by
        unfold catIlksReturnFromMemWf
        repeat' first | apply And.intro | native_decide)
      (solcMappingHashMem_mload64 ⟨1⟩ (ilksArgWord I))
      (solcMappingHashMem_size ⟨1⟩ (ilksArgWord I))
      (solcMappingHashMem_read64 ⟨1⟩ (ilksArgWord I))
      (by simp)
    have hidem :
        UInt256.land (UInt256.land flipWord solcAddrMask) solcAddrMask =
          UInt256.land flipWord solcAddrMask :=
      solcAddrMask_clean (solcAddrMask_result_canonical flipWord)
    simpa [hidem] using hret'
  have hflipWord : catSlotWord flipSlot σ_evm I = catSlotWord flipSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner flipSlot ⟨0⟩
  have hchopWord : catSlotWord chopSlot σ_evm I = catSlotWord chopSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner chopSlot ⟨0⟩
  have hdunkWord : catSlotWord dunkSlot σ_evm I = catSlotWord dunkSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner dunkSlot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat
              (UInt256.land (catSlotWord (ilksFlipSlotFor I) σ_solm I) solcAddrMask).toNat),
          Value.int (Int.ofNat (catSlotWord (ilksChopSlotFor I) σ_solm I).toNat),
          Value.int (Int.ofNat (catSlotWord (ilksDunkSlotFor I) σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat
              (UInt256.land flipWord solcAddrMask).toNat),
          Value.int (Int.ofNat chopWord.toNat),
          Value.int (Int.ofNat dunkWord.toNat)] := by
    rw [hflipSlot, hchopSlot, hdunkSlot]
    simp [flipWord, chopWord, dunkWord, hflipWord, hchopWord, hdunkWord]
  have henc :
      returnEquiv
        (UInt256.toByteArray (UInt256.land flipWord solcAddrMask) ++
          UInt256.toByteArray chopWord ++ UInt256.toByteArray dunkWord)
        (some [(.address (AccountAddress.ofNat (UInt256.land flipWord solcAddrMask).toNat)),
          (.int (Int.ofNat chopWord.toNat)), (.int (Int.ofNat dunkWord.toNat))])
        ilksTransition.returnType := by
    rw [show ilksTransition.returnType = [addr, uint256, uint256] by rfl]
    exact returnEquiv.returned rfl (catAddrUintUintReturnEncoding flipWord chopWord dunkWord)
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem catIlksBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := catBytecode) (sel := sel) (entry := ⟨635⟩) (ret := ⟨664⟩)
    (decoded := ⟨657⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (catDecode_ilks_none_short hsz4 hshort)

theorem catIlksBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some ilksTransition :=
    catDispatch_ilks hsel
  have hreach := catReachIlksBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact catIlksBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (catDecode_ilks_ok hsz36) hreach hAccounts
  · exact catIlksBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Cat
