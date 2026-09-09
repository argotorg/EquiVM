import Benchmarks.Dss.Spot.Dispatch
import Benchmarks.Dss.Jug.Ilks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

/-! ## `ilks(bytes32)` struct mapping getter -/

abbrev ilksArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev ilksArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev ilksArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksPipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "pip"] }

abbrev ilksMatEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "mat"] }

abbrev ilksPipSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (ilksArgKey I)

abbrev ilksMatSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksPipSlotFor I + ⟨1⟩

theorem spotDecode_ilks_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (ilksArgValue I)) := by
  simpa [config, ilksTransition, ilksArgValue, ilksArgBytes, bytes32, bytes32Width] using
    (Benchmarks.Dss.Jug.decodeCalldataWithMode_legacyBytes32_ok
      (cd := I.calldata) (x := "arg0") hsz36)

theorem spotDecode_ilks_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata = none := by
  simpa [config, ilksTransition, bytes32, bytes32Width] using
    (Benchmarks.Dss.Jug.decodeCalldataWithMode_legacyBytes32_none_short
      (cd := I.calldata) (x := "arg0") hsz4 hshort)

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

theorem ilksArgBytes_len32 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (ilksArgBytes I).length = 32 := by
  have hlen := ilksArgBytes_len (I := I) hsz36
  simpa [bytes32Width] using hlen

theorem keyValueToWord_ilksArgKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (ilksArgKey I) = ilksArgWord I := by
  have hlen32 : (ilksArgBytes I).length = 32 :=
    ilksArgBytes_len32 (I := I) hsz36
  have hword : ABI.bytesToWord (ilksArgBytes I) = ilksArgWord I := by
    simpa [ilksArgBytes, ilksArgWord] using
      (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
  have hbytes : ilksArgBytes I = EVM.Word.toBytesBE (ilksArgWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := ilksArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [ilksArgKey, bytes32Width, hbytes] using keyValueToWord_fixedBytes32 (ilksArgWord I)

theorem ilksPipSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksPipSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) := by
  unfold ilksPipSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_ilksArgKey hsz36]

theorem ilksMatSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksMatSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) + ⟨1⟩ := by
  simp [ilksMatSlotFor, ilksPipSlotFor_eq hsz36]

theorem addressUint256PairReturnEncoding (first second : UInt256) :
    encodeReturnValues? [addr, uint256]
      [.address (AccountAddress.ofNat (UInt256.land first solcAddrMask).toNat),
        .int (Int.ofNat second.toNat)] =
        some (UInt256.toByteArray (UInt256.land first solcAddrMask) ++
          UInt256.toByteArray second) := by
  have hencFirst :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (UInt256.land first solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land first solcAddrMask)) := by
    have hcanon := solcAddrMask_result_canonical first
    have haddrMod : (UInt256.land first solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land first solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hword :
        EVM.word (UInt256.land first solcAddrMask).toNat =
          UInt256.land first solcAddrMask :=
      u256_ofNat_toNat _
    simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]
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
  rw [show UInt256.toByteArray (UInt256.land first solcAddrMask) =
      (EVM.Word.toBytesBE (UInt256.land first solcAddrMask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray
      (UInt256.land first solcAddrMask)).symm]
  rw [show UInt256.toByteArray second = (EVM.Word.toBytesBE second).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray second).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [addr, uint256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencFirst]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType addr = false by decide +native]
  unfold encodeABIValuesFrom?
  rw [hencSecond]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by decide +native]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

@[reducible] def spotIlksStructGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  let p25 := p23 + UInt256.ofNat 2
  let p27 := p25 + UInt256.ofNat 2
  let p29 := p27 + UInt256.ofNat 2
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
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
  ∧ decode code p23 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p25 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p27 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p29 = some (.SHL, .none)
  ∧ decode code p30 = some (.SUB, .none)
  ∧ decode code p31 = some (.SWAP1, .none)
  ∧ decode code p32 = some (.SWAP2, .none)
  ∧ decode code p33 = some (.AND, .none)
  ∧ decode code p34 = some (.SWAP1, .none)
  ∧ decode code p35 = some (.DUP3, .none)
  ∧ decode code p36 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.spotIlksStructGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : spotIlksStructGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee ((solcMappingSlot ⟨1⟩ key) + ⟨1⟩) ::
        UInt256.land solcAddrMask (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key)) ::
        ret :: R)
      (solcMappingHashMem ⟨1⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd25, hd27, hd29, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36⟩
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
  have rd25 := rd23.push1 ⟨1⟩ hd23 (by evm_ov)
  have rd27 := rd25.push1 ⟨1⟩ hd25 (by evm_ov)
  have rd29 := rd27.push1 ⟨160⟩ hd27 (by evm_ov)
  have rd30 := rd29.shl hd29 (by evm_ov)
  have rd31 := rd30.sub hd30 (by evm_ov)
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd31
  have rd32 := rd31.swap1 hd31 (by evm_ov)
  have rd33 := rd32.swap2 hd32 (by evm_ov)
  have rd34 := rd33.and hd33 (by evm_ov)
  have rd35 := rd34.swap1 hd34 (by evm_ov)
  have rd36 := rd35.dup3 hd35 (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_add_comm, u256_land_comm] using
      rd36.jump hd36 hret (by evm_ov)⟩

@[reducible] def solcAddressUintReturnFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  ∧ decode code p14 = some (.SWAP4, .none)
  ∧ decode code p15 = some (.AND, .none)
  ∧ decode code p16 = some (.DUP4, .none)
  ∧ decode code p17 = some (.MSTORE, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p20 = some (.DUP4, .none)
  ∧ decode code p21 = some (.ADD, .none)
  ∧ decode code p22 = some (.SWAP2, .none)
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.SWAP2, .none)
  ∧ decode code p25 = some (.MSTORE, .none)
  ∧ decode code p26 = some (.DUP1, .none)
  ∧ decode code p27 = some (.MLOAD, .none)
  ∧ decode code p28 = some (.SWAP2, .none)
  ∧ decode code p29 = some (.DUP3, .none)
  ∧ decode code p30 = some (.SWAP1, .none)
  ∧ decode code p31 = some (.SUB, .none)
  ∧ decode code p32 = some (.ADD, .none)
  ∧ decode code p33 = some (.SWAP1, .none)
  ∧ decode code p34 = some (.RETURN, .none)

theorem RD.solcAddressUintReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc first second ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (second :: first :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcAddressUintReturnFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hscratch : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land first solcAddrMask) ++ UInt256.toByteArray second) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16,
      hd17, hd18, hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29,
      hd30, hd31, hd32, hd33, hd34⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨1⟩ hd7 (by evm_ov),
    raw push1 ⟨160⟩ hd9 (by evm_ov),
    raw shl hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap4 hd14 (by evm_ov),
    raw and hd15 (by evm_ov),
    raw dup4 hd16 (by evm_ov),
    raw mstore 6 (solcScratchReturnMem mem (UInt256.land first solcAddrMask))
      (UInt256.ofNat 5) hd17 mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide,
          show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov),
    raw dup4 hd20 (by evm_ov),
    raw add hd21 (by evm_ov),
    raw swap2 hd22 (by evm_ov),
    raw swap1 hd23 (by evm_ov),
    raw swap2 hd24 (by evm_ov),
    raw mstore 3
      (Benchmarks.Dss.Jug.solcScratchReturn2Mem mem (UInt256.land first solcAddrMask)
        second)
      (UInt256.ofNat 6) hd25 mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup1 hd26 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) hd27 mem_cost
      (Benchmarks.Dss.Jug.solcScratchReturn2Mem_mload64
        (UInt256.land first solcAddrMask) second hscratch hread64)
      (by decide) (by evm_ov),
    raw swap2 hd28 (by evm_ov),
    raw dup3 hd29 (by evm_ov),
    raw swap1 hd30 (by evm_ov),
    raw sub hd31 (by evm_ov),
    raw add hd32 (by evm_ov),
    raw swap1 hd33 (by evm_ov),
    raw ret 0
      (UInt256.toByteArray (UInt256.land first solcAddrMask) ++ UInt256.toByteArray second)
      hd34 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rw [show (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨64⟩).toNat = 64
          from by decide]
        exact Benchmarks.Dss.Jug.solcScratchReturn2Mem_read128_64
          (UInt256.land first solcAddrMask) second hscratch)
      (by evm_ov)]

theorem spotIlksBodyReturns {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals = (∅ : Store).insert "arg0" (ilksArgValue I)) :
    ExecTransitionBody config contract evm locals ilksTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (spotAddressReturnWord (ilksPipSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (spotSlotWord (ilksMatSlotFor I) evm.accountMap evm.executionEnv).toNat))])) := by
  subst locals
  let frame : Frame := { contract := contract, locals := (∅ : Store).insert "arg0" (ilksArgValue I) }
  have hpip :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "pip")) =
        .ok (.address (AccountAddress.ofNat
          (spotAddressReturnWord (ilksPipSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "pip") (er := ilksPipEvaledRef I)
      (t := .address) (loc := addrLoc (ilksPipSlotFor I))
      (value := .address (AccountAddress.ofNat
        (spotAddressReturnWord (ilksPipSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
        simp [frame, ilksPipEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, IlkStructTy, addrSt])
      (by rfl)
      (by
        simpa [spotAddressReturnWord, spotSlotWord] using
          spotStorageLocLoad_address_offset0 evm (ilksPipSlotFor I))
  have hmat :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "mat")) =
        .ok (.int (Int.ofNat
          (spotSlotWord (ilksMatSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "mat") (er := ilksMatEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksMatSlotFor I))
      (value := .int (Int.ofNat
        (spotSlotWord (ilksMatSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
        simp [frame, ilksMatEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, IlkStructTy, uint256St])
      (by rfl)
      (by simpa [spotSlotWord] using spotStorageLocLoad_uint256 evm (ilksMatSlotFor I))
  have hreturns :
      evalExprs? config frame evm
        [.storage (ilksF (.var "arg0") "pip"), .storage (ilksF (.var "arg0") "mat")] =
          .ok
            [ .address (AccountAddress.ofNat
                (spotAddressReturnWord (ilksPipSlotFor I) evm.accountMap
                  evm.executionEnv).toNat),
              .int (Int.ofNat
                (spotSlotWord (ilksMatSlotFor I) evm.accountMap
                  evm.executionEnv).toNat) ] := by
    simp [evalExprs?, hpip, hmat, EvalResult.bind, bind, pure]
  simpa [ilksTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

theorem spotReachIlksBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 5)) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨484⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : spotSelWord I = ⟨0xd9638d36⟩ :=
    spotSelWord_eq_of_beq I hsz 0xd9 0x63 0x8d 0x36 ⟨0xd9638d36⟩
      (by decide +native) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc 4))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact spotReachHighBody 4 (by omega) ⟨484⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by decide +native)

theorem spotIlksBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
        (transitionSignature ilksTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (ilksArgValue I)))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨484⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let pipSlot := solcMappingSlot ⟨1⟩ (ilksArgWord I)
  let matSlot := pipSlot + ⟨1⟩
  let pipWord := spotSlotWord pipSlot σ_evm I
  let matWord := spotSlotWord matSlot σ_evm I
  let locals : Store := (∅ : Store).insert "arg0" (ilksArgValue I)
  have hpipSlot : ilksPipSlotFor I = pipSlot := by
    simp [pipSlot, ilksPipSlotFor_eq hsz36]
  have hmatSlot : ilksMatSlotFor I = matSlot := by
    simp [matSlot, pipSlot, ilksMatSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals ilksTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (spotAddressReturnWord (ilksPipSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (spotSlotWord (ilksMatSlotFor I) σ_solm I).toNat))])) := by
    simpa [locals, initState] using
      spotIlksBodyReturns hsz36
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (by simp only [initState]; exact hwv) rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := spotBytecode) (sel := sel) (entry := ⟨484⟩) (ret := ⟨513⟩)
    (decoded := ⟨506⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have htoRoutine : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1800⟩
      (ilksArgWord I :: ⟨513⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    have rd507 := hdecoded.jumpdest (by decide +native) (by evm_ov)
    have rd508 := rd507.pop (by decide +native) (by evm_ov)
    have rd509 := rd508.calldataload (by decide +native) (by evm_ov)
    have rd512 := rd509.push2 ⟨1800⟩ (by decide +native) (by evm_ov)
    exact ⟨_, _, by
      simpa [ilksArgWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
        using rd512.jump (by decide +native) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, htoRoutineRd⟩ := htoRoutine
  obtain ⟨_, _, hretPc⟩ := RD.spotIlksStructGetter
    (code := spotBytecode) (pc := ⟨1800⟩) (key := ilksArgWord I) (ret := ⟨513⟩)
    (R := [sel]) (by simpa using htoRoutineRd)
    (by
      unfold spotIlksStructGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by simp)
  have hret :
      RDret spotBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (UInt256.land pipWord solcAddrMask) ++
          UInt256.toByteArray matWord) := by
    have hret' := RD.solcAddressUintReturnFromMem
      (pc := ⟨513⟩)
      (first := UInt256.land solcAddrMask pipWord) (second := matWord) (ret := ⟨513⟩)
      (R := [sel]) (mem := solcMappingHashMem ⟨1⟩ (ilksArgWord I))
      (by
        simpa [pipWord, matWord, pipSlot, matSlot, spotSlotWord] using hretPc)
      (by
        unfold solcAddressUintReturnFromMemWf
        repeat' first | apply And.intro | decide +native)
      (solcMappingHashMem_mload64 ⟨1⟩ (ilksArgWord I))
      (solcMappingHashMem_size ⟨1⟩ (ilksArgWord I))
      (solcMappingHashMem_read64 ⟨1⟩ (ilksArgWord I))
      (by simp)
    have hclean :
        UInt256.land (UInt256.land solcAddrMask pipWord) solcAddrMask =
          UInt256.land pipWord solcAddrMask := by
      rw [u256_land_comm solcAddrMask pipWord]
      exact solcAddrMask_clean (solcAddrMask_result_canonical pipWord)
    simpa [hclean, u256_land_comm] using hret'
  have hpipWord : spotSlotWord pipSlot σ_evm I = spotSlotWord pipSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner pipSlot ⟨0⟩
  have hmatWord : spotSlotWord matSlot σ_evm I = spotSlotWord matSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner matSlot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat
          (spotAddressReturnWord (ilksPipSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (spotSlotWord (ilksMatSlotFor I) σ_solm I).toNat)] =
      some [Value.address (AccountAddress.ofNat (UInt256.land pipWord solcAddrMask).toNat),
        Value.int (Int.ofNat matWord.toNat)] := by
    rw [hpipSlot, hmatSlot]
    simp [spotAddressReturnWord, pipWord, matWord, hpipWord, hmatWord]
  have henc :
      returnEquiv
        (UInt256.toByteArray (UInt256.land pipWord solcAddrMask) ++ UInt256.toByteArray matWord)
        (some [(.address (AccountAddress.ofNat (UInt256.land pipWord solcAddrMask).toNat)),
          (.int (Int.ofNat matWord.toNat))])
        ilksTransition.returnType := by
    rw [show ilksTransition.returnType = [addr, uint256] by rfl]
    exact returnEquiv.returned rfl (addressUint256PairReturnEncoding pipWord matWord)
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem spotIlksBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨484⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := spotBytecode) (sel := sel) (entry := ⟨484⟩) (ret := ⟨513⟩)
    (decoded := ⟨506⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (spotDecode_ilks_none_short hsz4 hshort)

theorem spotIlksBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 5) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some ilksTransition :=
    spotDispatchIlks hsel
  have hreach := spotReachIlksBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact spotIlksBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (spotDecode_ilks_ok hsz36) hreach hAccounts
  · exact spotIlksBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Spot
