import Benchmarks.Dss.Dog.Dispatch
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Dog.Immutables

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Dog

/-! ## `ilks(bytes32)` struct mapping getter -/

abbrev ilksArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev ilksArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev ilksArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (ilksArgValue I)

abbrev ilksClipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "clip"] }

abbrev ilksChopEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "chop"] }

abbrev ilksHoleEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "hole"] }

abbrev ilksDirtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "dirt"] }

abbrev ilksClipSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (ilksArgKey I)

abbrev ilksChopSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksClipSlotFor I + ⟨1⟩

abbrev ilksHoleSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksClipSlotFor I + ⟨2⟩

abbrev ilksDirtSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksClipSlotFor I + ⟨3⟩

theorem dogDecode_ilks_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata =
        some (ilksLocals I) := by
  simpa [config, ilksTransition, ilksLocals, ilksArgValue, ilksArgBytes, bytes32,
    bytes32Width] using
    (dogDecodeCalldataWithMode_legacyBytes32_ok (cd := I.calldata) (x := "arg0")
      hsz36)

theorem dogDecode_ilks_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata = none := by
  simpa [config, ilksTransition, bytes32, bytes32Width] using
    (dogDecodeCalldataWithMode_legacyBytes32_none_short (cd := I.calldata) (x := "arg0")
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
  simpa [ilksArgKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (ilksArgWord I)

theorem ilksClipSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksClipSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) := by
  unfold ilksClipSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_ilksArgKey hsz36]

theorem ilksChopSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksChopSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) + ⟨1⟩ := by
  simp [ilksChopSlotFor, ilksClipSlotFor_eq hsz36]

theorem ilksHoleSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksHoleSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) + ⟨2⟩ := by
  simp [ilksHoleSlotFor, ilksClipSlotFor_eq hsz36]

theorem ilksDirtSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksDirtSlotFor I = solcMappingSlot ⟨1⟩ (ilksArgWord I) + ⟨3⟩ := by
  simp [ilksDirtSlotFor, ilksClipSlotFor_eq hsz36]

theorem dogIlksReturnEncoding (clip chop hole dirt : UInt256) :
    encodeReturnValues? [addr, uint256, uint256, uint256]
      [.address (AccountAddress.ofNat (UInt256.land clip solcAddrMask).toNat),
        .int (Int.ofNat chop.toNat), .int (Int.ofNat hole.toNat),
        .int (Int.ofNat dirt.toNat)] =
        some (UInt256.toByteArray (UInt256.land clip solcAddrMask) ++
          UInt256.toByteArray chop ++ UInt256.toByteArray hole ++ UInt256.toByteArray dirt) := by
  have hencAddr :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (UInt256.land clip solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land clip solcAddrMask)) := by
    have hcanon := solcAddrMask_result_canonical clip
    have haddrMod : (UInt256.land clip solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land clip solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hword :
        EVM.word (UInt256.land clip solcAddrMask).toNat =
          UInt256.land clip solcAddrMask :=
      u256_ofNat_toNat _
    simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]
  have hencUint : ∀ w : UInt256,
      encodeABIValue? uint256 (.int (Int.ofNat w.toNat)) =
        some (EVM.Word.toBytesBE w) := by
    intro w
    have hword : EVM.word w.toNat = w := by
      show UInt256.ofNat w.toNat = w
      exact u256_ofNat_toNat w
    have hlt : w.toNat < EVM.twoPow 256 := by
      change w.val.val < EVM.twoPow 256
      exact w.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray (UInt256.land clip solcAddrMask) =
      (EVM.Word.toBytesBE (UInt256.land clip solcAddrMask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray
      (UInt256.land clip solcAddrMask)).symm]
  rw [show UInt256.toByteArray chop = (EVM.Word.toBytesBE chop).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray chop).symm]
  rw [show UInt256.toByteArray hole = (EVM.Word.toBytesBE hole).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray hole).symm]
  rw [show UInt256.toByteArray dirt = (EVM.Word.toBytesBE dirt).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray dirt).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [addr, uint256, uint256, uint256] = some 128 by
    native_decide]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencAddr]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType addr = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencUint chop]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencUint hole]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencUint dirt]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

noncomputable abbrev dogIlksReturnMem
    (mem : ByteArray) (clip chop hole dirt : UInt256) : ByteArray :=
  writeCascade mem
    [(128, UInt256.land clip solcAddrMask), (160, chop), (192, hole), (224, dirt)]

theorem dogIlksReturnMem_size {mem : ByteArray} (clip chop hole dirt : UInt256)
    (hmem : mem.size = 96) :
    (dogIlksReturnMem mem clip chop hole dirt).size = 256 := by
  unfold dogIlksReturnMem
  exact writeCascade_size_of_base mem _ hmem
    (by
      simp [WriteGapsOk]
      exact lt_usize 32 (by norm_num))
    (by norm_num [writeCascadeSize])

theorem dogIlksReturnMem_read64 {mem : ByteArray} (clip chop hole dirt : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dogIlksReturnMem mem clip chop hole dirt).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold dogIlksReturnMem
  rw [writeCascade_read_preserved_of_base mem _ hmem
    (by
      simp [WindowDisjointFromWrites]
      exact lt_usize 32 (by norm_num))]
  exact hread64

theorem dogIlksReturnMem_mload64 {mem : ByteArray} (clip chop hole dirt : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (dogIlksReturnMem mem clip chop hole dirt).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((dogIlksReturnMem mem clip chop hole dirt).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [dogIlksReturnMem_size clip chop hole dirt hmem]; decide)
    (by decide)
    (dogIlksReturnMem_read64 clip chop hole dirt hmem hread64)

theorem dogIlksReturnMem_read128 {mem : ByteArray} (clip chop hole dirt : UInt256)
    (hmem : mem.size = 96) :
    (dogIlksReturnMem mem clip chop hole dirt).readWithPadding 128 128 =
      UInt256.toByteArray (UInt256.land clip solcAddrMask) ++
        UInt256.toByteArray chop ++ UInt256.toByteArray hole ++ UInt256.toByteArray dirt := by
  let out := dogIlksReturnMem mem clip chop hole dirt
  have hsize : out.size = 256 := dogIlksReturnMem_size clip chop hole dirt hmem
  have h128 : out.readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.land clip solcAddrMask) := by
    unfold out dogIlksReturnMem
    exact writeCascade_read_word_of_head_of_base mem
      (base := 96) (off := 128) (word := UInt256.land clip solcAddrMask)
      (rest := [(160, chop), (192, hole), (224, dirt)])
      hmem (by native_decide) (by simp [WindowDisjointFromWrites])
  have h160 : out.readWithPadding 160 32 = UInt256.toByteArray chop := by
    unfold out dogIlksReturnMem
    rw [writeCascade_cons]
    let mem1 := writeWord mem 128 (UInt256.land clip solcAddrMask)
    have hmem1 : mem1.size = 160 := by
      have h := writeWord_size mem 128 (UInt256.land clip solcAddrMask)
        (by rw [hmem]; native_decide)
      simpa [mem1, hmem] using h
    exact writeCascade_read_word_of_head_of_base mem1
      (base := 160) (off := 160) (word := chop) (rest := [(192, hole), (224, dirt)])
      hmem1 (by native_decide) (by simp [WindowDisjointFromWrites])
  have h192 : out.readWithPadding 192 32 = UInt256.toByteArray hole := by
    unfold out dogIlksReturnMem
    rw [writeCascade_cons, writeCascade_cons]
    let mem1 := writeWord mem 128 (UInt256.land clip solcAddrMask)
    let mem2 := writeWord mem1 160 chop
    have hmem1 : mem1.size = 160 := by
      have h := writeWord_size mem 128 (UInt256.land clip solcAddrMask)
        (by rw [hmem]; native_decide)
      simpa [mem1, hmem] using h
    have hmem2 : mem2.size = 192 := by
      have h := writeWord_size mem1 160 chop (by rw [hmem1]; native_decide)
      simpa [mem2, hmem1] using h
    exact writeCascade_read_word_of_head_of_base mem2
      (base := 192) (off := 192) (word := hole) (rest := [(224, dirt)])
      hmem2 (by native_decide) (by simp [WindowDisjointFromWrites])
  have h224 : out.readWithPadding 224 32 = UInt256.toByteArray dirt := by
    unfold out dogIlksReturnMem
    rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
    let mem1 := writeWord mem 128 (UInt256.land clip solcAddrMask)
    let mem2 := writeWord mem1 160 chop
    let mem3 := writeWord mem2 192 hole
    have hmem1 : mem1.size = 160 := by
      have h := writeWord_size mem 128 (UInt256.land clip solcAddrMask)
        (by rw [hmem]; native_decide)
      simpa [mem1, hmem] using h
    have hmem2 : mem2.size = 192 := by
      have h := writeWord_size mem1 160 chop (by rw [hmem1]; native_decide)
      simpa [mem2, hmem1] using h
    have hmem3 : mem3.size = 224 := by
      have h := writeWord_size mem2 192 hole (by rw [hmem2]; native_decide)
      simpa [mem3, hmem2] using h
    exact writeCascade_read_word_of_head_of_base mem3
      (base := 224) (off := 224) (word := dirt) (rest := [])
      hmem3 (by native_decide) (by norm_num [WindowDisjointFromWrites])
  rw [byteArray_readWithPadding_split out 128 32 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega)]
  rw [byteArray_readWithPadding_split out 160 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega)]
  rw [byteArray_readWithPadding_split out 192 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega)]
  rw [h128, h160, h192, h224]
  apply ByteArray.ext
  simp [ByteArray.data_append]

@[reducible] def dogIlksStructGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p37 := p35 + UInt256.ofNat 2
  let p39 := p37 + UInt256.ofNat 2
  let p41 := p39 + UInt256.ofNat 2
  let p42 := p41 + ⟨1⟩
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
  let p48 := p47 + ⟨1⟩
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
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
  ∧ decode code p26 = some (.DUP3, .none)
  ∧ decode code p27 = some (.ADD, .none)
  ∧ decode code p28 = some (.SLOAD, .none)
  ∧ decode code p29 = some (.Push .PUSH1, some (⟨3⟩, 1))
  ∧ decode code p31 = some (.SWAP1, .none)
  ∧ decode code p32 = some (.SWAP3, .none)
  ∧ decode code p33 = some (.ADD, .none)
  ∧ decode code p34 = some (.SLOAD, .none)
  ∧ decode code p35 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p37 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p39 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p41 = some (.SHL, .none)
  ∧ decode code p42 = some (.SUB, .none)
  ∧ decode code p43 = some (.SWAP1, .none)
  ∧ decode code p44 = some (.SWAP4, .none)
  ∧ decode code p45 = some (.AND, .none)
  ∧ decode code p46 = some (.SWAP3, .none)
  ∧ decode code p47 = some (.SWAP1, .none)
  ∧ decode code p48 = some (.SWAP2, .none)
  ∧ decode code p49 = some (.SWAP1, .none)
  ∧ decode code p50 = some (.DUP5, .none)
  ∧ decode code p51 = some (.JUMP, .none)

theorem RD.dogIlksStructGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : dogIlksStructGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨3⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨2⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨1⟩) ::
        UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key)) solcAddrMask ::
        ret :: R)
      (solcMappingHashMem ⟨1⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24, hd26, hd27, hd28, hd29,
      hd31, hd32, hd33, hd34, hd35, hd37, hd39, hd41, hd42, hd43, hd44, hd45,
      hd46, hd47, hd48, hd49, hd50, hd51⟩
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
  have rd27 := rd26.dup3 hd26 (by evm_ov)
  have rd28 := rd27.add hd27 (by evm_ov)
  obtain ⟨_, _, rd29⟩ := rd28.sload hd28 (by evm_ov)
  have rd31 := rd29.push1 ⟨3⟩ hd29 (by evm_ov)
  have rd32 := rd31.swap1 hd31 (by evm_ov)
  have rd33 := rd32.swap3 hd32 (by evm_ov)
  have rd34 := rd33.add hd33 (by evm_ov)
  obtain ⟨_, _, rd35⟩ := rd34.sload hd34 (by evm_ov)
  have rdMaskedRaw := evm_run rd35 with [
    raw push1 ⟨1⟩ hd35 (by evm_ov),
    raw push1 ⟨1⟩ hd37 (by evm_ov),
    raw push1 ⟨160⟩ hd39 (by evm_ov),
    raw shl hd41 (by evm_ov),
    raw sub hd42 (by evm_ov),
    raw swap1 hd43 (by evm_ov),
    raw swap4 hd44 (by evm_ov),
    raw and hd45 (by evm_ov)]
  have hmaskLiteral (w : UInt256) :
      UInt256.land w (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        UInt256.land w solcAddrMask := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
  exact ⟨_, _, by
    simpa [hmaskLiteral, u256_add_comm] using (evm_run rdMaskedRaw with [
      raw swap3 hd46 (by evm_ov),
      raw swap1 hd47 (by evm_ov),
      raw swap2 hd48 (by evm_ov),
      raw swap1 hd49 (by evm_ov),
      raw dup5 hd50 (by evm_ov),
      raw jump hd51 hret (by evm_ov)])⟩

@[reducible] def dogIlksReturnFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  let p35 := p33 + UInt256.ofNat 2
  let p36 := p35 + ⟨1⟩
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p43 := p42 + ⟨1⟩
  let p45 := p43 + UInt256.ofNat 2
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
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
  ∧ decode code p14 = some (.SWAP6, .none)
  ∧ decode code p15 = some (.AND, .none)
  ∧ decode code p16 = some (.DUP6, .none)
  ∧ decode code p17 = some (.MSTORE, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p20 = some (.DUP6, .none)
  ∧ decode code p21 = some (.ADD, .none)
  ∧ decode code p22 = some (.SWAP4, .none)
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.SWAP4, .none)
  ∧ decode code p25 = some (.MSTORE, .none)
  ∧ decode code p26 = some (.DUP4, .none)
  ∧ decode code p27 = some (.DUP4, .none)
  ∧ decode code p28 = some (.ADD, .none)
  ∧ decode code p29 = some (.SWAP2, .none)
  ∧ decode code p30 = some (.SWAP1, .none)
  ∧ decode code p31 = some (.SWAP2, .none)
  ∧ decode code p32 = some (.MSTORE, .none)
  ∧ decode code p33 = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code p35 = some (.DUP4, .none)
  ∧ decode code p36 = some (.ADD, .none)
  ∧ decode code p37 = some (.MSTORE, .none)
  ∧ decode code p38 = some (.MLOAD, .none)
  ∧ decode code p39 = some (.SWAP1, .none)
  ∧ decode code p40 = some (.DUP2, .none)
  ∧ decode code p41 = some (.SWAP1, .none)
  ∧ decode code p42 = some (.SUB, .none)
  ∧ decode code p43 = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code p45 = some (.ADD, .none)
  ∧ decode code p46 = some (.SWAP1, .none)
  ∧ decode code p47 = some (.RETURN, .none)

theorem RD.dogIlksReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc clip chop hole dirt ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (dirt :: hole :: chop :: clip :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : dogIlksReturnFromMemWf code pc)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land clip solcAddrMask) ++ UInt256.toByteArray chop ++
        UInt256.toByteArray hole ++ UInt256.toByteArray dirt) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16,
      hd17, hd18, hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29,
      hd30, hd31, hd32, hd33, hd35, hd36, hd37, hd38, hd39, hd40, hd41, hd42,
      hd43, hd45, hd46, hd47⟩
  let clipOut := UInt256.land clip solcAddrMask
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost
      (mloadFreePtrValue
        (by rw [hmem]; decide)
        (by decide)
        hread64)
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨1⟩ hd7 (by evm_ov),
    raw push1 ⟨160⟩ hd9 (by evm_ov),
    raw shl hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap6 hd14 (by evm_ov),
    raw and hd15 (by evm_ov),
    raw dup6 hd16 (by evm_ov),
    raw mstore 6 (writeWord mem 128 clipOut)
      (UInt256.ofNat 5) hd17 mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide,
          show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov),
    raw dup6 hd20 (by evm_ov),
    raw add hd21 (by evm_ov),
    raw swap4 hd22 (by evm_ov),
    raw swap1 hd23 (by evm_ov),
    raw swap4 hd24 (by evm_ov),
    raw mstore 3 (writeCascade mem [(128, clipOut), (160, chop)])
      (UInt256.ofNat 6) hd25 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw dup4 hd26 (by evm_ov),
    raw dup4 hd27 (by evm_ov),
    raw add hd28 (by evm_ov),
    raw swap2 hd29 (by evm_ov),
    raw swap1 hd30 (by evm_ov),
    raw swap2 hd31 (by evm_ov),
    raw mstore 3 (writeCascade mem [(128, clipOut), (160, chop), (192, hole)])
      (UInt256.ofNat 7) hd32 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ hd33 (by evm_ov),
    raw dup4 hd35 (by evm_ov),
    raw add hd36 (by evm_ov),
    raw mstore 3 (dogIlksReturnMem mem clip chop hole dirt)
      (UInt256.ofNat 8) hd37 mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by decide]
        rfl)
      (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd38 mem_cost
      (dogIlksReturnMem_mload64 clip chop hole dirt hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hd39 (by evm_ov),
    raw dup2 hd40 (by evm_ov),
    raw swap1 hd41 (by evm_ov),
    raw sub hd42 (by evm_ov),
    raw push1 ⟨128⟩ hd43 (by evm_ov),
    raw add hd45 (by evm_ov),
    raw swap1 hd46 (by evm_ov),
    raw ret 0
      (UInt256.toByteArray (UInt256.land clip solcAddrMask) ++ UInt256.toByteArray chop ++
        UInt256.toByteArray hole ++ UInt256.toByteArray dirt)
      hd47 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact dogIlksReturnMem_read128 clip chop hole dirt hmem)
      (by evm_ov)]

theorem dogIlksBodyReturns {v : DogImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals = ilksLocals I) :
    ExecTransitionBody (config v) (contract v) evm locals ilksTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (dogAddressReturnWord (ilksClipSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat (dogSlotWord (ilksChopSlotFor I) evm.accountMap
            evm.executionEnv).toNat)),
          (.int (Int.ofNat (dogSlotWord (ilksHoleSlotFor I) evm.accountMap
            evm.executionEnv).toNat)),
          (.int (Int.ofNat (dogSlotWord (ilksDirtSlotFor I) evm.accountMap
            evm.executionEnv).toNat))])) := by
  subst locals
  let frame : Frame := { contract := contract v, locals := ilksLocals I }
  have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
  have hclip :
      evalExpr? (config v) frame evm (.storage (ilksF (.var "arg0") "clip")) =
        .ok (.address (AccountAddress.ofNat
          (dogAddressReturnWord (ilksClipSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "clip") (er := ilksClipEvaledRef I)
      (t := .address) (loc := addrLoc (ilksClipSlotFor I))
      (value := .address (AccountAddress.ofNat
        (dogAddressReturnWord (ilksClipSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        simp [frame, ilksClipEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, ilksLocals, hkeyLen])
      (by simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, IlkStructTy, addrSt])
      (by rfl)
      (by simpa [dogAddressReturnWord, dogSlotWord] using
        dogStorageLocLoad_address_offset0 evm (ilksClipSlotFor I))
  have hchop :
      evalExpr? (config v) frame evm (.storage (ilksF (.var "arg0") "chop")) =
        .ok (.int (Int.ofNat
          (dogSlotWord (ilksChopSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "chop") (er := ilksChopEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksChopSlotFor I))
      (value := .int (Int.ofNat
        (dogSlotWord (ilksChopSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        simp [frame, ilksChopEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, ilksLocals, hkeyLen])
      (by simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, IlkStructTy, uint256St])
      (by rfl)
      (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm (ilksChopSlotFor I))
  have hhole :
      evalExpr? (config v) frame evm (.storage (ilksF (.var "arg0") "hole")) =
        .ok (.int (Int.ofNat
          (dogSlotWord (ilksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "hole") (er := ilksHoleEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksHoleSlotFor I))
      (value := .int (Int.ofNat
        (dogSlotWord (ilksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        simp [frame, ilksHoleEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, ilksLocals, hkeyLen])
      (by simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, IlkStructTy, uint256St])
      (by rfl)
      (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm (ilksHoleSlotFor I))
  have hdirt :
      evalExpr? (config v) frame evm (.storage (ilksF (.var "arg0") "dirt")) =
        .ok (.int (Int.ofNat
          (dogSlotWord (ilksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := frame) (evm := evm)
      (slot := ilksF (.var "arg0") "dirt") (er := ilksDirtEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (ilksDirtSlotFor I))
      (value := .int (Int.ofNat
        (dogSlotWord (ilksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, ilksF])
      (by
        simp [frame, ilksDirtEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, ilksLocals, hkeyLen])
      (by simp [frame, ilksArgKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, IlkStructTy, uint256St])
      (by rfl)
      (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm (ilksDirtSlotFor I))
  have hreturns :
      evalExprs? (config v) frame evm
        [.storage (ilksF (.var "arg0") "clip"), .storage (ilksF (.var "arg0") "chop"),
          .storage (ilksF (.var "arg0") "hole"), .storage (ilksF (.var "arg0") "dirt")] =
          .ok
            [ .address (AccountAddress.ofNat
                (dogAddressReturnWord (ilksClipSlotFor I) evm.accountMap
                  evm.executionEnv).toNat),
              .int (Int.ofNat
                (dogSlotWord (ilksChopSlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (dogSlotWord (ilksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (dogSlotWord (ilksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat) ] := by
    simp [evalExprs?, hclip, hchop, hhole, hdirt, EvalResult.bind, bind, pure]
  simpa [ilksTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

theorem dogIlksReturnValuesEquiv {I : ExecutionEnv} {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some [Value.address (AccountAddress.ofNat
        (dogAddressReturnWord (ilksClipSlotFor I) σ_solm I).toNat),
      Value.int (Int.ofNat (dogSlotWord (ilksChopSlotFor I) σ_solm I).toNat),
      Value.int (Int.ofNat (dogSlotWord (ilksHoleSlotFor I) σ_solm I).toNat),
      Value.int (Int.ofNat (dogSlotWord (ilksDirtSlotFor I) σ_solm I).toNat)] =
    some [Value.address (AccountAddress.ofNat
        (dogAddressReturnWord (ilksClipSlotFor I) σ_evm I).toNat),
      Value.int (Int.ofNat (dogSlotWord (ilksChopSlotFor I) σ_evm I).toNat),
      Value.int (Int.ofNat (dogSlotWord (ilksHoleSlotFor I) σ_evm I).toNat),
      Value.int (Int.ofNat (dogSlotWord (ilksDirtSlotFor I) σ_evm I).toNat)] := by
  have hclip :
      dogSlotWord (ilksClipSlotFor I) σ_evm I =
        dogSlotWord (ilksClipSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (ilksClipSlotFor I) ⟨0⟩
  have hchop :
      dogSlotWord (ilksChopSlotFor I) σ_evm I =
        dogSlotWord (ilksChopSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (ilksChopSlotFor I) ⟨0⟩
  have hhole :
      dogSlotWord (ilksHoleSlotFor I) σ_evm I =
        dogSlotWord (ilksHoleSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (ilksHoleSlotFor I) ⟨0⟩
  have hdirt :
      dogSlotWord (ilksDirtSlotFor I) σ_evm I =
        dogSlotWord (ilksDirtSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (ilksDirtSlotFor I) ⟨0⟩
  simp [dogAddressReturnWord, hclip, hchop, hhole, hdirt]

theorem dogIlksReturnEquiv (clip chop hole dirt : UInt256) :
    returnEquiv
      (UInt256.toByteArray (UInt256.land clip solcAddrMask) ++ UInt256.toByteArray chop ++
        UInt256.toByteArray hole ++ UInt256.toByteArray dirt)
      (some [(.address (AccountAddress.ofNat (UInt256.land clip solcAddrMask).toNat)),
        (.int (Int.ofNat chop.toNat)), (.int (Int.ofNat hole.toNat)),
        (.int (Int.ofNat dirt.toNat))])
      ilksTransition.returnType := by
  rw [show ilksTransition.returnType = [addr, uint256, uint256, uint256] by rfl]
  exact returnEquiv.returned rfl (dogIlksReturnEncoding clip chop hole dirt)

theorem dogReachIlksBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 11)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨658⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xd9638d36⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd9 0x63 0x8d 0x36 ⟨0xd9638d36⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hhighWidth : armTgtWidth code (⟨43⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h54 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [selArmNextPc, hhighWidth] using
      RD.selectorSplitNotTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh (by simp)
  have hchop : UInt256.eq (dogSelectorWord 4) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hilks : UInt256.eq (dogSelectorWord 11) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h65 := by
    simpa [selArmNextPc] using
      h54.selectorArmNotTaken (selNat := dogSelectorWord 4) (tgt := (⟨629⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hchop
        (by simp)
  have h658 := by
    simpa using
      h65.selectorArmTaken (selNat := dogSelectorWord 11) (tgt := (⟨658⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hilks
        (dogPatchedDJumpPrefix1405 ⟨658⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h658⟩

theorem dogIlksBodyCoreOk
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some ilksTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (ilksTransition.params.map Param.name)
        (transitionSignature ilksTransition).paramTypes I.calldata = some (ilksLocals I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨658⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let baseSlot := solcMappingSlot ⟨1⟩ (ilksArgWord I)
  let clipWord := dogSlotWord baseSlot σ_evm I
  let chopWord := dogSlotWord (baseSlot + ⟨1⟩) σ_evm I
  let holeWord := dogSlotWord (baseSlot + ⟨2⟩) σ_evm I
  let dirtWord := dogSlotWord (baseSlot + ⟨3⟩) σ_evm I
  let locals := ilksLocals I
  have hclipSlot : ilksClipSlotFor I = baseSlot := by
    simp [baseSlot, ilksClipSlotFor_eq hsz36]
  have hchopSlot : ilksChopSlotFor I = baseSlot + ⟨1⟩ := by
    simp [baseSlot, ilksChopSlotFor_eq hsz36]
  have hholeSlot : ilksHoleSlotFor I = baseSlot + ⟨2⟩ := by
    simp [baseSlot, ilksHoleSlotFor_eq hsz36]
  have hdirtSlot : ilksDirtSlotFor I = baseSlot + ⟨3⟩ := by
    simp [baseSlot, ilksDirtSlotFor_eq hsz36]
  have hval :
      some [Value.address (AccountAddress.ofNat
          (dogAddressReturnWord (ilksClipSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (dogSlotWord (ilksChopSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (dogSlotWord (ilksHoleSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (dogSlotWord (ilksDirtSlotFor I) σ_solm I).toNat)] =
      some [Value.address (AccountAddress.ofNat (UInt256.land clipWord solcAddrMask).toNat),
        Value.int (Int.ofNat chopWord.toNat), Value.int (Int.ofNat holeWord.toNat),
        Value.int (Int.ofNat dirtWord.toNat)] := by
    simpa [hclipSlot, hchopSlot, hholeSlot, hdirtSlot, clipWord, chopWord, holeWord,
      dirtWord, dogAddressReturnWord] using
      (dogIlksReturnValuesEquiv (I := I) (σ_evm := σ_evm) (σ_solm := σ_solm)
        hAccounts)
  have henc := dogIlksReturnEquiv clipWord chopWord holeWord dirtWord
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        ilksTransition.body
        (.returned { contract := contract v, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (dogAddressReturnWord (ilksClipSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (dogSlotWord (ilksChopSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (dogSlotWord (ilksHoleSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (dogSlotWord (ilksDirtSlotFor I) σ_solm I).toNat))])) := by
    simpa [locals, initState] using
      dogIlksBodyReturns (v := v) (I := I) hsz36
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (by simp only [initState]; exact hwv) rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨658⟩) (ret := ⟨687⟩)
    (decoded := ⟨680⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨680⟩ hpatch (by native_decide)) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (code := code) (decoded := ⟨680⟩) (ret := ⟨687⟩) (routine := ⟨2365⟩)
    (R := [sel]) hdecoded
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.dogIlksStructGetter
    (code := code) (pc := ⟨2365⟩) (key := ilksArgWord I) (ret := ⟨687⟩)
    (R := [sel]) (by simpa [ilksArgWord] using hroutine)
    (by
      unfold dogIlksStructGetterWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (dogPatchedDJumpPrefix1405 ⟨687⟩ hpatch (by native_decide))
    (by simp)
  have hret :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (UInt256.land clipWord solcAddrMask) ++
          UInt256.toByteArray chopWord ++ UInt256.toByteArray holeWord ++
          UInt256.toByteArray dirtWord) := by
    have hmem : (solcMappingHashMem ⟨1⟩ (ilksArgWord I)).size = 96 :=
      solcMappingHashMem_size ⟨1⟩ (ilksArgWord I)
    have hread64 :
        (solcMappingHashMem ⟨1⟩ (ilksArgWord I)).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
      solcMappingHashMem_read64 ⟨1⟩ (ilksArgWord I)
    have hret' := RD.dogIlksReturnFromMem
      (code := code) (pc := ⟨687⟩)
      (clip := UInt256.land clipWord solcAddrMask) (chop := chopWord)
      (hole := holeWord) (dirt := dirtWord) (ret := ⟨687⟩) (R := [sel])
      (by
        have hclean :
            UInt256.land (UInt256.land clipWord solcAddrMask) solcAddrMask =
              UInt256.land clipWord solcAddrMask := by
          exact solcAddrMask_clean (solcAddrMask_result_canonical clipWord)
        simpa [baseSlot, clipWord, chopWord, holeWord, dirtWord, dogSlotWord,
          hclean, u256_land_comm] using hretPc)
      (by
        unfold dogIlksReturnFromMemWf
        repeat' first
          | apply And.intro
          | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
            native_decide)
      hmem hread64 (by simp)
    have hclean :
        UInt256.land (UInt256.land clipWord solcAddrMask) solcAddrMask =
          UInt256.land clipWord solcAddrMask := by
      exact solcAddrMask_clean (solcAddrMask_result_canonical clipWord)
    simpa [hclean] using hret'
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem dogIlksBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some ilksTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨658⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨658⟩) (ret := ⟨687⟩)
    (decoded := ⟨680⟩) (need := ⟨32⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_ilks_none_short (v := v) hsz4 hshort)

theorem dogIlksBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 11) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some ilksTransition :=
    dogDispatchIlks hsel
  have hreach := dogReachIlksBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact dogIlksBodyCoreOk hpatch hcode hwv hsz36 hsize hdispatch
      (dogDecode_ilks_ok (v := v) hsz36) hreach hAccounts
  · exact dogIlksBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog
