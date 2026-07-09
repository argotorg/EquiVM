import Benchmarks.Dss.Vat.Init
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `ilks(bytes32)` five-field struct mapping getter -/

abbrev ilksArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev ilksArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev ilksArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (ilksArgBytes I)

abbrev ilksStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (ilksArgValue I)

abbrev ilksArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "Art"] }

abbrev ilksRateEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "rate"] }

abbrev ilksSpotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "spot"] }

abbrev ilksLineEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "line"] }

abbrev ilksDustEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (ilksArgKey I), .field "dust"] }

abbrev ilksArtSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (ilksArgKey I)

abbrev ilksRateSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksArtSlotFor I + ⟨1⟩

abbrev ilksSpotSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksArtSlotFor I + ⟨2⟩

abbrev ilksLineSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksArtSlotFor I + ⟨3⟩

abbrev ilksDustSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksArtSlotFor I + ⟨4⟩

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

theorem ilksArtSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksArtSlotFor I = solcMappingSlot ⟨2⟩ (ilksArgWord I) := by
  unfold ilksArtSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_ilksArgKey hsz36]

theorem ilksRateSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksRateSlotFor I = solcMappingSlot ⟨2⟩ (ilksArgWord I) + ⟨1⟩ := by
  simp [ilksRateSlotFor, ilksArtSlotFor_eq hsz36]

theorem ilksSpotSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksSpotSlotFor I = solcMappingSlot ⟨2⟩ (ilksArgWord I) + ⟨2⟩ := by
  simp [ilksSpotSlotFor, ilksArtSlotFor_eq hsz36]

theorem ilksLineSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksLineSlotFor I = solcMappingSlot ⟨2⟩ (ilksArgWord I) + ⟨3⟩ := by
  simp [ilksLineSlotFor, ilksArtSlotFor_eq hsz36]

theorem ilksDustSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ilksDustSlotFor I = solcMappingSlot ⟨2⟩ (ilksArgWord I) + ⟨4⟩ := by
  simp [ilksDustSlotFor, ilksArtSlotFor_eq hsz36]

theorem vatDecode_ilks_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata = some (ilksStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [bytes32] I.calldata = _
  simpa [config, ilksStore, ilksArgValue, ilksArgBytes, bytes32] using
    decodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36

theorem vatDecode_ilks_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
      (transitionSignature ilksTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [bytes32] I.calldata = none
  simpa [config, bytes32] using
    decodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort

theorem vatDispatchIlks {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 16)) :
    dispatchMsg contract I.calldata = some ilksTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ilksTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes]
  native_decide

theorem vatReachIlksBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 16)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1395⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xd9638d36⟩ :=
    vatSelWord_eq_of_beq I hsz 0xd9 0x63 0x8d 0x36 ⟨0xd9638d36⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms114Body 2 (by omega) ⟨1395⟩ hcode hwv hsz hsize
    hroot hhigh hhighhigh heq0 htake (by jump_dest) (by native_decide)

@[reducible] def solcIlksStruct5GetterWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p36 := p34 + UInt256.ofNat 2
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨2⟩, 1))
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
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p22 = some (.DUP3, .none)
  ∧ decode code p23 = some (.ADD, .none)
  ∧ decode code p24 = some (.SLOAD, .none)
  ∧ decode code p25 = some (.SWAP3, .none)
  ∧ decode code p26 = some (.DUP3, .none)
  ∧ decode code p27 = some (.ADD, .none)
  ∧ decode code p28 = some (.SLOAD, .none)
  ∧ decode code p29 = some (.Push .PUSH1, some (⟨3⟩, 1))
  ∧ decode code p31 = some (.DUP4, .none)
  ∧ decode code p32 = some (.ADD, .none)
  ∧ decode code p33 = some (.SLOAD, .none)
  ∧ decode code p34 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p36 = some (.SWAP1, .none)
  ∧ decode code p37 = some (.SWAP4, .none)
  ∧ decode code p38 = some (.ADD, .none)
  ∧ decode code p39 = some (.SLOAD, .none)
  ∧ decode code p40 = some (.SWAP2, .none)
  ∧ decode code p41 = some (.SWAP4, .none)
  ∧ decode code p42 = some (.SWAP3, .none)
  ∧ decode code p43 = some (.SWAP1, .none)
  ∧ decode code p44 = some (.SWAP2, .none)
  ∧ decode code p45 = some (.DUP6, .none)
  ∧ decode code p46 = some (.JUMP, .none)

set_option maxHeartbeats 2000000 in
theorem RD.solcIlksStruct5Getter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcIlksStruct5GetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨2⟩ key + ⟨4⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨2⟩ key + ⟨3⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨2⟩ key + ⟨2⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨2⟩ key + ⟨1⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨2⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨2⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd25, hd26, hd27, hd28,
      hd29, hd31, hd32, hd33, hd34, hd36, hd37, hd38, hd39, hd40, hd41,
      hd42, hd43, hd44, hd45, hd46⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨2⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨2⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd10 := rd8.push1 ⟨0⟩ hd8 (by evm_ov)
  have rd11 := rd10.swap2 hd10 (by evm_ov)
  have rd12 := rd11.dup3 hd11 (by evm_ov)
  have rd13 := rd12.mstore 0 (solcMappingHashMem ⟨2⟩ key)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := rd13.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.swap1 hd15 (by evm_ov)
  have rd17 := rd16.swap2 hd16 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨2⟩ key
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨2⟩ key)
    (UInt256.ofNat 3) hd17 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  have rd19 := rd18.dup1 hd18 (by evm_ov)
  obtain ⟨_, _, rd20₀⟩ := rd19.sload hd19 (by evm_ov)
  have rd22 := rd20₀.push1 ⟨1⟩ hd20 (by evm_ov)
  have rd23 := rd22.dup3 hd22 (by evm_ov)
  have rd24 := rd23.add hd23 (by evm_ov)
  obtain ⟨_, _, rd25₀⟩ := rd24.sload hd24 (by evm_ov)
  have rd26 := rd25₀.swap3 hd25 (by evm_ov)
  have rd27 := rd26.dup3 hd26 (by evm_ov)
  have rd28 := rd27.add hd27 (by evm_ov)
  obtain ⟨_, _, rd29₀⟩ := rd28.sload hd28 (by evm_ov)
  have rd31 := rd29₀.push1 ⟨3⟩ hd29 (by evm_ov)
  have rd32 := rd31.dup4 hd31 (by evm_ov)
  have rd33 := rd32.add hd32 (by evm_ov)
  obtain ⟨_, _, rd34₀⟩ := rd33.sload hd33 (by evm_ov)
  have rd36 := rd34₀.push1 ⟨4⟩ hd34 (by evm_ov)
  have rd37 := rd36.swap1 hd36 (by evm_ov)
  have rd38 := rd37.swap4 hd37 (by evm_ov)
  have rd39 := rd38.add hd38 (by evm_ov)
  obtain ⟨_, _, rd40₀⟩ := rd39.sload hd39 (by evm_ov)
  have rd41 := rd40₀.swap2 hd40 (by evm_ov)
  have rd42 := rd41.swap4 hd41 (by evm_ov)
  have rd43 := rd42.swap3 hd42 (by evm_ov)
  have rd44 := rd43.swap1 hd43 (by evm_ov)
  have rd45 := rd44.swap2 hd44 (by evm_ov)
  have rd46 := rd45.dup6 hd45 (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_add_comm] using rd46.jump hd46 hret (by evm_ov)⟩

abbrev ilksReturn5Writes (art rate spot line dust : UInt256) : List (Nat × UInt256) :=
  [(128, art), (160, rate), (192, spot), (224, line), (256, dust)]

noncomputable def solcScratchReturn5Mem
    (scratch : ByteArray) (art rate spot line dust : UInt256) : ByteArray :=
  writeCascade scratch (ilksReturn5Writes art rate spot line dust)

theorem solcScratchReturn5Mem_size {scratch : ByteArray} (art rate spot line dust : UInt256)
    (hscratch : scratch.size = 96) :
    (solcScratchReturn5Mem scratch art rate spot line dust).size = 288 := by
  unfold solcScratchReturn5Mem ilksReturn5Writes
  exact writeCascade_size_of_base scratch _ hscratch
    (by simp [WriteGapsOk]; native_decide)
    (by simp [writeCascadeSize])

theorem solcScratchReturn5Mem_read64 {scratch : ByteArray} (art rate spot line dust : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcScratchReturn5Mem ilksReturn5Writes
  rw [writeCascade_read_preserved_of_base scratch _ hscratch (by
    simp [WindowDisjointFromWrites]; native_decide)]
  exact hread64

theorem solcScratchReturn5Mem_mload64 {scratch : ByteArray} (art rate spot line dust : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcScratchReturn5Mem scratch art rate spot line dust).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcScratchReturn5Mem_size art rate spot line dust hscratch]; decide)
    (by decide) (solcScratchReturn5Mem_read64 art rate spot line dust hscratch hread64)

private theorem solcScratchReturn5Mem_read128_word {scratch : ByteArray}
    (art rate spot line dust : UInt256) (hscratch : scratch.size = 96) :
    (solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding 128 32 =
      UInt256.toByteArray art := by
  unfold solcScratchReturn5Mem ilksReturn5Writes
  exact writeCascade_read_word_of_head_of_base scratch art
    [(160, rate), (192, spot), (224, line), (256, dust)] hscratch
    (by native_decide) (by simp [WindowDisjointFromWrites])

private theorem solcScratchReturn5Mem_read160_word {scratch : ByteArray}
    (art rate spot line dust : UInt256) (hscratch : scratch.size = 96) :
    (solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding 160 32 =
      UInt256.toByteArray rate := by
  unfold solcScratchReturn5Mem ilksReturn5Writes
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head (writeWord scratch 128 art) 160 rate
    [(192, spot), (224, line), (256, dust)]
    (by
      have hgap : 128 - scratch.size < USize.size := by
        rw [hscratch]
        exact lt_usize 32 (by norm_num)
      rw [writeWord_size scratch 128 art hgap]
      rw [hscratch]
      native_decide)
    (by
      have hgap : 128 - scratch.size < USize.size := by
        rw [hscratch]
        exact lt_usize 32 (by norm_num)
      rw [writeWord_size scratch 128 art hgap]
      rw [hscratch]
      simp [WindowDisjointFromWrites])

private theorem solcScratchReturn5Mem_read192_word {scratch : ByteArray}
    (art rate spot line dust : UInt256) (hscratch : scratch.size = 96) :
    (solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding 192 32 =
      UInt256.toByteArray spot := by
  unfold solcScratchReturn5Mem ilksReturn5Writes
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head
    (writeWord (writeWord scratch 128 art) 160 rate) 192 spot
    [(224, line), (256, dust)]
    (by
      have h1 : (writeWord scratch 128 art).size = 160 := by
        have hgap : 128 - scratch.size < USize.size := by
          rw [hscratch]
          exact lt_usize 32 (by norm_num)
        rw [writeWord_size scratch 128 art hgap]
        rw [hscratch]
        native_decide
      rw [writeWord_size (writeWord scratch 128 art) 160 rate
        (by rw [h1]; exact lt_usize 0 (by norm_num)), h1]
      native_decide)
    (by
      have h1 : (writeWord scratch 128 art).size = 160 := by
        have hgap : 128 - scratch.size < USize.size := by
          rw [hscratch]
          exact lt_usize 32 (by norm_num)
        rw [writeWord_size scratch 128 art hgap]
        rw [hscratch]
        native_decide
      rw [writeWord_size (writeWord scratch 128 art) 160 rate
        (by rw [h1]; exact lt_usize 0 (by norm_num)), h1]
      simp [WindowDisjointFromWrites])

private theorem solcScratchReturn5Mem_read224_word {scratch : ByteArray}
    (art rate spot line dust : UInt256) (hscratch : scratch.size = 96) :
    (solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding 224 32 =
      UInt256.toByteArray line := by
  unfold solcScratchReturn5Mem ilksReturn5Writes
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head
    (writeWord (writeWord (writeWord scratch 128 art) 160 rate) 192 spot) 224 line
    [(256, dust)]
    (by
      have h1 : (writeWord scratch 128 art).size = 160 := by
        have hgap : 128 - scratch.size < USize.size := by
          rw [hscratch]
          exact lt_usize 32 (by norm_num)
        rw [writeWord_size scratch 128 art hgap]
        rw [hscratch]
        native_decide
      have h2 : (writeWord (writeWord scratch 128 art) 160 rate).size = 192 := by
        rw [writeWord_size (writeWord scratch 128 art) 160 rate
          (by rw [h1]; exact lt_usize 0 (by norm_num)), h1]
        native_decide
      rw [writeWord_size (writeWord (writeWord scratch 128 art) 160 rate) 192 spot
        (by rw [h2]; exact lt_usize 0 (by norm_num)), h2]
      native_decide)
    (by
      have h1 : (writeWord scratch 128 art).size = 160 := by
        have hgap : 128 - scratch.size < USize.size := by
          rw [hscratch]
          exact lt_usize 32 (by norm_num)
        rw [writeWord_size scratch 128 art hgap]
        rw [hscratch]
        native_decide
      have h2 : (writeWord (writeWord scratch 128 art) 160 rate).size = 192 := by
        rw [writeWord_size (writeWord scratch 128 art) 160 rate
          (by rw [h1]; exact lt_usize 0 (by norm_num)), h1]
        norm_num
      rw [writeWord_size (writeWord (writeWord scratch 128 art) 160 rate) 192 spot
        (by rw [h2]; exact lt_usize 0 (by norm_num)), h2]
      simp [WindowDisjointFromWrites])

private theorem solcScratchReturn5Mem_read256_word {scratch : ByteArray}
    (art rate spot line dust : UInt256) (hscratch : scratch.size = 96) :
    (solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding 256 32 =
      UInt256.toByteArray dust := by
  unfold solcScratchReturn5Mem ilksReturn5Writes
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head
    (writeWord (writeWord (writeWord (writeWord scratch 128 art) 160 rate) 192 spot) 224 line)
      256 dust []
    (by
      have h1 : (writeWord scratch 128 art).size = 160 := by
        have hgap : 128 - scratch.size < USize.size := by
          rw [hscratch]
          exact lt_usize 32 (by norm_num)
        rw [writeWord_size scratch 128 art hgap]
        rw [hscratch]
        native_decide
      have h2 : (writeWord (writeWord scratch 128 art) 160 rate).size = 192 := by
        rw [writeWord_size (writeWord scratch 128 art) 160 rate
          (by rw [h1]; exact lt_usize 0 (by norm_num)), h1]
        native_decide
      have h3 : (writeWord (writeWord (writeWord scratch 128 art) 160 rate) 192 spot).size = 224 := by
        rw [writeWord_size (writeWord (writeWord scratch 128 art) 160 rate) 192 spot
          (by rw [h2]; exact lt_usize 0 (by norm_num)), h2]
        native_decide
      rw [writeWord_size
        (writeWord (writeWord (writeWord scratch 128 art) 160 rate) 192 spot) 224 line
        (by rw [h3]; exact lt_usize 0 (by norm_num)), h3]
      native_decide)
    (by simp [WindowDisjointFromWrites])

theorem solcScratchReturn5Mem_read128_160 {scratch : ByteArray}
    (art rate spot line dust : UInt256) (hscratch : scratch.size = 96) :
    (solcScratchReturn5Mem scratch art rate spot line dust).readWithPadding 128 160 =
      UInt256.toByteArray art ++ UInt256.toByteArray rate ++ UInt256.toByteArray spot ++
        UInt256.toByteArray line ++ UInt256.toByteArray dust := by
  let memout := solcScratchReturn5Mem scratch art rate spot line dust
  have hsize : memout.size = 288 := by
    simpa [memout] using solcScratchReturn5Mem_size art rate spot line dust hscratch
  have h128 : memout.readWithPadding 128 32 = UInt256.toByteArray art := by
    simpa [memout] using solcScratchReturn5Mem_read128_word art rate spot line dust hscratch
  have h160 : memout.readWithPadding 160 32 = UInt256.toByteArray rate := by
    simpa [memout] using solcScratchReturn5Mem_read160_word art rate spot line dust hscratch
  have h192 : memout.readWithPadding 192 32 = UInt256.toByteArray spot := by
    simpa [memout] using solcScratchReturn5Mem_read192_word art rate spot line dust hscratch
  have h224 : memout.readWithPadding 224 32 = UInt256.toByteArray line := by
    simpa [memout] using solcScratchReturn5Mem_read224_word art rate spot line dust hscratch
  have h256 : memout.readWithPadding 256 32 = UInt256.toByteArray dust := by
    simpa [memout] using solcScratchReturn5Mem_read256_word art rate spot line dust hscratch
  rw [show (160 : Nat) = 32 + 128 by norm_num]
  rw [byteArray_readWithPadding_split memout 128 32 128
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega)]
  rw [h128]
  rw [show (128 : Nat) = 32 + 96 by norm_num]
  rw [byteArray_readWithPadding_split memout 160 32 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega)]
  rw [h160]
  rw [show (96 : Nat) = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split memout 192 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega)]
  rw [h192]
  rw [show (64 : Nat) = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split memout 224 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega)]
  rw [h224, h256]
  simp [ByteArray.append_assoc]

@[reducible] def solcFiveWordReturnFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  let p25 := p23 + UInt256.ofNat 2
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p40 := p38 + UInt256.ofNat 2
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.SWAP6, .none)
  ∧ decode code p6 = some (.DUP7, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.DUP7, .none)
  ∧ decode code p11 = some (.ADD, .none)
  ∧ decode code p12 = some (.SWAP5, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.SWAP5, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.DUP5, .none)
  ∧ decode code p17 = some (.DUP5, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.SWAP3, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.SWAP3, .none)
  ∧ decode code p22 = some (.MSTORE, .none)
  ∧ decode code p23 = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code p25 = some (.DUP5, .none)
  ∧ decode code p26 = some (.ADD, .none)
  ∧ decode code p27 = some (.MSTORE, .none)
  ∧ decode code p28 = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code p30 = some (.DUP4, .none)
  ∧ decode code p31 = some (.ADD, .none)
  ∧ decode code p32 = some (.MSTORE, .none)
  ∧ decode code p33 = some (.MLOAD, .none)
  ∧ decode code p34 = some (.SWAP1, .none)
  ∧ decode code p35 = some (.DUP2, .none)
  ∧ decode code p36 = some (.SWAP1, .none)
  ∧ decode code p37 = some (.SUB, .none)
  ∧ decode code p38 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p40 = some (.ADD, .none)
  ∧ decode code p41 = some (.SWAP1, .none)
  ∧ decode code p42 = some (.RETURN, .none)

set_option maxHeartbeats 2000000 in
theorem RD.solcFiveWordReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc art rate spot line dust ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (dust :: line :: spot :: rate :: art :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcFiveWordReturnFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hscratch : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray art ++ UInt256.toByteArray rate ++ UInt256.toByteArray spot ++
        UInt256.toByteArray line ++ UInt256.toByteArray dust) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd14,
      hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd25, hd26,
      hd27, hd28, hd30, hd31, hd32, hd33, hd34, hd35, hd36, hd37, hd38,
      hd40, hd41, hd42⟩
  let mem1 := Reasoning.Theory.writeWord mem 128 art
  let mem2 := writeCascade mem [(128, art), (160, rate)]
  let mem3 := writeCascade mem [(128, art), (160, rate), (192, spot)]
  let mem4 := writeCascade mem [(128, art), (160, rate), (192, spot), (224, line)]
  let mem5 := solcScratchReturn5Mem mem art rate spot line dust
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap6 hd5 (by evm_ov),
    raw dup7 hd6 (by evm_ov),
    raw mstore 6 mem1 (UInt256.ofNat 5) hd7 mem_cost
      (by
        simp [mem1, Reasoning.Theory.writeWord]
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd8 (by evm_ov),
    raw dup7 hd10 (by evm_ov),
    raw add hd11 (by evm_ov),
    raw swap5 hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap5 hd14 (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 6) hd15 mem_cost
      (by
        simp [mem1, mem2, Reasoning.Theory.writeWord]
        try rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide])
      (by decide) (by evm_ov),
    raw dup5 hd16 (by evm_ov),
    raw dup5 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw swap3 hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw swap3 hd21 (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 7) hd22 mem_cost
      (by
        simp [mem2, mem3, Reasoning.Theory.writeWord]
        try rw [show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by decide])
      (by decide) (by evm_ov),
    raw push1 ⟨96⟩ hd23 (by evm_ov),
    raw dup5 hd25 (by evm_ov),
    raw add hd26 (by evm_ov),
    raw mstore 3 mem4 (UInt256.ofNat 8) hd27 mem_cost
      (by
        simp [mem3, mem4, Reasoning.Theory.writeWord]
        try rw [show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by decide])
      (by decide) (by evm_ov),
    raw push1 ⟨128⟩ hd28 (by evm_ov),
    raw dup4 hd30 (by evm_ov),
    raw add hd31 (by evm_ov),
    raw mstore 3 mem5 (UInt256.ofNat 9) hd32 mem_cost
      (by
        simp [mem4, mem5, solcScratchReturn5Mem, ilksReturn5Writes,
          Reasoning.Theory.writeWord]
        try rw [show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 from by decide])
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) hd33 mem_cost
      (by simpa [mem5] using solcScratchReturn5Mem_mload64 art rate spot line dust hscratch hread64)
      (by decide) (by evm_ov),
    raw swap1 hd34 (by evm_ov),
    raw dup2 hd35 (by evm_ov),
    raw swap1 hd36 (by evm_ov),
    raw sub hd37 (by evm_ov),
    raw push1 ⟨160⟩ hd38 (by evm_ov),
    raw add hd40 (by evm_ov),
    raw swap1 hd41 (by evm_ov),
    raw ret 0
      (UInt256.toByteArray art ++ UInt256.toByteArray rate ++ UInt256.toByteArray spot ++
        UInt256.toByteArray line ++ UInt256.toByteArray dust)
      hd42 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rw [show ((⟨160⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 160
          from by decide]
        simpa [mem5] using solcScratchReturn5Mem_read128_160 art rate spot line dust hscratch)
      (by evm_ov)]

private theorem encodeABIValue_uint256_word (v : UInt256) :
    encodeABIValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  have hlt : v.toNat < EVM.twoPow 256 := by
    change v.val.val < EVM.twoPow 256
    exact v.val.isLt
  simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]

theorem uint256FiveReturnEncoding (art rate spot line dust : UInt256) :
    encodeReturnValues? [uint256, uint256, uint256, uint256, uint256]
      [.int (Int.ofNat art.toNat), .int (Int.ofNat rate.toNat),
        .int (Int.ofNat spot.toNat), .int (Int.ofNat line.toNat),
        .int (Int.ofNat dust.toNat)] =
        some (UInt256.toByteArray art ++ UInt256.toByteArray rate ++ UInt256.toByteArray spot ++
          UInt256.toByteArray line ++ UInt256.toByteArray dust) := by
  rw [show UInt256.toByteArray art = (EVM.Word.toBytesBE art).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray art).symm]
  rw [show UInt256.toByteArray rate = (EVM.Word.toBytesBE rate).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray rate).symm]
  rw [show UInt256.toByteArray spot = (EVM.Word.toBytesBE spot).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray spot).symm]
  rw [show UInt256.toByteArray line = (EVM.Word.toBytesBE line).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray line).symm]
  rw [show UInt256.toByteArray dust = (EVM.Word.toBytesBE dust).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray dust).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, uint256, uint256] = some 160
    by native_decide]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256_word art]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256_word rate]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256_word spot]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256_word line]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256_word dust]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

private theorem evalIlksField
    {I : ExecutionEnv} (evm : EVM.State)
    (field : Ident) (slot : UInt256) (er : EvaledStorageRef)
    (her :
      evalStorageRef config { contract := contract, locals := ilksStore I } evm
        (ilksF (.var "arg0") field) = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    evalExpr? config { contract := contract, locals := ilksStore I } evm
        (.storage (ilksF (.var "arg0") field)) =
      .ok (.int (Int.ofNat (vatSlotWord slot evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := ilksStore I }) (evm := evm)
    (slot := ilksF (.var "arg0") field) (er := er)
    (t := .int uint256Int) (loc := wordLoc slot)
    (value := .int (Int.ofNat (vatSlotWord slot evm.accountMap evm.executionEnv).toNat))
    (by simp [ilksStore, ilksF])
    her
    hty
    hloc
    (by simpa [vatSlotWord] using vatStorageLocLoad_uint256 evm slot)

theorem vatIlksBodyReturns {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals = ilksStore I) :
    ExecTransitionBody config contract evm locals ilksTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (vatSlotWord (ilksArtSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (vatSlotWord (ilksRateSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (vatSlotWord (ilksSpotSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (vatSlotWord (ilksLineSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (vatSlotWord (ilksDustSlotFor I) evm.accountMap evm.executionEnv).toNat))])) := by
  subst locals
  let frame : Frame := { contract := contract, locals := ilksStore I }
  have hArt :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "Art")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (ilksArtSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
    exact evalIlksField evm "Art" (ilksArtSlotFor I) (ilksArtEvaledRef I)
      (by
        simp [ilksStore, ilksArtEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (by rfl)
  have hRate :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "rate")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (ilksRateSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
    exact evalIlksField evm "rate" (ilksRateSlotFor I) (ilksRateEvaledRef I)
      (by
        simp [ilksStore, ilksRateEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (by rfl)
  have hSpot :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "spot")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (ilksSpotSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
    exact evalIlksField evm "spot" (ilksSpotSlotFor I) (ilksSpotEvaledRef I)
      (by
        simp [ilksStore, ilksSpotEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (by rfl)
  have hLine :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "line")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (ilksLineSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
    exact evalIlksField evm "line" (ilksLineSlotFor I) (ilksLineEvaledRef I)
      (by
        simp [ilksStore, ilksLineEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (by rfl)
  have hDust :
      evalExpr? config frame evm (.storage (ilksF (.var "arg0") "dust")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (ilksDustSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    have hkeyLen := ilksArgBytes_len_min (I := I) hsz36
    exact evalIlksField evm "dust" (ilksDustSlotFor I) (ilksDustEvaledRef I)
      (by
        simp [ilksStore, ilksDustEvaledRef, ilksArgKey, ilksArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
      (by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (by rfl)
  have hreturns :
      evalExprs? config frame evm
        [.storage (ilksF (.var "arg0") "Art"), .storage (ilksF (.var "arg0") "rate"),
          .storage (ilksF (.var "arg0") "spot"), .storage (ilksF (.var "arg0") "line"),
          .storage (ilksF (.var "arg0") "dust")] =
          .ok
            [ .int (Int.ofNat
                (vatSlotWord (ilksArtSlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (vatSlotWord (ilksRateSlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (vatSlotWord (ilksSpotSlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (vatSlotWord (ilksLineSlotFor I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (vatSlotWord (ilksDustSlotFor I) evm.accountMap evm.executionEnv).toNat) ] := by
    simp [evalExprs?, hArt, hRate, hSpot, hLine, hDust, EvalResult.bind, bind, pure]
  simpa [ilksTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

theorem vatIlksBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (ilksTransition.params.map Param.name)
        (transitionSignature ilksTransition).paramTypes I.calldata =
          some (ilksStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1395⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let artSlot := solcMappingSlot ⟨2⟩ (ilksArgWord I)
  let rateSlot := artSlot + ⟨1⟩
  let spotSlot := artSlot + ⟨2⟩
  let lineSlot := artSlot + ⟨3⟩
  let dustSlot := artSlot + ⟨4⟩
  let artWord := vatSlotWord artSlot σ_evm I
  let rateWord := vatSlotWord rateSlot σ_evm I
  let spotWord := vatSlotWord spotSlot σ_evm I
  let lineWord := vatSlotWord lineSlot σ_evm I
  let dustWord := vatSlotWord dustSlot σ_evm I
  let locals : Store := ilksStore I
  have hArtSlot : ilksArtSlotFor I = artSlot := by
    simp [artSlot, ilksArtSlotFor_eq hsz36]
  have hRateSlot : ilksRateSlotFor I = rateSlot := by
    simp [rateSlot, artSlot, ilksRateSlotFor_eq hsz36]
  have hSpotSlot : ilksSpotSlotFor I = spotSlot := by
    simp [spotSlot, artSlot, ilksSpotSlotFor_eq hsz36]
  have hLineSlot : ilksLineSlotFor I = lineSlot := by
    simp [lineSlot, artSlot, ilksLineSlotFor_eq hsz36]
  have hDustSlot : ilksDustSlotFor I = dustSlot := by
    simp [dustSlot, artSlot, ilksDustSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals ilksTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vatSlotWord (ilksArtSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (vatSlotWord (ilksRateSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (vatSlotWord (ilksSpotSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (vatSlotWord (ilksLineSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat (vatSlotWord (ilksDustSlotFor I) σ_solm I).toNat))])) := by
    simpa [locals, initState] using
      vatIlksBodyReturns hsz36
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (by simp only [initState]; exact hwv) rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1395⟩) (ret := ⟨1424⟩)
    (decoded := ⟨1417⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, htoRoutineRd⟩ := RD.solcOneWordExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨1417⟩) (ret := ⟨1424⟩) (routine := ⟨6084⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcOneWordExternalLoadAndJumpWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcIlksStruct5Getter
    (code := vatBytecode) (pc := ⟨6084⟩) (key := ilksArgWord I) (ret := ⟨1424⟩)
    (R := [sel]) (by simpa using htoRoutineRd)
    (by
      unfold solcIlksStruct5GetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray artWord ++ UInt256.toByteArray rateWord ++
          UInt256.toByteArray spotWord ++ UInt256.toByteArray lineWord ++
          UInt256.toByteArray dustWord) := by
    have hret' := RD.solcFiveWordReturnFromMem
      (pc := ⟨1424⟩) (art := artWord) (rate := rateWord) (spot := spotWord)
      (line := lineWord) (dust := dustWord) (ret := ⟨1424⟩)
      (R := [sel]) (mem := solcMappingHashMem ⟨2⟩ (ilksArgWord I))
      (by
        simpa [artWord, rateWord, spotWord, lineWord, dustWord, artSlot, rateSlot,
          spotSlot, lineSlot, dustSlot, vatSlotWord] using hretPc)
      (by
        unfold solcFiveWordReturnFromMemWf
        repeat' first | apply And.intro | native_decide)
      (solcMappingHashMem_mload64 ⟨2⟩ (ilksArgWord I))
      (solcMappingHashMem_size ⟨2⟩ (ilksArgWord I))
      (solcMappingHashMem_read64 ⟨2⟩ (ilksArgWord I))
      (by simp)
    simpa [artWord, rateWord, spotWord, lineWord, dustWord] using hret'
  have hArtWord : vatSlotWord artSlot σ_evm I = vatSlotWord artSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner artSlot ⟨0⟩
  have hRateWord : vatSlotWord rateSlot σ_evm I = vatSlotWord rateSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner rateSlot ⟨0⟩
  have hSpotWord : vatSlotWord spotSlot σ_evm I = vatSlotWord spotSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner spotSlot ⟨0⟩
  have hLineWord : vatSlotWord lineSlot σ_evm I = vatSlotWord lineSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner lineSlot ⟨0⟩
  have hDustWord : vatSlotWord dustSlot σ_evm I = vatSlotWord dustSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner dustSlot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (vatSlotWord (ilksArtSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (vatSlotWord (ilksRateSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (vatSlotWord (ilksSpotSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (vatSlotWord (ilksLineSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (vatSlotWord (ilksDustSlotFor I) σ_solm I).toNat)] =
      some [Value.int (Int.ofNat artWord.toNat), Value.int (Int.ofNat rateWord.toNat),
        Value.int (Int.ofNat spotWord.toNat), Value.int (Int.ofNat lineWord.toNat),
        Value.int (Int.ofNat dustWord.toNat)] := by
    rw [hArtSlot, hRateSlot, hSpotSlot, hLineSlot, hDustSlot]
    simp [artWord, rateWord, spotWord, lineWord, dustWord, hArtWord, hRateWord,
      hSpotWord, hLineWord, hDustWord]
  have henc :
      returnEquiv
        (UInt256.toByteArray artWord ++ UInt256.toByteArray rateWord ++
          UInt256.toByteArray spotWord ++ UInt256.toByteArray lineWord ++
          UInt256.toByteArray dustWord)
        (some [(.int (Int.ofNat artWord.toNat)), (.int (Int.ofNat rateWord.toNat)),
          (.int (Int.ofNat spotWord.toNat)), (.int (Int.ofNat lineWord.toNat)),
          (.int (Int.ofNat dustWord.toNat))])
        ilksTransition.returnType := by
    rw [show ilksTransition.returnType = [uint256, uint256, uint256, uint256, uint256] by rfl]
    exact returnEquiv.returned rfl
      (uint256FiveReturnEncoding artWord rateWord spotWord lineWord dustWord)
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem vatIlksBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some ilksTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1395⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1395⟩) (ret := ⟨1424⟩)
    (decoded := ⟨1417⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (vatDecode_ilks_none_short hsz4 hshort)

theorem vatIlksBodyCore : VatBodyTheorem 16 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 16) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some ilksTransition :=
    vatDispatchIlks hsel
  have hreach := vatReachIlksBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatIlksBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (vatDecode_ilks_ok hsz36) hreach hAccounts
  · exact vatIlksBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
