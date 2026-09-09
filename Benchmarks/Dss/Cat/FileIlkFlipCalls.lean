import Benchmarks.Dss.Cat.Storage
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `file(bytes32,bytes32,address)` — HIGH-HIGH dispatch arm 3, entry ⟨733⟩, routine ⟨3366⟩

`file(ilk, what, flip)` is auth-guarded.  On `what == "flip"`:
`vat.nope(ilks[ilk].flip); ilks[ilk].flip = flip; vat.hope(flip);` — two void single-address-arg
external CALLs bracketing an address read-modify-write store at `keccak(ilk,1)+0`. -/

abbrev fileIlkFlipIlk (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileIlkFlipWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev fileIlkFlipIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileIlkFlipWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileIlkFlipFlipRawWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fileIlkFlipFlipKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileIlkFlipFlipRawWord I)

abbrev fileIlkFlipFlip (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (fileIlkFlipFlipRawWord I).toNat

abbrev fileIlkFlipIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (fileIlkFlipIlk I)

abbrev fileIlkFlipBytes : List UInt8 :=
  [102, 108, 105, 112] ++ zeroPad28

abbrev fileIlkFlipLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (fileIlkFlipIlk I))).insert
    "what" (.fixedBytes bytes32Width (fileIlkFlipWhat I))).insert
    "flip" (.address (fileIlkFlipFlip I))

/-! ### length / word helpers -/

theorem fileIlkFlipIlk_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileIlkFlipIlk I).length = 32 := by
  simp [fileIlkFlipIlk, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileIlkFlipWhat_length {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (fileIlkFlipWhat I).length = 32 := by
  simp [fileIlkFlipWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileIlkFlipWhatWord_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    ABI.bytesToWord (fileIlkFlipWhat I) = fileIlkFlipWhatWord I := by
  simpa [fileIlkFlipWhat, fileIlkFlipWhatWord] using
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)

theorem fileIlkFlipWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hbs : fileIlkFlipWhat I = bs) :
    fileIlkFlipWhatWord I = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileIlkFlipWhatWord_eq (I := I) hsz68).symm

theorem fileIlkFlipWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hword : fileIlkFlipWhatWord I = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileIlkFlipWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkFlipWhat I)
    (fileIlkFlipWhat_length (I := I) hsz68)
  rw [fileIlkFlipWhatWord_eq (I := I) hsz68, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileIlkFlipWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hneq : fileIlkFlipWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    fileIlkFlipWhatWord I ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileIlkFlipWhat_eq_of_word_eq hsz68 hword hbsLen)

theorem fileIlkFlipFlipKey_canonical (I : ExecutionEnv) :
    (fileIlkFlipFlipKey I).toNat < EVM.addressModulus := by
  rw [fileIlkFlipFlipKey, u256_land_comm solcAddrMask (fileIlkFlipFlipRawWord I)]
  exact solcAddrMask_result_canonical (fileIlkFlipFlipRawWord I)

/-! ### ABI decode (`bytes32`, `bytes32`, `address`) -/

theorem decodeABIValues_bytes32_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .fixedBytes abiBytes32Width ((bytes.drop 32).take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  have hlen32le : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  rw [if_pos hlen32le]
  have hlen64le : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen64]

theorem decodeABIValues_bytes32_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have hnot : ¬ 32 ≤ bytes.length - 32 := by omega
      simp [hnot]
    · have hlen32le : 32 ≤ bytes.length - 32 := by omega
      rw [if_pos hlen32le]
      have hnot : ¬ 32 ≤ bytes.length - 64 := by omega
      simp [readWord?, readBytes?, hnot]

theorem decodeCalldata_legacyBytes32_bytes32_address_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiAddress] cd =
      some ((((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.fixedBytes abiBytes32Width ((cd.toList.drop 36).take 32))).insert z
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by decide +native]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword68]

theorem decodeCalldata_legacyBytes32_bytes32_address_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_bytes32_address_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

/-! ### Dispatch / decode / locals -/

theorem catDispatch_fileIlkFlip {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩) :
    dispatchMsg contract I.calldata = some fileIlkFlipTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition])
    (post := [fileIlkUintTransition, fileUintTransition, ilksTransition, litterTransition,
      liveTransition, relyTransition, vatTransition, vowTransition, wardsTransition])
    (ti := fileIlkFlipTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes, hcd]
      decide +native
  · rw [selectorOf, fileIlkFlipSelectorBytes]
    exact hsel

theorem catDecode_fileIlkFlip_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileIlkFlipTransition.params.map Param.name)
      (transitionSignature fileIlkFlipTransition).paramTypes I.calldata =
        some (fileIlkFlipLocals I) := by
  simpa [config, fileIlkFlipTransition, bytes32, bytes32Width, addr, fileIlkFlipLocals,
    fileIlkFlipIlk, fileIlkFlipWhat, fileIlkFlipFlip, fileIlkFlipFlipRawWord, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_bytes32_address_ok (cd := I.calldata) (x := "ilk")
      (y := "what") (z := "flip") hsz100)

theorem catDecode_fileIlkFlip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (fileIlkFlipTransition.params.map Param.name)
      (transitionSignature fileIlkFlipTransition).paramTypes I.calldata = none := by
  simpa [config, fileIlkFlipTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_bytes32_address_none_short (cd := I.calldata) (x := "ilk")
      (y := "what") (z := "flip") hsz4 hshort)

theorem fileIlkFlipLocals_get_ilk (I : ExecutionEnv) :
    (fileIlkFlipLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (fileIlkFlipIlk I)) := by
  rw [fileIlkFlipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem fileIlkFlipLocals_get_what (I : ExecutionEnv) :
    (fileIlkFlipLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkFlipWhat I)) := by
  rw [fileIlkFlipLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileIlkFlipLocals_get_flip (I : ExecutionEnv) :
    (fileIlkFlipLocals I).get? "flip" = some (.address (fileIlkFlipFlip I)) := by
  rw [fileIlkFlipLocals, store_get_self]

theorem fileIlkFlipLocals_get_ilks (I : ExecutionEnv) :
    (fileIlkFlipLocals I).get? "ilks" = none := by
  rw [fileIlkFlipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem fileIlkFlipLocals_get_vat (I : ExecutionEnv) :
    (fileIlkFlipLocals I).get? "vat" = none := by
  rw [fileIlkFlipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

/-! ### Reachability (HIGH-HIGH arm 3, entry ⟨733⟩) -/

theorem catReachFileIlkFlipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨733⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : catSelWord I = ⟨3958158237⟩ :=
    catSelWord_eq_of_beq I hsz 0xeb 0xec 0xb3 0x9d ⟨3958158237⟩
      (by decide +native) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc 3))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact catReachHighHighBody 3 (by omega) ⟨733⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by decide +native)

/-! ### Entry bridge: decoded ⟨755⟩ → routine ⟨3366⟩ (load `ilk`@4, `what`@36, `flip`@68 masked) -/

theorem RD.catFileIlkFlipDecodeToRoutine {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨755⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J catBytecode 0).contains ⟨3366⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨3366⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 68) ::
        calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd756 := h.jumpdest (by decide +native) (by evm_ov)
  have rd757 := rd756.pop (by decide +native) (by evm_ov)
  have rd758 := rd757.dup1 (by decide +native) (by evm_ov)
  have rd759 := rd758.calldataload (by decide +native) (by evm_ov)
  have rd760 := rd759.swap1 (by decide +native) (by evm_ov)
  have rd762 := rd760.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd763 := rd762.dup2 (by decide +native) (by evm_ov)
  have rd764 := rd763.add (by decide +native) (by evm_ov)
  have rd765 := rd764.calldataload (by decide +native) (by evm_ov)
  have rd766 := rd765.swap1 (by decide +native) (by evm_ov)
  have rd768 := rd766.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd769 := rd768.add (by decide +native) (by evm_ov)
  have rd770 := rd769.calldataload (by decide +native) (by evm_ov)
  have rd772 := rd770.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd774 := rd772.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd776 := rd774.push1 ⟨160⟩ (by decide +native) (by evm_ov)
  have rd777 := rd776.shl (by decide +native) (by evm_ov)
  have rd778 := rd777.sub (by decide +native) (by evm_ov)
  have rd779 := rd778.and (by decide +native) (by evm_ov)
  have rd782 := rd779.push2 ⟨3366⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide, solcAddrMask]
      using rd782.jump (by decide +native) hroutine (by evm_ov)⟩

/-! ### Reach → auth → what-check (⟨733⟩ → ⟨3455⟩ on auth ok) -/

theorem RD.catFileIlkFlipToWhatCheck {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨733⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3455⟩
      (fileIlkFlipFlipKey I :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ⟨302⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨733⟩) (ret := ⟨302⟩)
    (decoded := ⟨755⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hlt
  obtain ⟨_, _, hroutine⟩ := RD.catFileIlkFlipDecodeToRoutine
    (ret := ⟨302⟩) (sel := sel) (R := []) hdecoded (by jump_dest) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.catAuthCheckOk
    (code := catBytecode) (pc := ⟨3366⟩) (okPc := ⟨3455⟩)
    (key := fileIlkFlipFlipKey I) (ret := fileIlkFlipWhatWord I)
    (R := [fileIlkFlipIlkWord I, ⟨302⟩, sel])
    (by simpa [fileIlkFlipFlipKey, fileIlkFlipWhatWord, fileIlkFlipIlkWord] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | decide +native)
    hauth (by jump_dest) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.catFileIlkFlipAuthRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨733⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨733⟩) (ret := ⟨302⟩)
    (decoded := ⟨755⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hlt
  obtain ⟨_, _, hroutine⟩ := RD.catFileIlkFlipDecodeToRoutine
    (ret := ⟨302⟩) (sel := sel) (R := []) hdecoded (by jump_dest) (by simp)
  exact RD.catAuthCheckRevert
    (code := catBytecode) (pc := ⟨3366⟩) (okPc := ⟨3455⟩)
    (key := fileIlkFlipFlipKey I) (ret := fileIlkFlipWhatWord I)
    (R := [fileIlkFlipIlkWord I, ⟨302⟩, sel])
    (by simpa [fileIlkFlipFlipKey, fileIlkFlipWhatWord, fileIlkFlipIlkWord] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcErrorStringRevertTailWf catAuthTailPc catNotAuthorizedRawWord
      repeat' first | apply And.intro | decide +native)
    hauth (by simp)

/-! ### `what == "flip"` switch (⟨3455⟩ → ⟨3471⟩ match / ⟨953⟩ skip) -/

theorem fileIlkFlipConst_eq :
    UInt256.shiftLeft ⟨107398807⟩ ⟨228⟩ = ABI.bytesToWord fileIlkFlipBytes := by
  decide +native

theorem RD.catFileIlkFlipWhatFlip {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {flip what ilk ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨3455⟩ (flip :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hmatch : what = ABI.bytesToWord fileIlkFlipBytes)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨3471⟩ (flip :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd3456 := h.jumpdest (by decide +native) (by evm_ov)
  have rd3457 := rd3456.dup2 (by decide +native) (by evm_ov)
  have rd3462 := rd3457.push4 ⟨107398807⟩ (by decide +native) (by evm_ov)
  have rd3464 := rd3462.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd3465 := rd3464.shl (by decide +native) (by evm_ov)
  rw [fileIlkFlipConst_eq, ← hmatch] at rd3465
  have rd3466 := rd3465.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd3466
  have rd3467 := rd3466.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3467
  have rd3470 := rd3467.push2 ⟨953⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd3470.jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)⟩

theorem RD.catFileIlkFlipWhatSkip {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {flip what ilk ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨3455⟩ (flip :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileIlkFlipBytes)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨953⟩ (flip :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd3456 := h.jumpdest (by decide +native) (by evm_ov)
  have rd3457 := rd3456.dup2 (by decide +native) (by evm_ov)
  have rd3462 := rd3457.push4 ⟨107398807⟩ (by decide +native) (by evm_ov)
  have rd3464 := rd3462.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd3465 := rd3464.shl (by decide +native) (by evm_ov)
  rw [fileIlkFlipConst_eq] at rd3465
  have rd3466 := rd3465.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileIlkFlipBytes) what = ⟨0⟩ :=
    u256_eq_of_ne (fun h1 => hneq h1.symm)
  rw [heq0] at rd3466
  have rd3467 := rd3466.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3467
  have rd3470 := rd3467.push2 ⟨953⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd3470.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

/-! ### nope-call encoder (⟨3471⟩ → EXTCODESIZE guard ⟨3546⟩)

Builds `mem[0]=ilk, mem[32]=1` (the `ilks[ilk]` keccak), loads `oldFlip = S[keccak(ilk,1)]`, and lays
the `nope(oldFlip&mask)` calldata at the free pointer `128`.  Leaves the canonical CALL words on the
stack for the void call to `vat`. -/

/-- Memory after `mem[0]=ilk; mem[32]=1` (the `ilks[ilk]` keccak preimage) over the auth memory. -/
noncomputable def fifKeccakMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (fileIlkFlipIlkWord I) ⟨1⟩ (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)

/-- `0x6e26907d << 225` — the `nope` selector `0xdc4d20fa` in the top 4 bytes of a word. -/
abbrev fifNopeSelShifted : UInt256 := UInt256.shiftLeft ⟨1848021117⟩ ⟨225⟩

/-- Memory after the `nope` selector `MSTORE` at `128`. -/
noncomputable def fifNopeSelMem (I : ExecutionEnv) : ByteArray :=
  fifNopeSelShifted.toByteArray.write 0 (fifKeccakMem I) 128 32

/-- Memory after the `nope` argument `MSTORE` at `132` — the full 36-byte `nope` calldata at `128`. -/
noncomputable def fifNopeCdMem (I : ExecutionEnv) (arg : UInt256) : ByteArray :=
  arg.toByteArray.write 0 (fifNopeSelMem I) 132 32

theorem fifKeccakMem_size (I : ExecutionEnv) : (fifKeccakMem I).size = 96 := by
  unfold fifKeccakMem
  exact twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)

theorem fifKeccakMem_read64 (I : ExecutionEnv) :
    (fifKeccakMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold fifKeccakMem
  exact twoWordHashMem_read64 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)

theorem fifKeccakMem_keccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((fifKeccakMem I).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I) := by
  unfold fifKeccakMem
  exact twoWordHashMem_solcMappingSlot ⟨1⟩ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)

theorem fifNopeSelMem_gapeq (I : ExecutionEnv) :
    fifNopeSelMem I = fifKeccakMem I ++ ffi.ByteArray.zeroes 32
      ++ UInt256.toByteArray fifNopeSelShifted := by
  unfold fifNopeSelMem
  rw [toByteArray_write_eq fifNopeSelShifted (fifKeccakMem I) 128
    (by rw [fifKeccakMem_size]; omega) (by rw [fifKeccakMem_size]; exact lt_usize 32 (by norm_num))]
  rw [fifKeccakMem_size]

theorem fifZeroes32_size : (ffi.ByteArray.zeroes 32).size = 32 := by
  rw [ByteArray_zeroes_size]

theorem fifNopeSelMem_size (I : ExecutionEnv) : (fifNopeSelMem I).size = 160 := by
  rw [fifNopeSelMem_gapeq, ByteArray.size_append, ByteArray.size_append, fifKeccakMem_size,
    fifZeroes32_size, toByteArray_size]

theorem fifNopeSelMem_read64 (I : ExecutionEnv) :
    (fifNopeSelMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have h2 : (64 : ℕ) + 32 ≤ (fifKeccakMem I ++ ffi.ByteArray.zeroes 32).size := by
    rw [ByteArray.size_append, fifKeccakMem_size, fifZeroes32_size]; omega
  have h3 : (64 : ℕ) + 32 ≤ (fifKeccakMem I).size := by rw [fifKeccakMem_size]
  rw [readWithPadding_eq_extract _ 64 (by rw [fifNopeSelMem_size]; omega),
    fifNopeSelMem_gapeq, extract_append_left _ _ 64 (64 + 32) h2,
    extract_append_left _ _ 64 (64 + 32) h3,
    ← readWithPadding_eq_extract (fifKeccakMem I) 64 h3]
  exact fifKeccakMem_read64 I

theorem fifNopeCdMem_size (I : ExecutionEnv) (arg : UInt256) :
    (fifNopeCdMem I arg).size = 164 := by
  unfold fifNopeCdMem
  exact toByteArray_write32_size_of_le (fifNopeSelMem I) arg 132 160 164
    (fifNopeSelMem_size I) (by rw [fifNopeSelMem_size]; omega) (by decide)

theorem fifNopeCdMem_read64 (I : ExecutionEnv) (arg : UInt256) :
    (fifNopeCdMem I arg).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold fifNopeCdMem
  rw [write32_read_below_len _ (fifNopeSelMem I) 132 64 32 (by rw [toByteArray_size])
    (by rw [fifNopeSelMem_size]; omega) (by omega) (by rw [fifNopeSelMem_size]; omega)
    (by norm_num) (by norm_num)]
  exact fifNopeSelMem_read64 I

theorem RD.catFileIlkFlipNopeEncode {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    (h : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3471⟩
      (flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3546⟩
      (UInt256.land (solcSlotWord σ I ⟨3⟩) solcAddrMask ::
        UInt256.land (solcSlotWord σ I ⟨3⟩) solcAddrMask :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ :: ⟨3696042234⟩ ::
        UInt256.land (solcSlotWord σ I ⟨3⟩) solcAddrMask ::
        flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
      (fifNopeCdMem I
        (UInt256.land solcAddrMask
          (solcSlotWord σ I (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I)))))
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  have hkeccak := fifKeccakMem_keccak I
  have hmload := mloadFreePtrValue (mem := fifKeccakMem I) (aw := ⟨3⟩)
    (by rw [fifKeccakMem_size I]; decide) (by decide) (fifKeccakMem_read64 I)
  -- 3471..3488: build ilks[ilk] keccak preimage, keccak, sload old flip
  have rd3473 := h.push1 ⟨3⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3474⟩ := rd3473.sload (by decide +native) (by evm_ov)
  have rd3476 := rd3474.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd3477 := rd3476.dup5 (by decide +native) (by evm_ov)
  have rd3478 := rd3477.dup2 (by decide +native) (by evm_ov)
  have rd3479 := rd3478.mstore 0 (wordAt0Mem (fileIlkFlipIlkWord I)
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd3481 := rd3479.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd3483 := rd3481.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd3484 := rd3483.mstore 0 (fifKeccakMem I) (UInt256.ofNat 3)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd3486 := rd3484.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd3487 := rd3486.dup1 (by decide +native) (by evm_ov)
  have rd3488 := rd3487.dup3 (by decide +native) (by evm_ov)
  have rd3489 := rd3488.keccak256 0 (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hkeccak (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3490⟩ := rd3489.sload (by decide +native) (by evm_ov)
  have rd3491 := rd3490.dup2 (by decide +native) (by evm_ov)
  have rd3492 := rd3491.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native) mem_cost hmload
    (by decide +native) (by evm_ov)
  -- 3492..3517: build the nope calldata (selector + masked old flip) at 128
  have rd3497 := rd3492.push4 ⟨1848021117⟩ (by decide +native) (by evm_ov)
  have rd3499 := rd3497.push1 ⟨225⟩ (by decide +native) (by evm_ov)
  have rd3500 := rd3499.shl (by decide +native) (by evm_ov)
  have rd3501 := rd3500.dup2 (by decide +native) (by evm_ov)
  have rd3502 := rd3501.mstore 6 (fifNopeSelMem I) (UInt256.ofNat 5)
    (by decide +native) mem_cost
    (by unfold fifNopeSelMem; rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl])
    (by decide +native) (by evm_ov)
  have rd3504 := rd3502.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd3506 := rd3504.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  have rd3508 := rd3506.push1 ⟨160⟩ (by decide +native) (by evm_ov)
  have rd3509 := rd3508.shl (by decide +native) (by evm_ov)
  have rd3510 := rd3509.sub (by decide +native) (by evm_ov)
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by decide]
    at rd3510
  have rd3511 := rd3510.swap2 (by decide +native) (by evm_ov)
  have rd3512 := rd3511.dup3 (by decide +native) (by evm_ov)
  have rd3513 := rd3512.and (by decide +native) (by evm_ov)
  have rd3515 := rd3513.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  have rd3516 := rd3515.dup3 (by decide +native) (by evm_ov)
  have rd3517 := rd3516.add (by decide +native) (by evm_ov)
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide] at rd3517
  have rd3518 := rd3517.mstore 3
    (fifNopeCdMem I (UInt256.land solcAddrMask
      (solcSlotWord σ I (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I))))) (UInt256.ofNat 6)
    (by decide +native) mem_cost
    (by unfold fifNopeCdMem; rw [show (⟨132⟩ : UInt256).toNat = 132 from rfl])
    (by decide +native) (by evm_ov)
  -- 3518..3546: shuffle the CALL words (gas/target/value/args/ret) into place
  have rd3519 := rd3518.swap2 (by decide +native) (by evm_ov)
  have rd3520 := rd3519.mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native) mem_cost
    (mloadFreePtrValue (mem := fifNopeCdMem I _) (aw := ⟨6⟩)
      (by rw [fifNopeCdMem_size]; decide) (by decide) (fifNopeCdMem_read64 I _))
    (by decide +native) (by evm_ov)
  have rd3521 := rd3520.swap4 (by decide +native) (by evm_ov)
  have rd3522 := rd3521.and (by decide +native) (by evm_ov)
  have rd3523 := rd3522.swap3 (by decide +native) (by evm_ov)
  have rd3528 := rd3523.push4 ⟨3696042234⟩ (by decide +native) (by evm_ov)
  have rd3529 := rd3528.swap3 (by decide +native) (by evm_ov)
  have rd3531 := rd3529.push1 ⟨36⟩ (by decide +native) (by evm_ov)
  have rd3532 := rd3531.dup1 (by decide +native) (by evm_ov)
  have rd3533 := rd3532.dup5 (by decide +native) (by evm_ov)
  have rd3534 := rd3533.add (by decide +native) (by evm_ov)
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide] at rd3534
  have rd3535 := rd3534.swap4 (by decide +native) (by evm_ov)
  have rd3536 := rd3535.swap2 (by decide +native) (by evm_ov)
  have rd3537 := rd3536.swap3 (by decide +native) (by evm_ov)
  have rd3539 := rd3537.swap2 (by decide +native) (by evm_ov)
  have rd3540 := rd3539.dup3 (by decide +native) (by evm_ov)
  have rd3541 := rd3540.swap1 (by decide +native) (by evm_ov)
  have rd3542 := rd3541.sub (by decide +native) (by evm_ov)
  rw [show UInt256.sub ⟨128⟩ ⟨128⟩ = ⟨0⟩ from by decide] at rd3542
  have rd3543 := rd3542.add (by decide +native) (by evm_ov)
  rw [show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd3543
  have rd3544 := rd3543.dup2 (by decide +native) (by evm_ov)
  have rd3545 := rd3544.dup4 (by decide +native) (by evm_ov)
  have rd3546 := rd3545.dup8 (by decide +native) (by evm_ov)
  exact ⟨_, _, rd3546.dup1 (by decide +native) (by evm_ov)⟩


end Benchmarks.Dss.Cat
