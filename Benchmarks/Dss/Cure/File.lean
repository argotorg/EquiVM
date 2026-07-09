import Benchmarks.Dss.Cure.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cure

/-! ## `file(bytes32,uint256)` -/

abbrev fileWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileWaitBytes : List UInt8 :=
  [119, 97, 105, 116] ++ zeroPad28

abbrev fileLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileWhat I))).insert
    "data" (.int (Int.ofNat (fileData I).toNat))

theorem fileWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileWhat I).length = 32 := by
  simp [fileWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileWhat I) = calldataWord I.calldata 4 := by
  simpa [fileWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileWhat I)
    (fileWhat_length (I := I) hsz36)
  rw [fileWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileWhatWord_eq (I := I) hsz36).symm

theorem fileWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem decodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt

theorem decodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem decodeCalldata_legacyBytes32_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decodeCalldata_legacyBytes32_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem cureDecode_file_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata =
        some (fileLocals I) := by
  simpa [config, fileTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileLocals, fileWhat, fileData, abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem cureDecode_file_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata = none := by
  simpa [config, fileTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem cureDispatchFile {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 4)) :
    dispatchMsg contract I.calldata = some fileTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes]
  native_decide

theorem cureReachFileBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 4)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨449⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x29ae8114⟩ :=
    cureSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h245⟩ := cureReachLowLowerFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨449⟩ 2 h245 (fun j hj => cureLowLowerArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem RD.cureFileDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨471⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = cureBytecode)
    (hroutine : (D_J code 0).contains ⟨1027⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1027⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd472 := h.jumpdest (by native_decide) (by evm_ov)
  have rd473 := rd472.pop (by native_decide) (by evm_ov)
  have rd474 := rd473.dup1 (by native_decide) (by evm_ov)
  have rd475 := rd474.calldataload (by native_decide) (by evm_ov)
  have rd476 := rd475.swap1 (by native_decide) (by evm_ov)
  have rd478 := rd476.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd479 := rd478.add (by native_decide) (by evm_ov)
  have rd480 := rd479.calldataload (by native_decide) (by evm_ov)
  have rd483 := rd480.push2 ⟨1027⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd483.jump (by native_decide) hroutine (by evm_ov)⟩

theorem cureFileX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD cureBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1027⟩
        [fileData I, calldataWord I.calldata 4, ⟨484⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := cureBytecode) (sel := sel) (entry := ⟨449⟩) (ret := ⟨484⟩)
    (decoded := ⟨471⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.cureFileDecodeToRoutine
    (code := cureBytecode) (ret := ⟨484⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileData] using hroutine⟩

theorem cureFileX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD cureBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := cureBytecode) (sel := sel) (entry := ⟨449⟩) (ret := ⟨484⟩)
    (decoded := ⟨471⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem cureFileX_afterLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (h : RD cureBytecode I g s0 ⟨1027⟩
      [fileData I, calldataWord I.calldata 4, ⟨484⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD cureBytecode I g s0 ⟨1188⟩
      [fileData I, calldataWord I.calldata 4, ⟨484⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [cureCallerWardsSlot, cureSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
    (code := cureBytecode) (pc := ⟨1027⟩) (okPc := ⟨1117⟩)
    (key := fileData I) (ret := calldataWord I.calldata 4) (R := [⟨484⟩, sel])
    h
    (by
      unfold cureAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ I ⟨1⟩ = ⟨1⟩ := by
    simpa [cureSlotWord] using hlive
  exact RD.cureLiveGuardOk
    (code := cureBytecode) (pc := ⟨1117⟩) (okPc := ⟨1188⟩)
    (key := fileData I) (ret := calldataWord I.calldata 4) (R := [⟨484⟩, sel])
    hafterAuth
    (by
      unfold cureLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)

theorem fileWaitShiftConst :
    UInt256.shiftLeft (⟨500718173⟩ : UInt256) ⟨226⟩ =
      ABI.bytesToWord fileWaitBytes := by
  native_decide

theorem RD.cureFileWaitStorePrefix {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {data what ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hmatch : what = ABI.bytesToWord fileWaitBytes)
    (h : RD cureBytecode I g s0 ⟨1188⟩
      (data :: what :: ret :: R) mem aw rdata (cA, σ) k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD cureBytecode I g s0 ⟨1290⟩
      (data :: what :: ret :: R) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ data) k' C' := by
  have rd1189 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1190 := rd1189.dup2 (by native_decide) (by evm_ov)
  have rd1195 := rd1190.pushConst (⟨500718173⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1197 := rd1195.push1 ⟨226⟩ (by native_decide) (by evm_ov)
  have rd1198raw := rd1197.shl (by native_decide) (by evm_ov)
  have rd1198 := rd1198raw
  rw [hmatch, ← fileWaitShiftConst] at rd1198
  have rd1199raw := rd1198.eq (by native_decide) (by evm_ov)
  have rd1199 := rd1199raw
  rw [uInt256_eq_self] at rd1199
  have rd1200raw := rd1199.iszero (by native_decide) (by evm_ov)
  have rd1200 := rd1200raw
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1200
  have rd1203 := rd1200.push2 ⟨1213⟩ (by native_decide) (by evm_ov)
  have rd1204 := rd1203.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1206 := rd1204.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd1207 := rd1206.dup2 (by native_decide) (by evm_ov)
  have rd1208 := rd1207.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1209⟩ := rd1208.sstore hperm (by native_decide) (by evm_ov)
  have rd1212 := rd1209.push2 ⟨1290⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [hmatch, fileWaitShiftConst] using
      rd1212.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem cureFileX_storeWaitPrefix {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileWaitBytes)
    (h : RD cureBytecode I g s0 ⟨1188⟩
      [fileData I, calldataWord I.calldata 4, ⟨484⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD cureBytecode I g s0 ⟨1290⟩
      [fileData I, calldataWord I.calldata 4, ⟨484⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ (fileData I)) k' C' := by
  exact RD.cureFileWaitStorePrefix hperm hmatch h (by simp)

abbrev cureFileEventTopic : UInt256 :=
  ⟨105627225169409785158710363763375725481095598661489361122320324215644262229191⟩

theorem fileEventMem_size {mem : ByteArray} (data : UInt256)
    (hmem : mem.size = 96) :
    ((UInt256.toByteArray data).write 0 mem 128 32).size = 160 := by
  exact toByteArray_write32_size_of_ge mem data 128 96 160 hmem (by omega)
    (by native_decide) (by omega)

theorem fileEventMem_read64 {mem : ByteArray} (data : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ((UInt256.toByteArray data).write 0 mem 128 32).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    native_decide
  have hreadBound : 64 + 32 ≤ mem.size := by
    omega
  have hbelow : 64 + 32 ≤ 128 := by
    norm_num
  rw [toByteArray_write_read_below_of_gap data mem 128 64
    hreadBound hbelow hgap]
  exact hread64

theorem RD.cureFileEventTail {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {data what : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    (h : RD cureBytecode I g s0 ⟨1290⟩ (data :: what :: ⟨484⟩ :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDret cureBytecode g s0 (cA, σ) ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmemoutRead64 :
      ((UInt256.toByteArray data).write 0 mem 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    fileEventMem_read64 data hmem hread64
  have hmemoutSize :
      ((UInt256.toByteArray data).write 0 mem 128 32).size = 160 :=
    fileEventMem_size data hmem
  have hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥
            ((UInt256.toByteArray data).write 0 mem 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray data).write 0 mem 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemoutSize]; decide) (by decide) hmemoutRead64
  have rd1291 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1293 := rd1291.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1294 := rd1293.dup1 (by native_decide) (by evm_ov)
  have rd1295 := rd1294.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost hmload64 (by native_decide) (by evm_ov)
  have rd1297 := evm_run rd1295 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1298 := rd1297.mstore 6 ((UInt256.toByteArray data).write 0 mem 128 32)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1300 := evm_run rd1298 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hlogMload (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd1335 := rd1300.pushConst cureFileEventTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1344 := evm_run rd1335 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1345 := RD.cureLog2 0 (UInt256.ofNat 5) rd1344
    (by native_decide) hperm mem_cost (by native_decide)
    (by
      simp only [List.length_cons]
      omega)
  have rd1347 := evm_run rd1345 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rdRet := rd1347.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rdStop := rdRet.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rdStop (by native_decide) (by evm_ov)

theorem cureFileX_storeWait {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileWaitBytes)
    (h : RD cureBytecode I g s0 ⟨1188⟩
      [fileData I, calldataWord I.calldata 4, ⟨484⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret cureBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ (fileData I)) ByteArray.empty := by
  obtain ⟨_, _, h1290⟩ := cureFileX_storeWaitPrefix hperm hmatch h
  have hmem :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  exact RD.cureFileEventTail h1290 hperm hmem hread64 (by simp)

abbrev cureFileUnrecognizedRawWord : UInt256 :=
  ⟨30512471488687873977596731382547105769570624897107015348524753129233065181184⟩

theorem RD.cureFileUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1213⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have rdMload := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨28⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨28⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst cureFileUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨28⟩ cureFileUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨28⟩ cureFileUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem cureFileX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileWaitBytes)
    (h : RD cureBytecode I g s0 ⟨1188⟩
      [fileData I, calldataWord I.calldata 4, ⟨484⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev cureBytecode g s0 := by
  have rd1189 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1190 := rd1189.dup2 (by native_decide) (by evm_ov)
  have rd1195 := rd1190.pushConst (⟨500718173⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1197 := rd1195.push1 ⟨226⟩ (by native_decide) (by evm_ov)
  have rd1198 := rd1197.shl (by native_decide) (by evm_ov)
  rw [fileWaitShiftConst] at rd1198
  have rd1199 := rd1198.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileWaitBytes) (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun hbad => hneq hbad.symm)
  rw [heq0] at rd1199
  have rd1200 := rd1199.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1200
  have rd1203 := rd1200.push2 ⟨1213⟩ (by native_decide) (by evm_ov)
  have rd1213 := rd1203.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  have hmem :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  exact RD.cureFileUnrecognizedRevert rd1213 hmem hread64 (by simp)

theorem fileLocals_get_what (I : ExecutionEnv) :
    (fileLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileWhat I)) := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileLocals_get_data (I : ExecutionEnv) :
    (fileLocals I).get? "data" =
      some (.int (Int.ofNat (fileData I).toNat)) := by
  rw [fileLocals, store_get_self]

theorem fileLocals_get_wards (I : ExecutionEnv) :
    (fileLocals I).get? "wards" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLocals_get_live (I : ExecutionEnv) :
    (fileLocals I).get? "live" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLocals_get_wait (I : ExecutionEnv) :
    (fileLocals I).get? "wait" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileWhat I)))
    (hwhat : fileWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileWhat I)))
    (hwhat : fileWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileWaitStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ (fileData I)
    assignStorageRef? config { contract := contract, locals := fileLocals I } evm
      .storage waitRef (.int (Int.ofNat (fileData I).toNat)) =
        .ok ({ contract := contract, locals := fileLocals I }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨3⟩)
    (er := ({ base := "wait", steps := [] } : EvaledStorageRef))
    (hbase := fileLocals_get_wait I)
    (her := by simp [waitRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := by simpa [evm'] using storageLocStore_uint256 evm ⟨3⟩ (fileData I))

theorem cureFileSourceBodyOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hwhat : fileWhat I = fileWaitBytes) :
    let locals := fileLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ (fileData I)
    ExecTransitionBody config contract evm0 locals fileTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simpa [locals] using fileLocals_get_wards I) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simpa [locals] using fileLocals_get_live I) hlive
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool true) := by
    simpa [waitParamLit, fileWaitBytes] using
      (evalExpr_fileWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileWaitBytes) (by simpa [locals] using fileLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileData I).toNat)) :=
    evalExpr_fileData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage waitRef (.int (Int.ofNat (fileData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileWaitStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage waitRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) :=
    ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem cureFileSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := fileLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
  intro locals evm0
  have hguard := cureAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simpa [locals] using fileLocals_get_wards I) hauth
  have hblock := nonpayableSecondRequireReverts
    (cfg := config) (solm := { contract := contract, locals := locals })
    (evm := evm0)
    (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
    (rest := [
      .require (.binary .eq (.storage liveRef) (.intLit 1)),
      .ite (.binary .eq (.var "what") waitParamLit)
        [.assign .storage waitRef (.var "data")] [.require (.boolLit false)]])
    (by simp [evm0, initState]; exact hwv)
    hguard
  simpa [ExecTransitionBody, fileTransition, nonpayable, auth, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureFileSourceBodyLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I ≠ ⟨1⟩) :
    let locals := fileLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
  intro locals evm0
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simpa [locals] using fileLocals_get_wards I) hauth
  have hguardLive := cureLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simpa [locals] using fileLocals_get_live I) hlive
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem cureFileSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hwhat : fileWhat I ≠ fileWaitBytes) :
    let locals := fileLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
  intro locals evm0
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simpa [locals] using fileLocals_get_wards I) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simpa [locals] using fileLocals_get_live I) hlive
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool false) := by
    simpa [waitParamLit, fileWaitBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileWaitBytes) (by simpa [locals] using fileLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem cureFileBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let sel := cureSelWord I
  let callerSlot := cureCallerWardsSlot I
  let locals := fileLocals I
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 4) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileTransition :=
    cureDispatchFile hsel
  have hreach := cureReachFileBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
          (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I) :=
      cureDecode_file_ok hsz68
    have hcallerWord :
        cureSlotWord callerSlot σ_evm I = cureSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have hliveWord :
        cureSlotWord ⟨1⟩ σ_evm I = cureSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    obtain ⟨_, _, hdecoded⟩ := cureFileX_decoded (g := Sat256.ofUInt256 g)
      (sel := sel) hsz68 hsize hreach
    by_cases hauthEvm : cureSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : cureSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
        (code := cureBytecode) (pc := ⟨1027⟩) (okPc := ⟨1117⟩)
        (key := fileData I) (ret := calldataWord I.calldata 4) (R := [⟨484⟩, sel])
        hdecoded
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by jump_dest) (by simp)
      by_cases hliveEvm : cureSlotWord ⟨1⟩ σ_evm I = ⟨1⟩
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨1⟩ := by
          rw [← hliveWord]
          exact hliveEvm
        obtain ⟨_, _, hafterLive⟩ := RD.cureLiveGuardOk
          (code := cureBytecode) (pc := ⟨1117⟩) (okPc := ⟨1188⟩)
          (key := fileData I) (ret := calldataWord I.calldata 4) (R := [⟨484⟩, sel])
          hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | native_decide)
          (by simpa [cureSlotWord] using hliveEvm) (by jump_dest) (by simp)
        by_cases hwhat : fileWhat I = fileWaitBytes
        · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ (fileData I)
          have hbody :
              ExecTransitionBody config contract evm0 locals fileTransition.body
                (.returned { contract := contract, locals := locals } evm1 none) := by
            simpa [evm0, evm1, locals] using
              (cureFileSourceBodyOk (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hwhat)
          have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileWaitBytes :=
            fileWhatWord_eq_of_bytes_eq (by omega) hwhat
          have hret := cureFileX_storeWait (I := I) hperm hmatch hafterLive
          have hcreated :
              (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ (fileData I)).1 =
                evm1.createdAccounts := by
            simp [evm1, evm0, initState, storageStore_createdAccounts]
          have haccounts :
              accountMapEquiv
                (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ (fileData I)).2
                evm1.accountMap := by
            simpa [evm1, evm0, initState, storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ (fileData I) hAccounts
          have henc : returnEquiv ByteArray.empty none fileTransition.returnType := by
            rw [show fileTransition.returnType = [] by rfl]
            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            hcreated haccounts henc
        · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hbody :
              ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
            simpa [evm0, locals] using
              (cureFileSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hwhat)
          have hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileWaitBytes :=
            fileWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
          exact (cureFileX_unrecognized (I := I) hneq hafterLive)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I ≠ ⟨1⟩ := by
          intro hsolm
          exact hliveEvm (by rw [hliveWord, hsolm])
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
          simpa [evm0, locals] using
            (cureFileSourceBodyLiveReverts (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hliveSolm)
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hrev := RD.cureLiveGuardRevert
          (code := cureBytecode) (pc := ⟨1117⟩) (okPc := ⟨1188⟩)
          (key := fileData I) (ret := calldataWord I.calldata 4) (R := [⟨484⟩, sel])
          hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | native_decide)
          (by
            unfold solcErrorStringRevertTailWf cureLiveGuardTailPc cureNotLiveRawWord
            repeat' first | apply And.intro | native_decide)
          (by simpa [cureSlotWord] using hliveEvm) hmemAuth hread64 (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : cureSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
        simpa [evm0, locals] using
          (cureFileSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm)
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      have hrev := RD.cureAuthCheckRevert
        (code := cureBytecode) (pc := ⟨1027⟩) (okPc := ⟨1117⟩)
        (key := fileData I) (ret := calldataWord I.calldata 4) (R := [⟨484⟩, sel])
        hdecoded
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold solcErrorStringRevertTailWf cureAuthTailPc cureNotAuthorizedRawWord
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hrev := cureFileX_shortarg (g := Sat256.ofUInt256 g) (sel := sel)
      hsz4 hsize (by omega) hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (cureDecode_file_none_short hsz4 (by omega))

end Benchmarks.Dss.Cure
