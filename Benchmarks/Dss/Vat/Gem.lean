import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `gem(bytes32,address)` nested mapping getter -/

abbrev gemIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev gemUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev gemUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (gemUsrWord I)

abbrev gemIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev gemUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (gemUsrWord I).toNat)

abbrev gemIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev gemUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (gemUsrWord I).toNat)

abbrev gemStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (gemIlkValue I)).insert "arg1" (gemUsrValue I)

theorem gemStore_index_arg0 (I : ExecutionEnv) :
    (gemStore I)["arg0"] = gemIlkValue I := by
  unfold gemStore
  rw [Std.HashMap.getElem_insert]
  simp

def gemStorageSlot (I : ExecutionEnv) : UInt256 :=
  gemSlot (gemIlkKey I) (gemUsrKey I)

abbrev gemEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gem", steps := [.mindex (gemIlkKey I), .mindex (gemUsrKey I)] }

theorem gemIlkKeyWord_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (gemIlkKey I) = gemIlkWord I := by
  unfold gemIlkKey gemIlkWord calldataWord
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (List.take 32 (List.drop 4 I.calldata.toList)).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      uInt256OfByteArray (I.calldata.readBytes 4 32) :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [keyValueToWord, bytes32Width, ABI.bytesToWord, fromByteArrayBigEndian,
    byteArray_toList_eq, show 32 ≤ I.calldata.size - 4 by omega] at hword ⊢
  exact hword

theorem gemStorageSlot_eq (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    gemStorageSlot I = solcMappingSlot (solcMappingSlot ⟨4⟩ (gemIlkWord I))
      (gemUsrMaskedWord I) := by
  unfold gemStorageSlot gemSlot gemIlkSlot gemUsrKey gemUsrMaskedWord mapSlot solcMappingSlot
  rw [gemIlkKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem decodeABIValues_bytes32_address_ok_legacy {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [bytes32, addr] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes bytes32Width (bytes.take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have htakeBytes32 :
      List.take (↑bytes32Width + 1) (List.take 32 bytes) = List.take 32 bytes := by
    simp [bytes32Width]
  simp [decodeABIValues?, decodeABIValue?, readBytes?, readWord?, decodeABIWord?,
    bytes32, addr, isDynamicABIType, staticABIEncodedSize?, hlen0, hge32,
    htakeBytes32, max, UInt256.toNat]

theorem decodeCalldata_legacyBytes32_legacyAddress_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [bytes32, addr] cd =
      some (((∅ : Store).insert x
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
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
  rw [if_neg (by simp [bytes32, addr, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by decide +native]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  rw [decodeABIValues_bytes32_address_ok_legacy
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyBytes32_legacyAddress_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [bytes32, addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by decide +native]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (cd.toList.drop 4).length < 64)]

theorem vatDecode_gem_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (gemTransition.params.map Param.name)
      (transitionSignature gemTransition).paramTypes I.calldata = some (gemStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [bytes32, addr]
    I.calldata = _
  simpa [config, gemStore, gemIlkValue, gemUsrValue, gemUsrWord] using
    decodeCalldata_legacyBytes32_legacyAddress_ok
      (cd := I.calldata) (x := "arg0") (y := "arg1") hsz68

theorem vatDecode_gem_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (gemTransition.params.map Param.name)
      (transitionSignature gemTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [bytes32, addr]
    I.calldata = none
  simpa [config] using decodeCalldata_legacyBytes32_legacyAddress_none_short
    (cd := I.calldata) (x := "arg0") (y := "arg1") hsz4 hshort

theorem vatDispatchGem {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 12)) :
    dispatchMsg contract I.calldata = some gemTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some gemTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes]
  decide +native

theorem vatReachGemBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 12)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨526⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x214414d5⟩ :=
    vatSelWord_eq_of_beq I hsz 0x21 0x44 0x14 0xd5 ⟨0x214414d5⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms419Body 2 (by omega) ⟨526⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by decide +native)

set_option maxHeartbeats 1000000 in
theorem RD.solcBytes32AddressExternalMaskAndJump {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd4 : decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd5 : decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd7 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd8 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd9 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd11 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd13 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd15 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd16 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd17 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd18 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd21 : decode code
        ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) +
          UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.dup1 hd2 (by evm_ov)
  have rd4 := rd3.calldataload hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd7 := rd5.push1 ⟨32⟩ hd5 (by evm_ov)
  have rd8 := rd7.add hd7 (by evm_ov)
  have rd9 := rd8.calldataload hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨1⟩ hd9 (by evm_ov)
  have rd13 := rd11.push1 ⟨1⟩ hd11 (by evm_ov)
  have rd15 := rd13.push1 ⟨160⟩ hd13 (by evm_ov)
  have rd16 := rd15.shl hd15 (by evm_ov)
  have rd17 := rd16.sub hd16 (by evm_ov)
  have rd18 := rd17.and hd17 (by evm_ov)
  have rd21 := rd18.push2 routine hd18 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd21.jump hd21 hroutine (by evm_ov)⟩

theorem vatGemBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some gemTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (gemTransition.params.map Param.name)
        (transitionSignature gemTransition).paramTypes I.calldata = some (gemStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨526⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let slot := solcMappingSlot (solcMappingSlot ⟨4⟩ (gemIlkWord I)) (gemUsrMaskedWord I)
  have hslot : gemStorageSlot I = slot := by
    simp [slot, gemStorageSlot_eq I hsz68]
  have harg0Len : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (gemStore I)
        gemTransition.body
        (.returned { contract := contract, locals := gemStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vatSlotWord (gemStorageSlot I) σ_solm I).toNat))])) := by
    simpa [gemTransition, gemStorageSlot, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vatUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (gemStore I)
        (ref := gemRef (.var "arg0") (.var "arg1")) (er := gemEvaledRef I)
        (slot := gemStorageSlot I)
        (by simp only [initState]; exact hwv) (by simp [gemStore, gemRef])
        (by
          simp [gemEvaledRef, gemIlkValue, gemUsrValue, gemIlkKey, gemUsrKey,
            evalStorageRef, evalStorageRefStep, gemRef, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?, gemStore_index_arg0, harg0Len,
            bytes32Width])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, gemIlkKey,
          gemUsrKey, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨526⟩) (ret := ⟨465⟩)
    (decoded := ⟨548⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcBytes32AddressExternalMaskAndJump
    (code := vatBytecode) (decoded := ⟨548⟩) (ret := ⟨465⟩) (routine := ⟨1987⟩)
    (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcNestedMappingGetter
    (code := vatBytecode) (pc := ⟨1987⟩) (baseSlot := ⟨4⟩)
    (owner := gemIlkWord I) (spender := gemUsrMaskedWord I)
    (ret := ⟨465⟩) (R := [sel])
    (by simpa [gemIlkWord, gemUsrMaskedWord, gemUsrWord] using hroutine)
    (by
      unfold solcNestedMappingGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (vatSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨465⟩) (val := vatSlotWord slot σ_evm I) (ret := ⟨465⟩) (R := [sel])
      (memout := solcScratchReturnMem
        (solcNestedMappingHashMem ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I))
        (vatSlotWord slot σ_evm I))
      (by simpa [slot, vatSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | decide +native)
      (by
        simpa [slot] using
          solcNestedMappingHashMem_mload64 ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (vatSlotWord slot σ_evm I)
          (solcNestedMappingHashMem_size ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I))
          (solcNestedMappingHashMem_read64 ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I)))
      (by
        exact solcScratchReturnMem_read128 (vatSlotWord slot σ_evm I)
          (solcNestedMappingHashMem_size ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I)))
      (by simp)
    simpa [slot, vatSlotWord] using hret'
  have hword : vatSlotWord slot σ_evm I = vatSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (vatSlotWord (gemStorageSlot I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (vatSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat))])
        gemTransition.returnType := by
    rw [show gemTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (vatSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem vatGemBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some gemTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨526⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := vatDecode_gem_none_short (I := I) hsz4 hshort
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨526⟩) (ret := ⟨465⟩)
    (decoded := ⟨548⟩) (need := ⟨64⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch hdec

theorem vatGemBodyCore : VatBodyTheorem 12 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 12) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some gemTransition :=
    vatDispatchGem hsel
  have hreach := vatReachGemBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact vatGemBodyCoreOk hcode hwv hsz68 hsize hdispatch
      (vatDecode_gem_ok hsz68) hreach hAccounts
  · exact vatGemBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
