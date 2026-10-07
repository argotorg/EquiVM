import Reasoning.SolcRoutines
import Reasoning.ABIViews
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
  simpa [config] using decodeCalldata_legacyBytes32_address_none_short
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
  native_decide

theorem vatReachGemBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 12)) :
    ∃ k C, RD vatBytecode I g (initState σ σ₀ g A I)
        ⟨526⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vatSelWord I = ⟨0x214414d5⟩ :=
    vatSelWord_eq_of_beq I hsz 0x21 0x44 0x14 0xd5 ⟨0x214414d5⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms419Body 2 (by omega) ⟨526⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by native_decide)


theorem vatGemBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some gemTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (gemTransition.params.map Param.name)
        (transitionSignature gemTransition).paramTypes I.calldata = some (gemStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨526⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
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
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (gemStore I)
        gemTransition.body
        (.returned { contract := contract, locals := gemStore I }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt (gemStorageSlot I) σ I).toNat))])) := by
    simpa [gemTransition, gemStorageSlot, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vatUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (gemStore I)
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
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcBytes32AddressExternalMaskAndJump
    (code := vatBytecode) (decoded := ⟨548⟩) (ret := ⟨465⟩) (routine := ⟨1987⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcNestedMappingGetter
    (code := vatBytecode) (pc := ⟨1987⟩) (baseSlot := ⟨4⟩)
    (owner := gemIlkWord I) (spender := gemUsrMaskedWord I)
    (ret := ⟨465⟩) (R := [sel])
    (by simpa [gemIlkWord, gemUsrMaskedWord, gemUsrWord] using hroutine)
    (by
      unfold solcNestedMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨465⟩) (val := solcSlotWordAt slot σ I) (ret := ⟨465⟩) (R := [sel])
      (memout := solcScratchReturnMem
        (solcNestedMappingHashMem ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I))
        (solcSlotWordAt slot σ I))
      (by simpa [slot, solcSlotWordAt] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        simpa [slot] using
          solcNestedMappingHashMem_mload64 ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (solcSlotWordAt slot σ I)
          (solcNestedMappingHashMem_size ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I))
          (solcNestedMappingHashMem_read64 ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I)))
      (by
        exact solcScratchReturnMem_read128 (solcSlotWordAt slot σ I)
          (solcNestedMappingHashMem_size ⟨4⟩ (gemIlkWord I) (gemUsrMaskedWord I)))
      (by simp)
    simpa [slot, solcSlotWordAt] using hret'
  rw [hslot] at hbody
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        gemTransition.returnType := by
    rw [show gemTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  exact hret.reEquivExecution hcode hdispatch hdecode hbody henc

theorem vatGemBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some gemTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨526⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
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
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch hdec

theorem vatGemBodyCore : VatBodyTheoremAnyPerm 12 := by
  intro σ σ₀ A I g hcode hsize hwv hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 12) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some gemTransition :=
    vatDispatchGem hsel
  have hreach := vatReachGemBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact vatGemBodyCoreOk hcode hwv hsz68 hsize hdispatch
      (vatDecode_gem_ok hsz68) hreach
  · exact vatGemBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
