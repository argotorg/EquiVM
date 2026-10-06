import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `sin(uint256)` mapping getter -/

abbrev sinMappingKey (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev sinMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sin", steps := [.mindex (.int (Int.ofNat (sinMappingKey I).toNat))] }

abbrev sinMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  sinSlot (.int (Int.ofNat (sinMappingKey I).toNat))

theorem sinMappingSlotFor_eq (I : ExecutionEnv) :
    sinMappingSlotFor I = solcMappingSlot ⟨4⟩ (sinMappingKey I) := by
  unfold sinMappingSlotFor sinMappingKey sinSlot mapSlot solcMappingSlot keyValueToWord
  simp only
  rw [wordOfInt_ofNat_toNat]

theorem vowDispatch_sin {I : ExecutionEnv} (hsel : selIs I ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩) :
    dispatchMsg contract I.calldata = some sinTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition, healTransition,
      humpTransition, kissTransition, liveTransition, relyTransition])
    (post := [sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := sinTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes, healSelectorBytes,
        humpSelectorBytes, kissSelectorBytes, liveSelectorBytes, relySelectorBytes, hcd]
      native_decide
  · rw [selectorOf, sinSelectorBytes]
    exact hsel

theorem vowDecode_sin_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (sinTransition.params.map Param.name)
      (transitionSignature sinTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.int (Int.ofNat (sinMappingKey I).toNat))) := by
  simpa [config, sinTransition, sinMappingKey, uint256] using
    (decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem vowDecode_sin_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (sinTransition.params.map Param.name)
      (transitionSignature sinTransition).paramTypes I.calldata = none := by
  simpa [config, sinTransition, uint256] using
    (decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem vowReachSinMappingBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        ⟨700⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vowSelWord I = ⟨3411853577⟩ :=
    vowSelWord_eq_of_beq I hsz 0xcb 0x5c 0xc1 0x09 ⟨3411853577⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc 0))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighHighBody 0 (by omega) ⟨700⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

theorem vowSinMappingBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some sinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (sinTransition.params.map Param.name)
        (transitionSignature sinTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.int (Int.ofNat (sinMappingKey I).toNat))))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨700⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let key := sinMappingKey I
  let slot := solcMappingSlot ⟨4⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat key.toNat))
  have hslot : sinMappingSlotFor I = slot := by
    simp [slot, key, sinMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals sinTransition.body
        (.returned { contract := contract, locals := locals }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt (sinMappingSlotFor I) σ I).toNat))])) := by
    simpa [sinTransition, sinMappingSlotFor, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      vowUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := sinRef (.var "arg0")) (er := sinMappingEvaledRef I)
        (slot := sinMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, sinRef])
        (by
          simp [sinMappingEvaledRef, sinMappingKey, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, sinRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals, key])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨700⟩) (ret := ⟨357⟩)
    (decoded := ⟨722⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ :
      ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4084⟩
        [key, ⟨357⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
    have rd723 := hdecoded.jumpdest (by native_decide) (by evm_ov)
    have rd724 := rd723.pop (by native_decide) (by evm_ov)
    have rd725 := rd724.calldataload (by native_decide) (by evm_ov)
    have rd728 := rd725.push2 ⟨4084⟩ (by native_decide) (by evm_ov)
    exact ⟨_, _, by
      simpa [key, sinMappingKey, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
        using rd728.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := vowBytecode) (pc := ⟨4084⟩) (baseSlot := ⟨4⟩) (key := key)
    (ret := ⟨357⟩) (R := [sel]) hroutine
    (by
      unfold solcSingleMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vowBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨357⟩) (val := solcSlotWordAt slot σ I) (ret := ⟨357⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨4⟩ key)
        (solcSlotWordAt slot σ I))
      (by simpa [slot, solcSlotWordAt] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨4⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨4⟩ key) (solcMappingHashMem_read64 ⟨4⟩ key))
      (by
        exact solcScratchReturnMem_read128 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨4⟩ key))
      (by simp)
    simpa [slot, solcSlotWordAt] using hret'
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        sinTransition.returnType := by
    rw [show sinTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  rw [hslot] at hbody
  exact hret.reEquivExecution hcode hdispatch hdecode hbody henc

theorem vowSinMappingBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := by omega
  exact vowSinMappingBodyCore hcode hwv hsz36 hsize (vowDispatch_sin hsel)
    (vowDecode_sin_ok hsz36)
    (vowReachSinMappingBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

theorem vowSinMappingShort {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hreach :=
    vowReachSinMappingBody (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨700⟩) (ret := ⟨357⟩)
    (decoded := ⟨722⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_sin hsel)
    (vowDecode_sin_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
