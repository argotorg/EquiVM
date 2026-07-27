import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

abbrev chopArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev chopArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev chopArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (chopArgBytes I)

abbrev chopArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (chopArgBytes I)

abbrev chopLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (chopArgValue I)

abbrev chopEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (chopArgKey I), .field "chop"] }

abbrev chopSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (chopArgKey I) + ⟨1⟩

theorem dogDecode_chop_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (chopTransition.params.map Param.name)
      (transitionSignature chopTransition).paramTypes I.calldata =
        some (chopLocals I) := by
  simpa [config, chopTransition, chopLocals, chopArgValue, chopArgBytes, bytes32,
    bytes32Width] using
    (dogDecodeCalldataWithMode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36)

theorem dogDecode_chop_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (chopTransition.params.map Param.name)
      (transitionSignature chopTransition).paramTypes I.calldata = none := by
  simpa [config, chopTransition, bytes32, bytes32Width] using
    (dogDecodeCalldataWithMode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk")
      hsz4 hshort)

theorem chopArgBytes_len (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    (chopArgBytes I).length = bytes32Width.val + 1 := by
  unfold chopArgBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem chopArgBytes_len32 (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    (chopArgBytes I).length = 32 := by
  have hlen := chopArgBytes_len I hsz36
  simpa [bytes32Width] using hlen

theorem keyValueToWord_chopArgKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (chopArgKey I) = chopArgWord I := by
  have hlen32 : (chopArgBytes I).length = 32 :=
    chopArgBytes_len32 I hsz36
  have hword : ABI.bytesToWord (chopArgBytes I) = chopArgWord I := by
    simpa [chopArgBytes, chopArgWord] using
      (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
  have hbytes : chopArgBytes I = EVM.Word.toBytesBE (chopArgWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := chopArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [chopArgKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (chopArgWord I)

theorem chopSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    chopSlotFor I = solcMappingSlot ⟨1⟩ (chopArgWord I) + ⟨1⟩ := by
  unfold chopSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_chopArgKey hsz36]

theorem dogReachChopBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 4)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨629⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xd7926538⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd7 0x92 0x65 0x38 ⟨0xd7926538⟩
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
  have hchop : UInt256.eq (dogSelectorWord 4) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h629 := by
    simpa using
      h54.selectorArmTaken (selNat := dogSelectorWord 4) (tgt := (⟨629⟩ : UInt256))
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
        (dogPatchedDJumpPrefix1405 ⟨629⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h629⟩

theorem dogChopBodyCoreOk
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some chopTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (chopTransition.params.map Param.name)
        (transitionSignature chopTransition).paramTypes I.calldata = some (chopLocals I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨629⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := chopArgWord I
  let slot := solcMappingSlot ⟨1⟩ key + ⟨1⟩
  let locals := chopLocals I
  have hslot : chopSlotFor I = slot := by
    simpa [slot, key] using chopSlotFor_eq (I := I) hsz36
  have hkeyLen : (chopArgBytes I).length = bytes32Width.val + 1 :=
    chopArgBytes_len I hsz36
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        chopTransition.body
        (.returned { contract := contract v, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat
            (dogSlotWord (chopSlotFor I) σ_solm I).toNat))])) := by
    simpa [chopTransition, chopSlotFor, dogSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, locals] using
      dogUint256GetterBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := ilksF (.var "ilk") "chop") (er := chopEvaledRef I)
        (slot := chopSlotFor I)
        (by simp only [initState]; exact hwv)
        (by simp [locals, chopLocals, ilksF])
        (by
          simp [chopEvaledRef, chopArgKey, chopArgValue, evalStorageRef,
            evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
            EvalResult.ofOption, EvalResult.bind, pure, bind, locals, chopLocals,
            hkeyLen])
        (by
          simp [chopArgKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
            IlkStructTy, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨629⟩) (ret := ⟨448⟩)
    (decoded := ⟨651⟩) hreach
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
    (dogPatchedDJumpPrefix1405 ⟨651⟩ hpatch (by native_decide)) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (code := code) (decoded := ⟨651⟩) (ret := ⟨448⟩) (routine := ⟨2343⟩)
    (R := [sel]) hdecoded
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.solcIlksChopGetter
    (code := code) (pc := ⟨2343⟩) (key := key) (ret := ⟨448⟩) (R := [sel])
    (by simpa [key, chopArgWord] using hroutine)
    (by
      unfold solcIlksChopGetterWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (dogPatchedDJumpPrefix1405 ⟨448⟩ hpatch (by native_decide))
    (by simp only [List.length_singleton]; omega)
  have hret :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (dogSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨448⟩) (val := dogSlotWord slot σ_evm I) (ret := sel) (R := [])
      (memout := solcScratchReturnMem (twoWordHashMem key ⟨1⟩ solcFreePtrMem)
        (dogSlotWord slot σ_evm I))
      (by simpa [slot, dogSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first
          | apply And.intro
          | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
            native_decide)
      (by
        exact mloadFreePtrValue
          (by rw [twoWordHashMem_size_96 key ⟨1⟩ solcFreePtrMem_size]; decide)
          (by decide)
          (twoWordHashMem_read64 key ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (dogSlotWord slot σ_evm I)
          (twoWordHashMem_size_96 key ⟨1⟩ solcFreePtrMem_size)
          (twoWordHashMem_read64 key ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64))
      (by
        exact solcScratchReturnMem_read128 (dogSlotWord slot σ_evm I)
          (twoWordHashMem_size_96 key ⟨1⟩ solcFreePtrMem_size))
      (by simp)
    simpa [slot, dogSlotWord] using hret'
  have hword : dogSlotWord slot σ_evm I = dogSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (dogSlotWord (chopSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (dogSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (dogSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (dogSlotWord slot σ_evm I).toNat))])
        chopTransition.returnType := by
    rw [show chopTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (dogSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem dogChopBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some chopTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨629⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨629⟩) (ret := ⟨448⟩)
    (decoded := ⟨651⟩) (need := ⟨32⟩) hreach
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
    (dogDecode_chop_none_short (v := v) hsz4 hshort)

theorem dogChopBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 4) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some chopTransition :=
    dogDispatchChop hsel
  have hreach := dogReachChopBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact dogChopBodyCoreOk hpatch hcode hwv hsz36 hsize hdispatch
      (dogDecode_chop_ok (v := v) hsz36) hreach hAccounts
  · exact dogChopBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog
