import Benchmarks.Dss.End.Trusted

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000

attribute [local simp]
  wardsSelectorBytes vatSelectorBytes catSelectorBytes dogSelectorBytes vowSelectorBytes
  potSelectorBytes spotSelectorBytes cureSelectorBytes liveSelectorBytes whenSelectorBytes
  waitSelectorBytes debtSelectorBytes tagSelectorBytes gapSelectorBytes ArtSelectorBytes
  fixSelectorBytes bagSelectorBytes outSelectorBytes relySelectorBytes denySelectorBytes
  fileAddressSelectorBytes fileUintSelectorBytes cageSelectorBytes cageIlkSelectorBytes
  snipSelectorBytes skipSelectorBytes skimSelectorBytes freeSelectorBytes thawSelectorBytes
  flowSelectorBytes packSelectorBytes cashSelectorBytes

abbrev outIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev outUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev outUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (outUsrWord I)

abbrev outIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (outIlkWord I))

abbrev outUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (outUsrWord I).toNat)

abbrev outIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (outIlkWord I))

abbrev outUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (outUsrWord I).toNat)

abbrev outStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (outIlkValue I)).insert "arg1" (outUsrValue I)

def outStorageSlot (I : ExecutionEnv) : UInt256 :=
  outSlot (outIlkKey I) (outUsrKey I)

def outWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (outStorageSlot I) σ I

theorem outStorageSlot_eq (I : ExecutionEnv) :
    outStorageSlot I =
      solcMappingSlot (solcMappingSlot ⟨17⟩ (outIlkWord I)) (outUsrMaskedWord I) := by
  unfold outStorageSlot outSlot outIlkSlot mapSlot solcMappingSlot outIlkKey outUsrKey
  unfold outIlkWord outUsrMaskedWord outUsrWord bytes32Width
  rw [keyValueToWord_fixedBytes32, keyValueToWord_address_ofNat_mask]

theorem endDecode_out_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (outTransition.params.map Param.name)
      (transitionSignature outTransition).paramTypes I.calldata = some (outStore I) := by
  simpa [config, outTransition, outStore, outIlkValue, outUsrValue, outIlkWord, outUsrWord]
    using (endDecodeCalldata_legacyBytes32Address_ok (cd := I.calldata)
      (x := "arg0") (y := "arg1") hsz68)

theorem endDecode_out_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (outTransition.params.map Param.name)
      (transitionSignature outTransition).paramTypes I.calldata = none := by
  simpa [config, outTransition]
    using (endDecodeCalldata_legacyBytes32Address_none_short (cd := I.calldata)
      (x := "arg0") (y := "arg1") hsz4 hshort)

theorem endDispatchOutLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 17)) :
    dispatchMsg contract I.calldata = some outTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 17 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some outTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, outSelectorBytes]
  native_decide

theorem endOutBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (outStore I) outTransition.body
      (.returned { contract := contract, locals := outStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (outStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := outStore I })
        (slot := outRef (.var "arg0") (.var "arg1"))
        (er := ({ base := "out", steps := [.mindex (outIlkKey I), .mindex (outUsrKey I)] } :
          EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (outStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (outStorageSlot I)).toNat))
        (hbase := by simp [outStore, outRef])
        (her := by
          have hget0v :
              (outStore I)["arg0"] = outIlkValue I := by
            unfold outStore
            rw [Std.HashMap.getElem_insert]
            simp
          have hget1v :
              (outStore I)["arg1"] = outUsrValue I := by
            unfold outStore
            rw [Std.HashMap.getElem_insert]
            simp
          have hlen :
              (EVM.Word.toBytesBE (outIlkWord I)).length = 32 := by
            simpa using word_toBytesBE_toByteArray_size (outIlkWord I)
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, outRef, hget0v, hget1v,
            outIlkValue, outUsrValue, outIlkKey, outUsrKey, bytes32Width, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?, valueToKey?, hlen])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, outIlkKey, outUsrKey,
            uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (outStorageSlot I))])

set_option maxHeartbeats 5000000 in
theorem endReachOutBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 17)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1054⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xc939ebfc⟩ :=
    endSelWord_eq_of_beq I hsz 0xc9 0x39 0xeb 0xfc ⟨0xc939ebfc⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot : UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 := RD.selectorSplitNotTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by simp)
  have h43gt : UInt256.gt (armSelNat endBytecode (⟨43⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h162 := RD.selectorSplitTakenAuto h43
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h43gt (by jump_dest) (by simp)
  have h163 := h162.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h163gt : UInt256.gt (armSelNat endBytecode (⟨163⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h174 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
      selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h163
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h163gt (by simp)
  have hwards0 : UInt256.eq (armSelNat endBytecode (⟨174⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hdog0 : UInt256.eq (armSelNat endBytecode (⟨185⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hfree0 : UInt256.eq (armSelNat endBytecode (⟨196⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hout :
      UInt256.eq (armSelNat endBytecode (⟨207⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h1054 := h174
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hwards0 (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hdog0 (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hfree0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hout (by jump_dest) (by simp)
  exact ⟨_, _, h1054⟩

theorem endOutX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1054⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (outWord σ I)) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (entry := ⟨1054⟩) (ret := ⟨509⟩) (decoded := ⟨1076⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcBytes32AddressExternalMaskAndJumpMasked
    (decoded := ⟨1076⟩) (ret := ⟨509⟩) (routine := ⟨8239⟩) (R := [sel])
    hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hwf : solcNestedMappingGetterWf endBytecode ⟨8239⟩ ⟨17⟩ := by
    unfold solcNestedMappingGetterWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, hinner⟩ := RD.solcNestedMappingInnerHash
    (pc := ⟨8239⟩) (baseSlot := ⟨17⟩)
    (owner := outIlkWord I) (spender := outUsrMaskedWord I) (ret := ⟨509⟩)
    (R := [sel]) hroutine hwf (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, houter⟩ := RD.solcNestedMappingOuterHash
    (pc := ⟨8239⟩) (baseSlot := ⟨17⟩)
    (owner := outIlkWord I) (spender := outUsrMaskedWord I) (ret := ⟨509⟩)
    (R := [sel]) hinner hwf (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.solcNestedMappingLoadAndJump
    (pc := ⟨8239⟩) (baseSlot := ⟨17⟩)
    (slot := solcMappingSlot (solcMappingSlot ⟨17⟩ (outIlkWord I)) (outUsrMaskedWord I))
    (ret := ⟨509⟩) (R := [sel]) houter hwf
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hslot : outStorageSlot I =
      solcMappingSlot (solcMappingSlot ⟨17⟩ (outIlkWord I)) (outUsrMaskedWord I) :=
    outStorageSlot_eq I
  have hret :
      RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray (endSlotWord (outStorageSlot I) σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨509⟩)
      (val := endSlotWord
        (solcMappingSlot (solcMappingSlot ⟨17⟩ (outIlkWord I)) (outUsrMaskedWord I)) σ I)
      (ret := ⟨509⟩) (R := [sel])
      (memout := solcScratchReturnMem
        (solcNestedMappingHashMem ⟨17⟩ (outIlkWord I) (outUsrMaskedWord I))
        (endSlotWord
          (solcMappingSlot (solcMappingSlot ⟨17⟩ (outIlkWord I)) (outUsrMaskedWord I)) σ I))
      (by simpa [endSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by exact solcNestedMappingHashMem_mload64 ⟨17⟩ (outIlkWord I) (outUsrMaskedWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64
          (endSlotWord
            (solcMappingSlot (solcMappingSlot ⟨17⟩ (outIlkWord I)) (outUsrMaskedWord I))
            σ I)
          (solcNestedMappingHashMem_size ⟨17⟩ (outIlkWord I) (outUsrMaskedWord I))
          (solcNestedMappingHashMem_read64 ⟨17⟩ (outIlkWord I) (outUsrMaskedWord I)))
      (by
        exact solcScratchReturnMem_read128
          (endSlotWord
            (solcMappingSlot (solcMappingSlot ⟨17⟩ (outIlkWord I)) (outUsrMaskedWord I))
            σ I)
          (solcNestedMappingHashMem_size ⟨17⟩ (outIlkWord I) (outUsrMaskedWord I)))
      (by simp only [List.length_singleton]; omega)
    simpa [endSlotWord, hslot] using hret'
  simpa [outWord] using hret

theorem endOutX_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1054⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hltShort :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (show (⟨4⟩ : UInt256).toNat ≤ I.calldata.size by simpa using hsz4)
      hsize]
    simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
      show (⟨4⟩ : UInt256).toNat = 4 from rfl]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (entry := ⟨1054⟩) (ret := ⟨509⟩) (decoded := ⟨1076⟩) (need := ⟨64⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    hltShort

theorem endOutBodyCore : endBodyObligation 17 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 17) rfl hsel
  have hdispatch := endDispatchOutLocal hsel
  have hreach :=
    endReachOutBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hword : outWord σ_evm I = outWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (outStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (outStore I)
          outTransition.body
          (.returned { contract := contract, locals := outStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (outWord σ_solm I).toNat))])) := by
      simpa [outWord, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        endOutBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hret :=
      endOutX_ok (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    exact hret.reEquivExecutionTransport hcode hdispatch (endDecode_out_ok hsz68) hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (outWord σ_evm I)))
  · have hshort : I.calldata.size < 68 := by omega
    have hrev :=
      endOutX_short (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_out_none_short hsz4 hshort)

end Benchmarks.Dss.End
