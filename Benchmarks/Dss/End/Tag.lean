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

abbrev tagArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev tagArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (tagArgWord I))

abbrev tagArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (tagArgWord I))

abbrev tagStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (tagArgValue I)

def tagStorageSlot (I : ExecutionEnv) : UInt256 :=
  tagSlot (tagArgKey I)

def tagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (tagStorageSlot I) σ I

theorem tagStorageSlot_eq (I : ExecutionEnv) :
    tagStorageSlot I = solcMappingSlot ⟨12⟩ (tagArgWord I) := by
  unfold tagStorageSlot tagSlot mapSlot solcMappingSlot tagArgKey tagArgWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

theorem endDecode_tag_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tagTransition.params.map Param.name)
      (transitionSignature tagTransition).paramTypes I.calldata = some (tagStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata =
    some (tagStore I)
  simpa [tagStore, tagArgValue, tagArgWord] using
    endDecodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36

theorem endDecode_tag_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (tagTransition.params.map Param.name)
      (transitionSignature tagTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata = none
  simpa using endDecodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

theorem endDispatchTagLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 12)) :
    dispatchMsg contract I.calldata = some tagTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tagTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, tagSelectorBytes]
  native_decide

theorem endTagBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (tagStore I) tagTransition.body
      (.returned { contract := contract, locals := tagStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tagStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := tagStore I })
        (slot := tagRef (.var "arg0"))
        (er := ({ base := "tag", steps := [.mindex (tagArgKey I)] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (tagStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tagStorageSlot I)).toNat))
        (hbase := by simp [tagStore, tagRef])
        (her := by
          have hlen :
              (EVM.Word.toBytesBE (tagArgWord I)).length = bytes32Width.val + 1 := by
            simpa [bytes32Width] using word_toBytesBE_toByteArray_size (tagArgWord I)
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, tagRef, tagStore,
            tagArgValue, tagArgKey, bytes32Width, EvalResult.bind, EvalResult.ofOption, bind,
            pure, evalExpr?, valueToKey?, hlen])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, tagArgKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (tagStorageSlot I))])

set_option maxHeartbeats 5000000 in
theorem endReachTagBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 12)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1245⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xee6447b5⟩ :=
    endSelWord_eq_of_beq I hsz 0xee 0x64 0x47 0xb5 ⟨0xee6447b5⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot : UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 := RD.selectorSplitNotTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by simp)
  have h43gt : UInt256.gt (armSelNat endBytecode (⟨43⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h54 := RD.selectorSplitNotTakenAuto h43
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h43gt (by simp)
  have h54gt : UInt256.gt (armSelNat endBytecode (⟨54⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h65 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
      selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h54gt (by simp)
  have hcat0 : UInt256.eq (armSelNat endBytecode (⟨65⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hgap0 : UInt256.eq (armSelNat endBytecode (⟨76⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have htag :
      UInt256.eq (armSelNat endBytecode (⟨87⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h1245 := h65
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hcat0 (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hgap0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      htag (by jump_dest) (by simp)
  exact ⟨_, _, h1245⟩

theorem endTagX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tagWord σ I)) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (entry := ⟨1245⟩) (ret := ⟨509⟩) (decoded := ⟨1267⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (decoded := ⟨1267⟩) (ret := ⟨509⟩) (routine := ⟨9591⟩) (R := [sel])
    hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := ⟨9591⟩) (baseSlot := ⟨12⟩)
    (key := tagArgWord I) (ret := ⟨509⟩) (R := [sel]) hroutine
    (by unfold solcSingleMappingGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hslot : tagStorageSlot I = solcMappingSlot ⟨12⟩ (tagArgWord I) :=
    tagStorageSlot_eq I
  have hret :
      RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray (endSlotWord (tagStorageSlot I) σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨509⟩) (val := endSlotWord (solcMappingSlot ⟨12⟩ (tagArgWord I)) σ I)
      (ret := ⟨509⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨12⟩ (tagArgWord I))
        (endSlotWord (solcMappingSlot ⟨12⟩ (tagArgWord I)) σ I))
      (by simpa [endSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by exact solcMappingHashMem_mload64 ⟨12⟩ (tagArgWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64
          (endSlotWord (solcMappingSlot ⟨12⟩ (tagArgWord I)) σ I)
          (solcMappingHashMem_size ⟨12⟩ (tagArgWord I))
          (solcMappingHashMem_read64 ⟨12⟩ (tagArgWord I)))
      (by
        exact solcScratchReturnMem_read128
          (endSlotWord (solcMappingSlot ⟨12⟩ (tagArgWord I)) σ I)
          (solcMappingHashMem_size ⟨12⟩ (tagArgWord I)))
      (by simp only [List.length_singleton]; omega)
    simpa [endSlotWord, hslot] using hret'
  simpa [tagWord] using hret

theorem endTagX_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hltShort :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (show (⟨4⟩ : UInt256).toNat ≤ I.calldata.size by simpa using hsz4)
      hsize]
    simp only [show (⟨32⟩ : UInt256).toNat = 32 from rfl,
      show (⟨4⟩ : UInt256).toNat = 4 from rfl]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (entry := ⟨1245⟩) (ret := ⟨509⟩) (decoded := ⟨1267⟩) (need := ⟨32⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    hltShort

theorem endTagBodyCore : endBodyObligation 12 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 12) rfl hsel
  have hdispatch := endDispatchTagLocal hsel
  have hreach :=
    endReachTagBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hword : tagWord σ_evm I = tagWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (tagStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (tagStore I)
          tagTransition.body
          (.returned { contract := contract, locals := tagStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (tagWord σ_solm I).toNat))])) := by
      simpa [tagWord, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        endTagBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hret :=
      endTagX_ok (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    exact hret.reEquivExecutionTransport hcode hdispatch (endDecode_tag_ok hsz36) hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (tagWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endTagX_short (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_tag_none_short hsz4 hshort)

end Benchmarks.Dss.End
