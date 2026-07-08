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

abbrev gapArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev gapArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (gapArgWord I))

abbrev gapArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (gapArgWord I))

abbrev gapStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (gapArgValue I)

def gapStorageSlot (I : ExecutionEnv) : UInt256 :=
  gapSlot (gapArgKey I)

def gapWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (gapStorageSlot I) σ I

theorem gapStorageSlot_eq (I : ExecutionEnv) :
    gapStorageSlot I = solcMappingSlot ⟨13⟩ (gapArgWord I) := by
  unfold gapStorageSlot gapSlot mapSlot solcMappingSlot gapArgKey gapArgWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

theorem endDecode_gap_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (gapTransition.params.map Param.name)
      (transitionSignature gapTransition).paramTypes I.calldata = some (gapStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata =
    some (gapStore I)
  simpa [gapStore, gapArgValue, gapArgWord] using
    endDecodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36

theorem endDecode_gap_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (gapTransition.params.map Param.name)
      (transitionSignature gapTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata = none
  simpa using endDecodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

theorem endDispatchGapLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 13)) :
    dispatchMsg contract I.calldata = some gapTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some gapTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, gapSelectorBytes]
  native_decide

theorem endGapBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (gapStore I) gapTransition.body
      (.returned { contract := contract, locals := gapStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (gapStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := gapStore I })
        (slot := gapRef (.var "arg0"))
        (er := ({ base := "gap", steps := [.mindex (gapArgKey I)] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (gapStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (gapStorageSlot I)).toNat))
        (hbase := by simp [gapStore, gapRef])
        (her := by
          have hlen :
              (EVM.Word.toBytesBE (gapArgWord I)).length = bytes32Width.val + 1 := by
            simpa [bytes32Width] using word_toBytesBE_toByteArray_size (gapArgWord I)
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, gapRef, gapStore,
            gapArgValue, gapArgKey, bytes32Width, EvalResult.bind, EvalResult.ofOption, bind,
            pure, evalExpr?, valueToKey?, hlen])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, gapArgKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (gapStorageSlot I))])

set_option maxHeartbeats 5000000 in
theorem endReachGapBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 13)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1216⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe6ee62aa⟩ :=
    endSelWord_eq_of_beq I hsz 0xe6 0xee 0x62 0xaa ⟨0xe6ee62aa⟩
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
  have hgap :
      UInt256.eq (armSelNat endBytecode (⟨76⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h1216 := h65
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hcat0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hgap (by jump_dest) (by simp)
  exact ⟨_, _, h1216⟩

theorem endGapX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (gapWord σ I)) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (entry := ⟨1216⟩) (ret := ⟨509⟩) (decoded := ⟨1238⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (decoded := ⟨1238⟩) (ret := ⟨509⟩) (routine := ⟨9573⟩) (R := [sel])
    hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := ⟨9573⟩) (baseSlot := ⟨13⟩)
    (key := gapArgWord I) (ret := ⟨509⟩) (R := [sel]) hroutine
    (by unfold solcSingleMappingGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hslot : gapStorageSlot I = solcMappingSlot ⟨13⟩ (gapArgWord I) :=
    gapStorageSlot_eq I
  have hret :
      RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray (endSlotWord (gapStorageSlot I) σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨509⟩) (val := endSlotWord (solcMappingSlot ⟨13⟩ (gapArgWord I)) σ I)
      (ret := ⟨509⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨13⟩ (gapArgWord I))
        (endSlotWord (solcMappingSlot ⟨13⟩ (gapArgWord I)) σ I))
      (by simpa [endSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by exact solcMappingHashMem_mload64 ⟨13⟩ (gapArgWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64
          (endSlotWord (solcMappingSlot ⟨13⟩ (gapArgWord I)) σ I)
          (solcMappingHashMem_size ⟨13⟩ (gapArgWord I))
          (solcMappingHashMem_read64 ⟨13⟩ (gapArgWord I)))
      (by
        exact solcScratchReturnMem_read128
          (endSlotWord (solcMappingSlot ⟨13⟩ (gapArgWord I)) σ I)
          (solcMappingHashMem_size ⟨13⟩ (gapArgWord I)))
      (by simp only [List.length_singleton]; omega)
    simpa [endSlotWord, hslot] using hret'
  simpa [gapWord] using hret

theorem endGapX_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩ [sel]
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
    (entry := ⟨1216⟩) (ret := ⟨509⟩) (decoded := ⟨1238⟩) (need := ⟨32⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    hltShort

theorem endGapBodyCore : endBodyObligation 13 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 13) rfl hsel
  have hdispatch := endDispatchGapLocal hsel
  have hreach :=
    endReachGapBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hword : gapWord σ_evm I = gapWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (gapStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (gapStore I)
          gapTransition.body
          (.returned { contract := contract, locals := gapStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (gapWord σ_solm I).toNat))])) := by
      simpa [gapWord, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        endGapBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hret :=
      endGapX_ok (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    exact hret.reEquivExecutionTransport hcode hdispatch (endDecode_gap_ok hsz36) hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (gapWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endGapX_short (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_gap_none_short hsz4 hshort)

end Benchmarks.Dss.End
