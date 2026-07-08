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

abbrev fixArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fixArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (fixArgWord I))

abbrev fixArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (fixArgWord I))

abbrev fixStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (fixArgValue I)

def fixStorageSlot (I : ExecutionEnv) : UInt256 :=
  fixSlot (fixArgKey I)

def fixWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (fixStorageSlot I) σ I

theorem fixStorageSlot_eq (I : ExecutionEnv) :
    fixStorageSlot I = solcMappingSlot ⟨15⟩ (fixArgWord I) := by
  unfold fixStorageSlot fixSlot mapSlot solcMappingSlot fixArgKey fixArgWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

theorem endDecode_fix_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fixTransition.params.map Param.name)
      (transitionSignature fixTransition).paramTypes I.calldata = some (fixStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata =
    some (fixStore I)
  simpa [fixStore, fixArgValue, fixArgWord] using
    endDecodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36

theorem endDecode_fix_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (fixTransition.params.map Param.name)
      (transitionSignature fixTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata = none
  simpa using endDecodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

theorem endDispatchFixLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 15)) :
    dispatchMsg contract I.calldata = some fixTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fixTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, fixSelectorBytes]
  native_decide

theorem endFixBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (fixStore I) fixTransition.body
      (.returned { contract := contract, locals := fixStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fixStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := fixStore I })
        (slot := fixRef (.var "arg0"))
        (er := ({ base := "fix", steps := [.mindex (fixArgKey I)] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (fixStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fixStorageSlot I)).toNat))
        (hbase := by simp [fixStore, fixRef])
        (her := by
          have hlen :
              (EVM.Word.toBytesBE (fixArgWord I)).length = bytes32Width.val + 1 := by
            simpa [bytes32Width] using word_toBytesBE_toByteArray_size (fixArgWord I)
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, fixRef, fixStore,
            fixArgValue, fixArgKey, bytes32Width, EvalResult.bind, EvalResult.ofOption, bind,
            pure, evalExpr?, valueToKey?, hlen])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, fixArgKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (fixStorageSlot I))])

set_option maxHeartbeats 5000000 in
theorem endReachFixBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 15)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨723⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x63fad85e⟩ :=
    endSelWord_eq_of_beq I hsz 0x63 0xfa 0xd8 0x5e ⟨0x63fad85e⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot : UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h271 := RD.selectorSplitTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by jump_dest) (by simp)
  have h272 := h271.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h272gt :
      UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h283 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
      selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h272gt (by simp)
  have h283gt :
      UInt256.gt (armSelNat endBytecode (⟨283⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h342 := RD.selectorSplitTakenAuto h283
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h283gt (by jump_dest) (by simp)
  have h343 := h342.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have hvow0 :
      UInt256.eq (armSelNat endBytecode (⟨343⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hfix :
      UInt256.eq (armSelNat endBytecode (⟨354⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h723 := h343
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hvow0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hfix (by jump_dest) (by simp)
  exact ⟨_, _, h723⟩

theorem endFixX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨723⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (fixWord σ I)) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (entry := ⟨723⟩) (ret := ⟨509⟩) (decoded := ⟨745⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (decoded := ⟨745⟩) (ret := ⟨509⟩) (routine := ⟨5251⟩) (R := [sel])
    hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := ⟨5251⟩) (baseSlot := ⟨15⟩)
    (key := fixArgWord I) (ret := ⟨509⟩) (R := [sel]) hroutine
    (by unfold solcSingleMappingGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hslot : fixStorageSlot I = solcMappingSlot ⟨15⟩ (fixArgWord I) :=
    fixStorageSlot_eq I
  have hret :
      RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray (endSlotWord (fixStorageSlot I) σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨509⟩) (val := endSlotWord (solcMappingSlot ⟨15⟩ (fixArgWord I)) σ I)
      (ret := ⟨509⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨15⟩ (fixArgWord I))
        (endSlotWord (solcMappingSlot ⟨15⟩ (fixArgWord I)) σ I))
      (by simpa [endSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by exact solcMappingHashMem_mload64 ⟨15⟩ (fixArgWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64
          (endSlotWord (solcMappingSlot ⟨15⟩ (fixArgWord I)) σ I)
          (solcMappingHashMem_size ⟨15⟩ (fixArgWord I))
          (solcMappingHashMem_read64 ⟨15⟩ (fixArgWord I)))
      (by
        exact solcScratchReturnMem_read128
          (endSlotWord (solcMappingSlot ⟨15⟩ (fixArgWord I)) σ I)
          (solcMappingHashMem_size ⟨15⟩ (fixArgWord I)))
      (by simp only [List.length_singleton]; omega)
    simpa [endSlotWord, hslot] using hret'
  simpa [fixWord] using hret

theorem endFixX_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨723⟩ [sel]
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
    (entry := ⟨723⟩) (ret := ⟨509⟩) (decoded := ⟨745⟩) (need := ⟨32⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    hltShort

theorem endFixBodyCore : endBodyObligation 15 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 15) rfl hsel
  have hdispatch := endDispatchFixLocal hsel
  have hreach :=
    endReachFixBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hword : fixWord σ_evm I = fixWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (fixStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (fixStore I)
          fixTransition.body
          (.returned { contract := contract, locals := fixStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (fixWord σ_solm I).toNat))])) := by
      simpa [fixWord, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        endFixBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hret :=
      endFixX_ok (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    exact hret.reEquivExecutionTransport hcode hdispatch (endDecode_fix_ok hsz36) hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (fixWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endFixX_short (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_fix_none_short hsz4 hshort)

end Benchmarks.Dss.End
