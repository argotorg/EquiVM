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

abbrev ArtArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev ArtArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (ArtArgWord I))

abbrev ArtArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (ArtArgWord I))

abbrev ArtStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (ArtArgValue I)

def ArtStorageSlot (I : ExecutionEnv) : UInt256 :=
  ArtSlot (ArtArgKey I)

def ArtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (ArtStorageSlot I) σ I

theorem ArtStorageSlot_eq (I : ExecutionEnv) :
    ArtStorageSlot I = solcMappingSlot ⟨14⟩ (ArtArgWord I) := by
  unfold ArtStorageSlot ArtSlot mapSlot solcMappingSlot ArtArgKey ArtArgWord
  unfold bytes32Width
  rw [keyValueToWord_fixedBytes32]

theorem endDecode_Art_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ArtTransition.params.map Param.name)
      (transitionSignature ArtTransition).paramTypes I.calldata = some (ArtStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata =
    some (ArtStore I)
  simpa [ArtStore, ArtArgValue, ArtArgWord] using
    endDecodeCalldata_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36

theorem endDecode_Art_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (ArtTransition.params.map Param.name)
      (transitionSignature ArtTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata = none
  simpa using endDecodeCalldata_legacyBytes32_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

theorem endDispatchArtLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 14)) :
    dispatchMsg contract I.calldata = some ArtTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ArtTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, ArtSelectorBytes]
  native_decide

theorem endArtBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (ArtStore I) ArtTransition.body
      (.returned { contract := contract, locals := ArtStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ArtStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := ArtStore I })
        (slot := ArtRef (.var "arg0"))
        (er := ({ base := "Art", steps := [.mindex (ArtArgKey I)] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (ArtStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ArtStorageSlot I)).toNat))
        (hbase := by simp [ArtStore, ArtRef])
        (her := by
          have hlen :
              (EVM.Word.toBytesBE (ArtArgWord I)).length = bytes32Width.val + 1 := by
            simpa [bytes32Width] using word_toBytesBE_toByteArray_size (ArtArgWord I)
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ArtRef, ArtStore,
            ArtArgValue, ArtArgKey, bytes32Width, EvalResult.bind, EvalResult.ofOption, bind,
            pure, evalExpr?, valueToKey?, hlen])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, ArtArgKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (ArtStorageSlot I))])

set_option maxHeartbeats 5000000 in
theorem endReachArtBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 14)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1142⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe1340a3d⟩ :=
    endSelWord_eq_of_beq I hsz 0xe1 0x34 0x0a 0x3d ⟨0xe1340a3d⟩
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
  have h54gt : UInt256.gt (armSelNat endBytecode (⟨54⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h113 := RD.selectorSplitTakenAuto h54
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h54gt (by jump_dest) (by simp)
  have h114 := h113.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have hfile0 :
      UInt256.eq (armSelNat endBytecode (⟨114⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hArt :
      UInt256.eq (armSelNat endBytecode (⟨125⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h1142 := h114
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hfile0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hArt (by jump_dest) (by simp)
  exact ⟨_, _, h1142⟩

theorem endArtX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1142⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (ArtWord σ I)) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (entry := ⟨1142⟩) (ret := ⟨509⟩) (decoded := ⟨1164⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneBytes32ExternalJump
    (decoded := ⟨1164⟩) (ret := ⟨509⟩) (routine := ⟨8814⟩) (R := [sel])
    hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := ⟨8814⟩) (baseSlot := ⟨14⟩)
    (key := ArtArgWord I) (ret := ⟨509⟩) (R := [sel]) hroutine
    (by unfold solcSingleMappingGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hslot : ArtStorageSlot I = solcMappingSlot ⟨14⟩ (ArtArgWord I) :=
    ArtStorageSlot_eq I
  have hret :
      RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray (endSlotWord (ArtStorageSlot I) σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨509⟩) (val := endSlotWord (solcMappingSlot ⟨14⟩ (ArtArgWord I)) σ I)
      (ret := ⟨509⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨14⟩ (ArtArgWord I))
        (endSlotWord (solcMappingSlot ⟨14⟩ (ArtArgWord I)) σ I))
      (by simpa [endSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by exact solcMappingHashMem_mload64 ⟨14⟩ (ArtArgWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64
          (endSlotWord (solcMappingSlot ⟨14⟩ (ArtArgWord I)) σ I)
          (solcMappingHashMem_size ⟨14⟩ (ArtArgWord I))
          (solcMappingHashMem_read64 ⟨14⟩ (ArtArgWord I)))
      (by
        exact solcScratchReturnMem_read128
          (endSlotWord (solcMappingSlot ⟨14⟩ (ArtArgWord I)) σ I)
          (solcMappingHashMem_size ⟨14⟩ (ArtArgWord I)))
      (by simp only [List.length_singleton]; omega)
    simpa [endSlotWord, hslot] using hret'
  simpa [ArtWord] using hret

theorem endArtX_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1142⟩ [sel]
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
    (entry := ⟨1142⟩) (ret := ⟨509⟩) (decoded := ⟨1164⟩) (need := ⟨32⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    hltShort

theorem endArtBodyCore : endBodyObligation 14 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 14) rfl hsel
  have hdispatch := endDispatchArtLocal hsel
  have hreach :=
    endReachArtBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hword : ArtWord σ_evm I = ArtWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (ArtStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (ArtStore I)
          ArtTransition.body
          (.returned { contract := contract, locals := ArtStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (ArtWord σ_solm I).toNat))])) := by
      simpa [ArtWord, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        endArtBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hret :=
      endArtX_ok (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    exact hret.reEquivExecutionTransport hcode hdispatch (endDecode_Art_ok hsz36) hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (ArtWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endArtX_short (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_Art_none_short hsz4 hshort)

end Benchmarks.Dss.End
