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

abbrev bagArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev bagArgMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (bagArgWord I)

abbrev bagArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (bagArgWord I).toNat)

abbrev bagArgKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (bagArgWord I).toNat)

abbrev bagStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (bagArgValue I)

def bagStorageSlot (I : ExecutionEnv) : UInt256 :=
  bagSlot (bagArgKey I)

def bagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (bagStorageSlot I) σ I

theorem bagStorageSlot_eq (I : ExecutionEnv) :
    bagStorageSlot I = solcMappingSlot ⟨16⟩ (bagArgMaskedWord I) := by
  unfold bagStorageSlot bagSlot mapSlot solcMappingSlot bagArgKey bagArgMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem endDecode_bag_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (bagTransition.params.map Param.name)
      (transitionSignature bagTransition).paramTypes I.calldata = some (bagStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [addr] I.calldata =
    some (bagStore I)
  simpa [bagStore, bagArgValue, bagArgWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36

theorem endDecode_bag_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (bagTransition.params.map Param.name)
      (transitionSignature bagTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

theorem endDispatchBagLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 16)) :
    dispatchMsg contract I.calldata = some bagTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some bagTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, bagSelectorBytes]
  native_decide

theorem endBagBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (bagStore I) bagTransition.body
      (.returned { contract := contract, locals := bagStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bagStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := bagStore I })
        (slot := bagRef (.var "arg0"))
        (er := ({ base := "bag", steps := [.mindex (bagArgKey I)] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (bagStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bagStorageSlot I)).toNat))
        (hbase := by simp [bagStore, bagRef])
        (her := by
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bagRef, bagStore,
            bagArgValue, bagArgKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind,
            pure, evalExpr?])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, bagArgKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (bagStorageSlot I))])

set_option maxHeartbeats 5000000 in
theorem endReachBagBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 16)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨895⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x9255f809⟩ :=
    endSelWord_eq_of_beq I hsz 0x92 0x55 0xf8 0x09 ⟨0x9255f809⟩
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
  have h163gt : UInt256.gt (armSelNat endBytecode (⟨163⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h222 := RD.selectorSplitTakenAuto h163
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h163gt (by jump_dest) (by simp)
  have h223 := h222.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h223eq0 : UInt256.eq (armSelNat endBytecode (⟨223⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h234take :
      UInt256.eq (armSelNat endBytecode (⟨234⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h895 := h223
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h223eq0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h234take (by jump_dest) (by simp)
  exact ⟨_, _, h895⟩

theorem endBagX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨895⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (bagWord σ I)) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (entry := ⟨895⟩) (ret := ⟨509⟩) (decoded := ⟨917⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (decoded := ⟨917⟩) (ret := ⟨509⟩) (routine := ⟨7476⟩) (R := [sel])
    hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := ⟨7476⟩) (baseSlot := ⟨16⟩)
    (key := bagArgMaskedWord I) (ret := ⟨509⟩) (R := [sel]) hroutine
    (by unfold solcSingleMappingGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hslot : bagStorageSlot I = solcMappingSlot ⟨16⟩ (bagArgMaskedWord I) :=
    bagStorageSlot_eq I
  have hret :
      RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray (endSlotWord (bagStorageSlot I) σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨509⟩) (val := endSlotWord (solcMappingSlot ⟨16⟩ (bagArgMaskedWord I)) σ I)
      (ret := ⟨509⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨16⟩ (bagArgMaskedWord I))
        (endSlotWord (solcMappingSlot ⟨16⟩ (bagArgMaskedWord I)) σ I))
      (by simpa [endSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by exact solcMappingHashMem_mload64 ⟨16⟩ (bagArgMaskedWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64
          (endSlotWord (solcMappingSlot ⟨16⟩ (bagArgMaskedWord I)) σ I)
          (solcMappingHashMem_size ⟨16⟩ (bagArgMaskedWord I))
          (solcMappingHashMem_read64 ⟨16⟩ (bagArgMaskedWord I)))
      (by
        exact solcScratchReturnMem_read128
          (endSlotWord (solcMappingSlot ⟨16⟩ (bagArgMaskedWord I)) σ I)
          (solcMappingHashMem_size ⟨16⟩ (bagArgMaskedWord I)))
      (by simp only [List.length_singleton]; omega)
    simpa [endSlotWord, hslot] using hret'
  simpa [bagWord] using hret

theorem endBagX_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨895⟩ [sel]
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
    (entry := ⟨895⟩) (ret := ⟨509⟩) (decoded := ⟨917⟩) (need := ⟨32⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    hltShort

theorem endBagBodyCore : endBodyObligation 16 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 16) rfl hsel
  have hdispatch := endDispatchBagLocal hsel
  have hreach :=
    endReachBagBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hword : bagWord σ_evm I = bagWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (bagStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (bagStore I)
          bagTransition.body
          (.returned { contract := contract, locals := bagStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (bagWord σ_solm I).toNat))])) := by
      simpa [bagWord, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        endBagBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hret :=
      endBagX_ok (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    exact hret.reEquivExecutionTransport hcode hdispatch (endDecode_bag_ok hsz36) hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (bagWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endBagX_short (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_bag_none_short hsz4 hshort)

end Benchmarks.Dss.End
