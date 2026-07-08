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

abbrev wardsArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev wardsArgMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (wardsArgWord I)

abbrev wardsArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (wardsArgWord I).toNat)

abbrev wardsArgKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (wardsArgWord I).toNat)

abbrev wardsStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (wardsArgValue I)

def wardsStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (wardsArgKey I)

def wardsWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (wardsStorageSlot I) σ I

theorem wardsStorageSlot_eq (I : ExecutionEnv) :
    wardsStorageSlot I = solcMappingSlot ⟨0⟩ (wardsArgMaskedWord I) := by
  unfold wardsStorageSlot wardsSlot mapSlot solcMappingSlot wardsArgKey wardsArgMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem endDecode_wards_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = some (wardsStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [addr] I.calldata =
    some (wardsStore I)
  simpa [wardsStore, wardsArgValue, wardsArgWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36

theorem endDecode_wards_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

theorem endDispatchWardsLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 0)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, wardsSelectorBytes]
  native_decide

theorem endWardsBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (wardsStore I) wardsTransition.body
      (.returned { contract := contract, locals := wardsStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (wardsStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := wardsStore I })
        (slot := wardsRef (.var "arg0"))
        (er := ({ base := "wards", steps := [.mindex (wardsArgKey I)] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (wardsStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (wardsStorageSlot I)).toNat))
        (hbase := by simp [wardsStore, wardsRef])
        (her := by
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, wardsRef, wardsStore,
            wardsArgValue, wardsArgKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind,
            pure, evalExpr?])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, wardsArgKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (wardsStorageSlot I))])

set_option maxHeartbeats 5000000 in
theorem endReachWardsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 0)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨979⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xbf353dbb⟩ :=
    endSelWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb ⟨0xbf353dbb⟩
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
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h163
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h163gt (by simp)
  have h174take :
      UInt256.eq (armSelNat endBytecode (⟨174⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h979 := h174.selectorArmTakenAuto
    (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
    h174take (by jump_dest) (by simp)
  exact ⟨_, _, h979⟩

@[reducible] def endZeroSlotSingleMappingGetterWf (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode endBytecode pc = some (.JUMPDEST, .none)
  ∧ decode endBytecode p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode endBytecode p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode endBytecode p5 = some (.DUP2, .none)
  ∧ decode endBytecode p6 = some (.SWAP1, .none)
  ∧ decode endBytecode p7 = some (.MSTORE, .none)
  ∧ decode endBytecode p8 = some (.SWAP1, .none)
  ∧ decode endBytecode p9 = some (.DUP2, .none)
  ∧ decode endBytecode p10 = some (.MSTORE, .none)
  ∧ decode endBytecode p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode endBytecode p13 = some (.SWAP1, .none)
  ∧ decode endBytecode p14 = some (.KECCAK256, .none)
  ∧ decode endBytecode p15 = some (.SLOAD, .none)
  ∧ decode endBytecode p16 = some (.DUP2, .none)
  ∧ decode endBytecode p17 = some (.JUMP, .none)

theorem RD.endZeroSlotSingleMappingGetter {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : endZeroSlotSingleMappingGetterWf pc)
    (hret : (D_J endBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by simp only [List.length_cons]; omega)
  have rd7 := rd6.swap1 hd6 (by simp only [List.length_cons]; omega)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  exact ⟨_, _, rd17.jump hd17 hret (by evm_ov)⟩

theorem endWardsX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (wardsWord σ I)) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (entry := ⟨979⟩) (ret := ⟨509⟩) (decoded := ⟨1001⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (decoded := ⟨1001⟩) (ret := ⟨509⟩) (routine := ⟨7657⟩) (R := [sel])
    hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, hretPc⟩ := RD.endZeroSlotSingleMappingGetter
    (pc := ⟨7657⟩) (key := wardsArgMaskedWord I) (ret := ⟨509⟩) (R := [sel])
    hroutine
    (by unfold endZeroSlotSingleMappingGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hslot : wardsStorageSlot I = solcMappingSlot ⟨0⟩ (wardsArgMaskedWord I) :=
    wardsStorageSlot_eq I
  have hret :
      RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray (endSlotWord (wardsStorageSlot I) σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨509⟩) (val := endSlotWord (solcMappingSlot ⟨0⟩ (wardsArgMaskedWord I)) σ I)
      (ret := ⟨509⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨0⟩ (wardsArgMaskedWord I))
        (endSlotWord (solcMappingSlot ⟨0⟩ (wardsArgMaskedWord I)) σ I))
      (by simpa [endSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by exact solcMappingHashMem_mload64 ⟨0⟩ (wardsArgMaskedWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64
          (endSlotWord (solcMappingSlot ⟨0⟩ (wardsArgMaskedWord I)) σ I)
          (solcMappingHashMem_size ⟨0⟩ (wardsArgMaskedWord I))
          (solcMappingHashMem_read64 ⟨0⟩ (wardsArgMaskedWord I)))
      (by
        exact solcScratchReturnMem_read128
          (endSlotWord (solcMappingSlot ⟨0⟩ (wardsArgMaskedWord I)) σ I)
          (solcMappingHashMem_size ⟨0⟩ (wardsArgMaskedWord I)))
      (by simp only [List.length_singleton]; omega)
    simpa [endSlotWord, hslot] using hret'
  simpa [wardsWord] using hret

theorem endWardsX_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨979⟩ [sel]
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
    (entry := ⟨979⟩) (ret := ⟨509⟩) (decoded := ⟨1001⟩) (need := ⟨32⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    hltShort

theorem endWardsBodyCore : endBodyObligation 0 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 0) rfl hsel
  have hdispatch := endDispatchWardsLocal hsel
  have hreach :=
    endReachWardsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hword : wardsWord σ_evm I = wardsWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (wardsStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (wardsStore I)
          wardsTransition.body
          (.returned { contract := contract, locals := wardsStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (wardsWord σ_solm I).toNat))])) := by
      simpa [wardsWord, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        endWardsBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    have hret :=
      endWardsX_ok (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    exact hret.reEquivExecutionTransport hcode hdispatch (endDecode_wards_ok hsz36) hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (wardsWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hrev :=
      endWardsX_short (σ := σ_evm) (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch (endDecode_wards_none_short hsz4 hshort)

end Benchmarks.Dss.End
