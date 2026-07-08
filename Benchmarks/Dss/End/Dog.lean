import Benchmarks.Dss.End.Trusted

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000

attribute [local simp]
  wardsSelectorBytes
  vatSelectorBytes
  catSelectorBytes
  dogSelectorBytes
  vowSelectorBytes
  potSelectorBytes
  spotSelectorBytes
  cureSelectorBytes
  liveSelectorBytes
  whenSelectorBytes
  waitSelectorBytes
  debtSelectorBytes
  tagSelectorBytes
  gapSelectorBytes
  ArtSelectorBytes
  fixSelectorBytes
  bagSelectorBytes
  outSelectorBytes
  relySelectorBytes
  denySelectorBytes
  fileAddressSelectorBytes
  fileUintSelectorBytes
  cageSelectorBytes
  cageIlkSelectorBytes
  snipSelectorBytes
  skipSelectorBytes
  skimSelectorBytes
  freeSelectorBytes
  thawSelectorBytes
  flowSelectorBytes
  packSelectorBytes
  cashSelectorBytes

/-! ## `dog()` getter -/

def dogWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨3⟩ σ I

theorem endDecode_dog {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dogTransition.params.map Param.name)
      (transitionSignature dogTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDispatchDogLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 3)) :
    dispatchMsg contract I.calldata = some dogTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dogTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, dogSelectorBytes]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachDogBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 3)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1017⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xc3b3ad7f⟩ :=
    endSelWord_eq_of_beq I hsz 0xc3 0xb3 0xad 0x7f ⟨0xc3b3ad7f⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := endBytecode)
      (bodyPc := (⟨18⟩ : UInt256)) (loadPc := (⟨26⟩ : UInt256))
      (firstPc := (⟨32⟩ : UInt256)) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := (⟨496⟩ : UInt256)) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hroot :
      UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h43 := RD.selectorSplitNotTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by simp)
  have h43gt :
      UInt256.gt (armSelNat endBytecode (⟨43⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h162 := RD.selectorSplitTakenAuto h43
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h43gt (by jump_dest) (by simp)
  have h163 := h162.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h163gt :
      UInt256.gt (armSelNat endBytecode (⟨163⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h174 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h163
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h163gt (by simp)
  have h174eq0 :
      UInt256.eq (armSelNat endBytecode (⟨174⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h185take :
      UInt256.eq (armSelNat endBytecode (⟨185⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h1017 := h174
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h174eq0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h185take (by jump_dest) (by simp)
  exact ⟨_, _, h1017⟩

theorem endDogBodyCoreImpl
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dogTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dogTransition.params.map Param.name)
        (transitionSignature dogTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1017⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ dogTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (dogWord σ_solm I).toNat))])) := by
    simpa [dogTransition, dogWord, endAddressReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := dogRef) (er := ({ base := "dog", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [dogRef])
        (by simp [evalStorageRef, evalStorageRefSteps, dogRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨1017⟩) (returnPc := ⟨572⟩)
    (routine := ⟨7675⟩) (slot := ⟨3⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcAddressSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [dogWord] using hbody)

theorem endDogBodyCore : endBodyObligation 3 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 3) rfl hsel
  exact endDogBodyCoreImpl hcode hwv (endDispatchDogLocal hsel) (endDecode_dog hsz)
    (endReachDogBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.End
