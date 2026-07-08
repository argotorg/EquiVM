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

/-! ## `vow()` getter -/

def vowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨4⟩ σ I

theorem endDecode_vow {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
      (transitionSignature vowTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDispatchVowLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 4)) :
    dispatchMsg contract I.calldata = some vowTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, vowSelectorBytes]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 4)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨715⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x626cb3c5⟩ :=
    endSelWord_eq_of_beq I hsz 0x62 0x6c 0xb3 0xc5 ⟨0x626cb3c5⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot :
      UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h271 := RD.selectorSplitTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by jump_dest) (by simp)
  have h272 := h271.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h272gt :
      UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h283 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h272gt (by simp)
  have h283gt :
      UInt256.gt (armSelNat endBytecode (⟨283⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h342 := RD.selectorSplitTakenAuto h283
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h283gt (by jump_dest) (by simp)
  have h343 := h342.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h343take :
      UInt256.eq (armSelNat endBytecode (⟨343⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h715 := h343.selectorArmTakenAuto
    (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
    h343take (by jump_dest) (by simp)
  exact ⟨_, _, h715⟩

theorem endVowBodyCoreImpl
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some vowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
        (transitionSignature vowTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨715⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (vowWord σ_solm I).toNat))])) := by
    simpa [vowTransition, vowWord, endAddressReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [vowRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨715⟩) (returnPc := ⟨572⟩)
    (routine := ⟨5236⟩) (slot := ⟨4⟩)
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
    (by rfl) (by simpa [vowWord] using hbody)

theorem endVowBodyCore : endBodyObligation 4 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 4) rfl hsel
  exact endVowBodyCoreImpl hcode hwv (endDispatchVowLocal hsel) (endDecode_vow hsz)
    (endReachVowBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.End
