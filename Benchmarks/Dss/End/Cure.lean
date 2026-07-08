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

/-! ## `cure()` getter -/

def cureWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨7⟩ σ I

theorem endDecode_cure {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cureTransition.params.map Param.name)
      (transitionSignature cureTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDispatchCureLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 7)) :
    dispatchMsg contract I.calldata = some cureTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cureTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelectorBytes]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachCureBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 7)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨843⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x840782ed⟩ :=
    endSelWord_eq_of_beq I hsz 0x84 0x07 0x82 0xed ⟨0x840782ed⟩
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
      UInt256.gt (armSelNat endBytecode (⟨283⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h294 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h283
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h283gt (by simp)
  have h294eq0 :
      UInt256.eq (armSelNat endBytecode (⟨294⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h305eq0 :
      UInt256.eq (armSelNat endBytecode (⟨305⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h316eq0 :
      UInt256.eq (armSelNat endBytecode (⟨316⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h327take :
      UInt256.eq (armSelNat endBytecode (⟨327⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h843 := h294
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h294eq0 (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h305eq0 (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h316eq0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h327take (by jump_dest) (by simp)
  exact ⟨_, _, h843⟩

theorem endCureBodyCoreImpl
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cureTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cureTransition.params.map Param.name)
        (transitionSignature cureTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨843⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ cureTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (cureWord σ_solm I).toNat))])) := by
    simpa [cureTransition, cureWord, endAddressReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := cureRef) (er := ({ base := "cure", steps := [] } : EvaledStorageRef))
        (slot := ⟨7⟩)
        (by simp only [initState]; exact hwv) (by simp [cureRef])
        (by simp [evalStorageRef, evalStorageRefSteps, cureRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨843⟩) (returnPc := ⟨572⟩)
    (routine := ⟨6690⟩) (slot := ⟨7⟩)
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
    (by rfl) (by simpa [cureWord] using hbody)

theorem endCureBodyCore : endBodyObligation 7 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 7) rfl hsel
  exact endCureBodyCoreImpl hcode hwv (endDispatchCureLocal hsel) (endDecode_cure hsz)
    (endReachCureBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.End
