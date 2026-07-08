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

/-! ## `pot()` getter -/

def potWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨5⟩ σ I

theorem endDecode_pot {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (potTransition.params.map Param.name)
      (transitionSignature potTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDispatchPotLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 5)) :
    dispatchMsg contract I.calldata = some potTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some potTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, potSelectorBytes]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachPotBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 5)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨664⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x4ba2363a⟩ :=
    endSelWord_eq_of_beq I hsz 0x4b 0xa2 0x36 0x3a ⟨0x4ba2363a⟩
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
      UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h391 := RD.selectorSplitTakenAuto h272
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h272gt (by jump_dest) (by simp)
  have h392 := h391.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h392gt :
      UInt256.gt (armSelNat endBytecode (⟨392⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h403 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h392
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h392gt (by simp)
  have h403eq0 :
      UInt256.eq (armSelNat endBytecode (⟨403⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h414take :
      UInt256.eq (armSelNat endBytecode (⟨414⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h664 := h403
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h403eq0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h414take (by jump_dest) (by simp)
  exact ⟨_, _, h664⟩

theorem endPotBodyCoreImpl
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some potTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (potTransition.params.map Param.name)
        (transitionSignature potTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨664⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ potTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (potWord σ_solm I).toNat))])) := by
    simpa [potTransition, potWord, endAddressReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := potRef) (er := ({ base := "pot", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [potRef])
        (by simp [evalStorageRef, evalStorageRefSteps, potRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨664⟩) (returnPc := ⟨572⟩)
    (routine := ⟨3209⟩) (slot := ⟨5⟩)
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
    (by rfl) (by simpa [potWord] using hbody)

theorem endPotBodyCore : endBodyObligation 5 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 5) rfl hsel
  exact endPotBodyCoreImpl hcode hwv (endDispatchPotLocal hsel) (endDecode_pot hsz)
    (endReachPotBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.End
