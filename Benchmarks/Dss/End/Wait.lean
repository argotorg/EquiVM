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

def waitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨10⟩ σ I

theorem endDecode_wait {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (waitTransition.params.map Param.name)
      (transitionSignature waitTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDispatchWaitLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 10)) :
    dispatchMsg contract I.calldata = some waitTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some waitTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, waitSelectorBytes]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachWaitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 10)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨752⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x64bd7013⟩ :=
    endSelWord_eq_of_beq I hsz 0x64 0xbd 0x70 0x13 ⟨0x64bd7013⟩
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
  have h272gt : UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h283 := by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
      selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272
        (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
        h272gt (by simp)
  have h283gt : UInt256.gt (armSelNat endBytecode (⟨283⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h342 := RD.selectorSplitTakenAuto h283
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h283gt (by jump_dest) (by simp)
  have h343 := h342.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h343eq0 : UInt256.eq (armSelNat endBytecode (⟨343⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h354eq0 : UInt256.eq (armSelNat endBytecode (⟨354⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h365take : UInt256.eq (armSelNat endBytecode (⟨365⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h752 := h343
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h343eq0 (by simp)
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h354eq0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      h365take (by jump_dest) (by simp)
  exact ⟨_, _, h752⟩

theorem endWaitBodyCoreImpl
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some waitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (waitTransition.params.map Param.name)
        (transitionSignature waitTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ waitTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (waitWord σ_solm I).toNat))])) := by
    simpa [waitTransition, waitWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := waitRef) (er := ({ base := "wait", steps := [] } : EvaledStorageRef))
        (slot := ⟨10⟩)
        (by simp only [initState]; exact hwv) (by simp [waitRef])
        (by simp [evalStorageRef, evalStorageRefSteps, waitRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endUint256GetterBodyCore (entry := ⟨752⟩) (returnPc := ⟨509⟩)
    (routine := ⟨5269⟩) (slot := ⟨10⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [waitWord] using hbody)

theorem endWaitBodyCore : endBodyObligation 10 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 10) rfl hsel
  exact endWaitBodyCoreImpl hcode hwv (endDispatchWaitLocal hsel) (endDecode_wait hsz)
    (endReachWaitBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.End
