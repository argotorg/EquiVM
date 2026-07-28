import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `wait()` getter -/

def waitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowSlotWord ⟨7⟩ σ I

theorem vowDispatch_wait {I : ExecutionEnv} (hsel : selIs I ⟨#[0x64, 0xbd, 0x70, 0x13]⟩) :
    dispatchMsg contract I.calldata = some waitTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition, healTransition,
      humpTransition, kissTransition, liveTransition, relyTransition, sinTransition,
      sumpTransition, vatTransition])
    (post := [wardsTransition])
    (ti := waitTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x64, 0xbd, 0x70, 0x13]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes, healSelectorBytes,
        humpSelectorBytes, kissSelectorBytes, liveSelectorBytes, relySelectorBytes,
        sinSelectorBytes, sumpSelectorBytes, vatSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, waitSelectorBytes]
    exact hsel

theorem vowDecode_wait {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (waitTransition.params.map Param.name)
      (transitionSignature waitTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachWaitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x64, 0xbd, 0x70, 0x13]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨509⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨1690136595⟩ :=
    vowSelWord_eq_of_beq I hsz 0x64 0xbd 0x70 0x13 ⟨1690136595⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc 2))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowHighBody 2 (by omega) ⟨509⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem vowWaitBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some waitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (waitTransition.params.map Param.name)
        (transitionSignature waitTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨509⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ waitTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (waitWord σ_solm I).toNat))])) := by
    simpa [waitTransition, waitWord, vowSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vowUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := waitRef) (er := ({ base := "wait", steps := [] } : EvaledStorageRef))
        (slot := ⟨7⟩)
        (by simp only [initState]; exact hwv) (by simp [waitRef])
        (by simp [evalStorageRef, evalStorageRefSteps, waitRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vowUint256GetterBodyCore (entry := ⟨509⟩) (routine := ⟨2288⟩) (slot := ⟨7⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl)
    (by simpa [waitWord] using hbody)

theorem vowWaitBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x64, 0xbd, 0x70, 0x13]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ rfl hsel
  exact vowWaitBodyCore hcode hwv (vowDispatch_wait hsel) (vowDecode_wait hsz)
    (vowReachWaitBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Vow
