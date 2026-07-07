import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flopper()` getter -/

def flopperWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowAddressReturnWord ⟨3⟩ σ I

theorem vowDispatch_flopper {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩) :
    dispatchMsg contract I.calldata = some flopperTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition])
    (post := [healTransition, humpTransition, kissTransition, liveTransition, relyTransition,
      sinTransition, sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := flopperTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x40, 0x81, 0xd7, 0x3a]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, flopSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, flopperSelectorBytes]
    exact hsel

theorem vowDecode_flopper {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flopperTransition.params.map Param.name)
      (transitionSignature flopperTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachFlopperBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨493⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨1082251066⟩ :=
    vowSelWord_eq_of_beq I hsz 0x40 0x81 0xd7 0x3a ⟨1082251066⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc 0))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowHighBody 0 (by omega) ⟨493⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem vowFlopperBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopperTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopperTransition.params.map Param.name)
        (transitionSignature flopperTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨493⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ flopperTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (flopperWord σ_solm I).toNat))])) := by
    simpa [flopperTransition, flopperWord, vowAddressReturnWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      vowAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := flopperRef) (er := ({ base := "flopper", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [flopperRef])
        (by simp [evalStorageRef, evalStorageRefSteps, flopperRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vowAddressGetterBodyCore (entry := ⟨493⟩) (routine := ⟨2258⟩) (slot := ⟨3⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcAddressSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl)
    (by simpa [flopperWord] using hbody)

theorem vowFlopperBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩ rfl hsel
  exact vowFlopperBodyCore hcode hwv (vowDispatch_flopper hsel) (vowDecode_flopper hsz)
    (vowReachFlopperBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Vow
