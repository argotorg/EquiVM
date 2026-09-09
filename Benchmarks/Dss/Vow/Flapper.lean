import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flapper()` getter -/

def flapperWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowAddressReturnWord ⟨2⟩ σ I

theorem vowDispatch_flapper {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩) :
    dispatchMsg contract I.calldata = some flapperTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition])
    (post := [flogTransition, flopTransition, flopperTransition, healTransition, humpTransition,
      kissTransition, liveTransition, relyTransition, sinTransition, sumpTransition,
      vatTransition, waitTransition, wardsTransition])
    (ti := flapperTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, hcd]
      decide +native
  · rw [selectorOf, flapperSelectorBytes]
    exact hsel

theorem vowDecode_flapper {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flapperTransition.params.map Param.name)
      (transitionSignature flapperTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachFlapperBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨501⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨1554044707⟩ :=
    vowSelWord_eq_of_beq I hsz 0x5c 0xa0 0xd7 0x23 ⟨1554044707⟩
      (by decide +native) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc 1))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vowReachLowHighBody 1 (by omega) ⟨501⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by decide +native)

theorem vowFlapperBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapperTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapperTransition.params.map Param.name)
        (transitionSignature flapperTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨501⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ flapperTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (flapperWord σ_solm I).toNat))])) := by
    simpa [flapperTransition, flapperWord, vowAddressReturnWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      vowAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := flapperRef) (er := ({ base := "flapper", steps := [] } : EvaledStorageRef))
        (slot := ⟨2⟩)
        (by simp only [initState]; exact hwv) (by simp [flapperRef])
        (by simp [evalStorageRef, evalStorageRefSteps, flapperRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vowAddressGetterBodyCore (entry := ⟨501⟩) (routine := ⟨2273⟩) (slot := ⟨2⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcAddressSlotGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by rfl)
    (by simpa [flapperWord] using hbody)

theorem vowFlapperBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩ rfl hsel
  exact vowFlapperBodyCore hcode hwv (vowDispatch_flapper hsel) (vowDecode_flapper hsz)
    (vowReachFlapperBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Vow
