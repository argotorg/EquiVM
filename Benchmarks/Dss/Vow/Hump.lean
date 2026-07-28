import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `hump()` getter -/

def humpWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowSlotWord ⟨11⟩ σ I

theorem vowDispatch_hump {I : ExecutionEnv} (hsel : selIs I ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩) :
    dispatchMsg contract I.calldata = some humpTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition, healTransition])
    (post := [kissTransition, liveTransition, relyTransition, sinTransition, sumpTransition,
      vatTransition, waitTransition, wardsTransition])
    (ti := humpTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes, healSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, humpSelectorBytes]
    exact hsel

theorem vowDecode_hump {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (humpTransition.params.map Param.name)
      (transitionSignature humpTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachHumpBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨375⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨462327034⟩ :=
    vowSelWord_eq_of_beq I hsz 0x1b 0x8e 0x8c 0xfa ⟨462327034⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc 1))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowLowBody 1 (by omega) ⟨375⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem vowHumpBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some humpTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (humpTransition.params.map Param.name)
        (transitionSignature humpTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨375⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ humpTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (humpWord σ_solm I).toNat))])) := by
    simpa [humpTransition, humpWord, vowSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vowUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := humpRef) (er := ({ base := "hump", steps := [] } : EvaledStorageRef))
        (slot := ⟨11⟩)
        (by simp only [initState]; exact hwv) (by simp [humpRef])
        (by simp [evalStorageRef, evalStorageRefSteps, humpRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vowUint256GetterBodyCore (entry := ⟨375⟩) (routine := ⟨1543⟩) (slot := ⟨11⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl)
    (by simpa [humpWord] using hbody)

theorem vowHumpBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩ rfl hsel
  exact vowHumpBodyCore hcode hwv (vowDispatch_hump hsel) (vowDecode_hump hsz)
    (vowReachHumpBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Vow
