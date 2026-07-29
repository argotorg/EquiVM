import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `Ash()` getter -/

def ashWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowSlotWord ⟨6⟩ σ I

theorem vowDispatch_Ash {I : ExecutionEnv} (hsel : selIs I ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩) :
    dispatchMsg contract I.calldata = some AshTransition := by
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)]
  change dispatchList
    [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition,
      flapTransition, flapperTransition, flogTransition, flopTransition,
      flopperTransition, healTransition, humpTransition, kissTransition, liveTransition,
      relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition] I.calldata = some AshTransition
  rw [dispatchList_cons, selectorOf, AshSelectorBytes, if_pos hsel]

theorem vowDecode_Ash {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (AshTransition.params.map Param.name)
      (transitionSignature AshTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachAshBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨449⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨706554684⟩ :=
    vowSelWord_eq_of_beq I hsz 0x2a 0x1d 0x2b 0x3c ⟨706554684⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc 4))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowLowBody 4 (by omega) ⟨449⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem vowAshBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some AshTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (AshTransition.params.map Param.name)
        (transitionSignature AshTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨449⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ AshTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (ashWord σ_solm I).toNat))])) := by
    simpa [AshTransition, ashWord, vowSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vowUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := AshRef) (er := ({ base := "Ash", steps := [] } : EvaledStorageRef))
        (slot := ⟨6⟩)
        (by simp only [initState]; exact hwv) (by simp [AshRef])
        (by simp [evalStorageRef, evalStorageRefSteps, AshRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vowUint256GetterBodyCore (entry := ⟨449⟩) (routine := ⟨2237⟩) (slot := ⟨6⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl)
    (by simpa [ashWord] using hbody)

theorem vowAshBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩ rfl hsel
  exact vowAshBodyCore hcode hwv (vowDispatch_Ash hsel) (vowDecode_Ash hsz)
    (vowReachAshBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Vow
