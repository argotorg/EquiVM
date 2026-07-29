import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `bump()` getter -/

def bumpWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowSlotWord ⟨10⟩ σ I

theorem vowDispatch_bump {I : ExecutionEnv} (hsel : selIs I ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩) :
    dispatchMsg contract I.calldata = some bumpTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition])
    (post := [cageTransition, denyTransition, dumpTransition, fessTransition,
      fileUintTransition, fileAddressTransition, flapTransition, flapperTransition,
      flogTransition, flopTransition, flopperTransition, healTransition, humpTransition,
      kissTransition, liveTransition, relyTransition, sinTransition, sumpTransition,
      vatTransition, waitTransition, wardsTransition])
    (ti := bumpTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x68, 0x11, 0x0b, 0x2f]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, bumpSelectorBytes]
    exact hsel

theorem vowDecode_bump {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (bumpTransition.params.map Param.name)
      (transitionSignature bumpTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachBumpBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨555⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨1745947439⟩ :=
    vowSelWord_eq_of_beq I hsz 0x68 0x11 0x0b 0x2f ⟨1745947439⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc 4))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowHighBody 4 (by omega) ⟨555⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem vowBumpBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some bumpTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (bumpTransition.params.map Param.name)
        (transitionSignature bumpTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨555⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ bumpTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (bumpWord σ_solm I).toNat))])) := by
    simpa [bumpTransition, bumpWord, vowSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vowUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := bumpRef) (er := ({ base := "bump", steps := [] } : EvaledStorageRef))
        (slot := ⟨10⟩)
        (by simp only [initState]; exact hwv) (by simp [bumpRef])
        (by simp [evalStorageRef, evalStorageRefSteps, bumpRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vowUint256GetterBodyCore (entry := ⟨555⟩) (routine := ⟨2482⟩) (slot := ⟨10⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl)
    (by simpa [bumpWord] using hbody)

theorem vowBumpBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩ rfl hsel
  exact vowBumpBodyCore hcode hwv (vowDispatch_bump hsel) (vowDecode_bump hsz)
    (vowReachBumpBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Vow
