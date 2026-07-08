import Benchmarks.Dss.ExponentialDecrease.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.ExponentialDecrease

/-! ## `cut()` getter -/

def cutWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  stairstepSlotWord ⟨1⟩ σ I

theorem stairstepDecode_cut {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cutTransition.params.map Param.name)
      (transitionSignature cutTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stairstepReachCutBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = exponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (stairstepSelBytes 0)) :
    ∃ k C, RD exponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        stairstepCutEntryPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : stairstepSelWord I = ⟨0xe6fd604c⟩ :=
    stairstepSelWord_eq_of_beq I hsz 0xe6 0xfd 0x60 0x4c ⟨0xe6fd604c⟩
      (by native_decide) (by simpa [stairstepSelBytes] using hsel)
  have heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat exponentialDecreaseBytecode
          (nthArmPc exponentialDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat exponentialDecreaseBytecode
          (nthArmPc exponentialDecreaseBytecode stairstepFirstArmPc 5))
        (stairstepSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact stairstepReachBody 5 (by omega) stairstepCutEntryPc hcode hwv hsz hsize
    heq0 htake (by jump_dest) (by native_decide)

theorem stairstepCutBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = exponentialDecreaseBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cutTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cutTransition.params.map Param.name)
        (transitionSignature cutTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD exponentialDecreaseBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) stairstepCutEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ cutTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (cutWord σ_solm I).toNat))])) := by
    simpa [cutTransition, cutWord, stairstepSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      stairstepUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := cutRef) (er := ({ base := "cut", steps := [] } : EvaledStorageRef))
        (slot := ⟨1⟩)
        (by simp only [initState]; exact hwv) (by simp [cutRef])
        (by simp [evalStorageRef, evalStorageRefSteps, cutRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact stairstepUint256GetterBodyCore (entry := stairstepCutEntryPc)
    (returnPc := ⟨175⟩) (routine := ⟨981⟩) (slot := ⟨1⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [cutWord] using hbody)

theorem stairstepCutBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = exponentialDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (stairstepSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (stairstepSelBytes 0) rfl hsel
  exact stairstepCutBodyCore hcode hwv (stairstepDispatchCut hsel) (stairstepDecode_cut hsz)
    (stairstepReachCutBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end Benchmarks.Dss.ExponentialDecrease
