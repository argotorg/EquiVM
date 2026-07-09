import Benchmarks.Dss.StairstepExponentialDecrease.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.StairstepExponentialDecrease

/-! ## `step()` getter -/

def stepWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  stairstepSlotWord ⟨1⟩ σ I

theorem stairstepDecode_step {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (stepTransition.params.map Param.name)
      (transitionSignature stepTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem stairstepReachStepBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (stairstepSelBytes 5)) :
    ∃ k C, RD stairstepExponentialDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        stairstepStepEntryPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : stairstepSelWord I = ⟨0xe25fe175⟩ :=
    stairstepSelWord_eq_of_beq I hsz 0xe2 0x5f 0xe1 0x75 ⟨0xe25fe175⟩
      (by native_decide) (by simpa [stairstepSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat stairstepExponentialDecreaseBytecode stairstepRootSplitPc)
        (stairstepSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat stairstepExponentialDecreaseBytecode
          (nthArmPc stairstepExponentialDecreaseBytecode stairstepHighFirstArmPc 2))
        (stairstepSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact stairstepReachHighBody 2 (by omega) stairstepStepEntryPc hcode hwv hsz hsize
    hroot heq0 htake (by jump_dest) (by native_decide)

theorem stairstepStepBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some stepTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (stepTransition.params.map Param.name)
        (transitionSignature stepTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD stairstepExponentialDecreaseBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) stairstepStepEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ stepTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (stepWord σ_solm I).toNat))])) := by
    simpa [stepTransition, stepWord, stairstepSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      stairstepUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := stepRef) (er := ({ base := "step", steps := [] } : EvaledStorageRef))
        (slot := ⟨1⟩)
        (by simp only [initState]; exact hwv) (by simp [stepRef])
        (by simp [evalStorageRef, evalStorageRefSteps, stepRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact stairstepUint256GetterBodyCore (entry := stairstepStepEntryPc)
    (returnPc := ⟨202⟩) (routine := ⟨1030⟩) (slot := ⟨1⟩)
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
    (by rfl) (by simpa [stepWord] using hbody)

theorem stairstepStepBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stairstepExponentialDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (stairstepSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (stairstepSelBytes 5) rfl hsel
  exact stairstepStepBodyCore hcode hwv (stairstepDispatchStep hsel) (stairstepDecode_step hsz)
    (stairstepReachStepBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end Benchmarks.Dss.StairstepExponentialDecrease
