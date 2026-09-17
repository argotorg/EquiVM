import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `dog()` getter -/

def dogWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨3⟩ σ I

theorem endDecode_dog {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dogTransition.params.map Param.name)
      (transitionSignature dogTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endDogConcreteSelector : ByteArray := selectorBytes 0xc3 0xb3 0xad 0x7f
abbrev endDogFirstArmPc : UInt256 := ⟨174⟩
abbrev endDogEntryPc : UInt256 := ⟨1017⟩
abbrev endDogRoutinePc : UInt256 := ⟨7675⟩

set_option maxHeartbeats 1000000 in
theorem endDogArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endDogFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem endReachDogBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endDogConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endDogEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xc3b3ad7f⟩ :=
    endSelWord_eq_of_beq I hsz 0xc3 0xb3 0xad 0x7f ⟨0xc3b3ad7f⟩
      (by native_decide) (by simpa [selIs, endDogConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup174FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDogFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDogFirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endDogEntryPc 1 hfirst
    (fun j hj => endDogArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endDogBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dogTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dogTransition.params.map Param.name)
        (transitionSignature dogTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1017⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ dogTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (dogWord σ_solm I).toNat))])) := by
    simpa [dogTransition, dogWord, endAddressReturnWord, endSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := dogRef) (er := ({ base := "dog", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [dogRef])
        (by simp [evalStorageRef, evalStorageRefSteps, dogRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨1017⟩) (returnPc := ⟨572⟩)
    (routine := ⟨7675⟩) (slot := ⟨3⟩)
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
    (by rfl) (by simpa [dogWord] using hbody)

theorem endDogBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf dogTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endDogConcreteSelector := by
    simpa [endDogSelectorBytes, endDogConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endDogConcreteSelector (by rfl) hsel'
  exact endDogBodyCore hcode hwv (endDispatchDog hsel) (endDecode_dog hsz)
    (endReachDogBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')
    hAccounts

end Benchmarks.Dss.End
