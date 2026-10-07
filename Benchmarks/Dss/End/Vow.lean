import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `vow()` getter -/

def vowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcAddressSlotWord ⟨4⟩ σ I

theorem endDecode_vow {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
      (transitionSignature vowTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endVowConcreteSelector : ByteArray := selectorBytes 0x62 0x6c 0xb3 0xc5
abbrev endVowFirstArmPc : UInt256 := ⟨343⟩
abbrev endVowEntryPc : UInt256 := ⟨715⟩
abbrev endVowRoutinePc : UInt256 := ⟨5236⟩

set_option maxHeartbeats 1000000 in
theorem endVowArmsWellFormed :
    ∀ j, j ≤ 0 → armWellFormed endBytecode (nthArmPc endBytecode endVowFirstArmPc j) := by
  intro j hj
  interval_cases j
  dsimp [armWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endReachVowBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endVowConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState σ σ₀ g A I)
        endVowEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  have hword : endSelWord I = ⟨0x626cb3c5⟩ :=
    endSelWord_eq_of_beq I hsz 0x62 0x6c 0xb3 0xc5 ⟨0x626cb3c5⟩
      (by native_decide) (by simpa [selIs, endVowConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup343FirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endVowFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endVowFirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endVowEntryPc 0 hfirst
    (fun j hj => endVowArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endVowBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some vowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
        (transitionSignature vowTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨715⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (vowWord σ I).toNat))])) := by
    simpa [vowTransition, vowWord, solcAddressSlotWord, solcSlotWordAt, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [vowRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨715⟩) (returnPc := ⟨572⟩)
    (routine := ⟨5236⟩) (slot := ⟨4⟩)
    hcode hdispatch hdecode hreach
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
    (by rfl) (by simpa [vowWord] using hbody)

theorem endVowBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf vowTransition)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsel' : selIs I endVowConcreteSelector := by
    simpa [endVowSelectorBytes, endVowConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endVowConcreteSelector (by rfl) hsel'
  exact endVowBodyCore hcode hwv (endDispatchVow hsel) (endDecode_vow hsz)
    (endReachVowBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')

end Benchmarks.Dss.End
