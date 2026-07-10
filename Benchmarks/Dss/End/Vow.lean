import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `vow()` getter -/

def vowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨4⟩ σ I

theorem endDecode_vow {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
      (transitionSignature vowTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endVowConcreteSelector : ByteArray := selectorBytes 0x62 0x6c 0xb3 0xc5
abbrev endVowHighSplitPc : UInt256 := ⟨283⟩
abbrev endVowGroupJumpdestPc : UInt256 := ⟨342⟩
abbrev endVowFirstArmPc : UInt256 := ⟨343⟩
abbrev endVowEntryPc : UInt256 := ⟨715⟩
abbrev endVowRoutinePc : UInt256 := ⟨5236⟩

theorem endVowHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endVowHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endVowArmsWellFormed :
    ∀ j, j ≤ 0 → armWellFormed endBytecode (nthArmPc endBytecode endVowFirstArmPc j) := by
  intro j hj
  interval_cases j
  dsimp [armWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endReachVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endVowConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endVowEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x626cb3c5⟩ :=
    endSelWord_eq_of_beq I hsz 0x62 0x6c 0xb3 0xc5 ⟨0x626cb3c5⟩
      (by native_decide) (by simpa [selIs, endVowConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endLow1JumpdestPc] using
      RD.selectorSplitTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by native_decide) (by simp)
  have h283 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endVowHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [endLow1SplitPc, endVowHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272 endLow1SplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h342 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endVowGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    simpa [endVowHighSplitPc, endVowGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h283 endVowHighSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h343 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endVowFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5 + 1)
        (C32 + 22 + 1 + 22 + 22 + 1) := by
    simpa [endVowFirstArmPc] using h342.jumpdest (by native_decide) (by simp)
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
  exact RD.dispatchTo endVowEntryPc 0 h343
    (fun j hj => endVowArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endVowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some vowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
        (transitionSignature vowTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨715⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (vowWord σ_solm I).toNat))])) := by
    simpa [vowTransition, vowWord, endAddressReturnWord, endSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [vowRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨715⟩) (returnPc := ⟨572⟩)
    (routine := ⟨5236⟩) (slot := ⟨4⟩)
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
    (by rfl) (by simpa [vowWord] using hbody)

theorem endVowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf vowTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endVowConcreteSelector := by
    simpa [endVowSelectorBytes, endVowConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endVowConcreteSelector (by rfl) hsel'
  exact endVowBodyCore hcode hwv (endDispatchVow hsel) (endDecode_vow hsz)
    (endReachVowBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')
    hAccounts

end Benchmarks.Dss.End
