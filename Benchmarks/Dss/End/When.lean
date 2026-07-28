import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `when()` getter -/

def whenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨9⟩ σ I

theorem endDecode_when {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (whenTransition.params.map Param.name)
      (transitionSignature whenTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endWhenConcreteSelector : ByteArray := selectorBytes 0xe2 0xb0 0xca 0xef

abbrev endWhenHighSplitPc : UInt256 := ⟨43⟩
abbrev endWhenHigh2SplitPc : UInt256 := ⟨54⟩
abbrev endWhenGroupJumpdestPc : UInt256 := ⟨113⟩
abbrev endWhenFirstArmPc : UInt256 := ⟨114⟩
abbrev endWhenEntryPc : UInt256 := ⟨1200⟩
abbrev endWhenRoutinePc : UInt256 := ⟨9552⟩

theorem endWhenHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endWhenHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endWhenHigh2SplitWellFormed :
    selectorSplitWellFormed endBytecode endWhenHigh2SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endWhenArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endWhenFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem endReachWhenBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endWhenConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endWhenEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe2b0caef⟩ :=
    endSelWord_eq_of_beq I hsz 0xe2 0xb0 0xca 0xef ⟨0xe2b0caef⟩
      (by native_decide) (by simpa [selIs, endWhenConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endWhenHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endWhenHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h54 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endWhenHigh2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endWhenHighSplitPc, endWhenHigh2SplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 endWhenHighSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h113 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endWhenGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    simpa [endWhenHigh2SplitPc, endWhenGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h54 endWhenHigh2SplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h114 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endWhenFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5 + 1) (C32 + 22 + 22 + 22 + 1) := by
    simpa [endWhenFirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endWhenFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endWhenFirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endWhenEntryPc 3 h114
    (fun j hj => endWhenArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endWhenBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some whenTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (whenTransition.params.map Param.name)
        (transitionSignature whenTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endWhenEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ whenTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (whenWord σ_solm I).toNat))])) := by
    simpa [whenTransition, whenWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := whenRef) (er := ({ base := "when", steps := [] } : EvaledStorageRef))
        (slot := ⟨9⟩)
        (by simp only [initState]; exact hwv) (by simp [whenRef])
        (by simp [evalStorageRef, evalStorageRefSteps, whenRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endUint256GetterBodyCore (entry := endWhenEntryPc)
    (returnPc := endWordReturnPc) (routine := endWhenRoutinePc) (slot := ⟨9⟩)
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
    (by rfl) (by simpa [whenWord] using hbody)

theorem endWhenBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf whenTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endWhenConcreteSelector := by
    simpa [endWhenSelectorBytes, endWhenConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endWhenConcreteSelector (by rfl) hsel'
  exact endWhenBodyCore hcode hwv (endDispatchWhen hsel) (endDecode_when hsz)
    (endReachWhenBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')
    hAccounts

end Benchmarks.Dss.End
