import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `spot()` getter -/

def spotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨6⟩ σ I

theorem endDecode_spot {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (spotTransition.params.map Param.name)
      (transitionSignature spotTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endSpotConcreteSelector : ByteArray := selectorBytes 0x6f 0x26 0x5b 0x93
abbrev endSpotHighSplitPc : UInt256 := ⟨283⟩
abbrev endSpotFirstArmPc : UInt256 := ⟨294⟩
abbrev endSpotEntryPc : UInt256 := ⟨835⟩
abbrev endSpotRoutinePc : UInt256 := ⟨6675⟩

theorem endSpotHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endSpotHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endSpotArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed endBytecode (nthArmPc endBytecode endSpotFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem endReachSpotBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endSpotConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endSpotEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x6f265b93⟩ :=
    endSelWord_eq_of_beq I hsz 0x6f 0x26 0x5b 0x93 ⟨0x6f265b93⟩
      (by native_decide) (by simpa [selIs, endSpotConcreteSelector, selectorBytes] using hsel)
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
      endSpotHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [endLow1SplitPc, endSpotHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272 endLow1SplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h294 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endSpotFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    simpa [endSpotHighSplitPc, endSpotFirstArmPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h283 endSpotHighSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endSpotFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endSpotFirstArmPc 2))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endSpotEntryPc 2 h294
    (fun j hj => endSpotArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endSpotBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some spotTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (spotTransition.params.map Param.name)
        (transitionSignature spotTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨835⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ spotTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (spotWord σ_solm I).toNat))])) := by
    simpa [spotTransition, spotWord, endAddressReturnWord, endSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := spotRef) (er := ({ base := "spot", steps := [] } : EvaledStorageRef))
        (slot := ⟨6⟩)
        (by simp only [initState]; exact hwv) (by simp [spotRef])
        (by simp [evalStorageRef, evalStorageRefSteps, spotRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨835⟩) (returnPc := ⟨572⟩)
    (routine := ⟨6675⟩) (slot := ⟨6⟩)
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
    (by rfl) (by simpa [spotWord] using hbody)

theorem endSpotBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf spotTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endSpotConcreteSelector := by
    simpa [endSpotSelectorBytes, endSpotConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endSpotConcreteSelector (by rfl) hsel'
  exact endSpotBodyCore hcode hwv (endDispatchSpot hsel) (endDecode_spot hsz)
    (endReachSpotBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')
    hAccounts

end Benchmarks.Dss.End
