import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `cat()` getter -/

def catWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨2⟩ σ I

theorem endDecode_cat {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (catTransition.params.map Param.name)
      (transitionSignature catTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endCatConcreteSelector : ByteArray := selectorBytes 0xe4 0x88 0x18 0x13
abbrev endCatHighSplitPc : UInt256 := ⟨43⟩
abbrev endCatHigh2SplitPc : UInt256 := ⟨54⟩
abbrev endCatFirstArmPc : UInt256 := ⟨65⟩
abbrev endCatEntryPc : UInt256 := ⟨1208⟩
abbrev endCatRoutinePc : UInt256 := ⟨9558⟩

theorem endCatHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endCatHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

theorem endCatHigh2SplitWellFormed :
    selectorSplitWellFormed endBytecode endCatHigh2SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

set_option maxHeartbeats 1000000 in
theorem endCatArmsWellFormed :
    ∀ j, j ≤ 0 → armWellFormed endBytecode (nthArmPc endBytecode endCatFirstArmPc j) := by
  intro j hj
  interval_cases j
  dsimp [armWellFormed]
  repeat' first | apply And.intro | decide +native

theorem endReachCatBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endCatConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endCatEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe4881813⟩ :=
    endSelWord_eq_of_beq I hsz 0xe4 0x88 0x18 0x13 ⟨0xe4881813⟩
      (by decide +native) (by simpa [selIs, endCatConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endCatHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endCatHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; decide +native) (by simp)
  have h54 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endCatHigh2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endCatHighSplitPc, endCatHigh2SplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 endCatHighSplitWellFormed
        (by rw [hword]; decide +native) (by simp)
  have h65 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endCatFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    simpa [endCatHigh2SplitPc, endCatFirstArmPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54 endCatHigh2SplitWellFormed
        (by rw [hword]; decide +native) (by simp)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endCatFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endCatFirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo endCatEntryPc 0 h65
    (fun j hj => endCatArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem endCatBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some catTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (catTransition.params.map Param.name)
        (transitionSignature catTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1208⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ catTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (catWord σ_solm I).toNat))])) := by
    simpa [catTransition, catWord, endAddressReturnWord, endSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := catRef) (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
        (slot := ⟨2⟩)
        (by simp only [initState]; exact hwv) (by simp [catRef])
        (by simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨1208⟩) (returnPc := ⟨572⟩)
    (routine := ⟨9558⟩) (slot := ⟨2⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcAddressSlotGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | decide +native)
    (by rfl) (by simpa [catWord] using hbody)

theorem endCatBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf catTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endCatConcreteSelector := by
    simpa [endCatSelectorBytes, endCatConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endCatConcreteSelector (by rfl) hsel'
  exact endCatBodyCore hcode hwv (endDispatchCat hsel) (endDecode_cat hsz)
    (endReachCatBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')
    hAccounts

end Benchmarks.Dss.End
