import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `pot()` getter -/

def potWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endAddressReturnWord ⟨5⟩ σ I

theorem endDecode_pot {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (potTransition.params.map Param.name)
      (transitionSignature potTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endPotConcreteSelector : ByteArray := selectorBytes 0x4b 0xa2 0x36 0x3a
abbrev endPotFirstArmPc : UInt256 := ⟨403⟩
abbrev endPotEntryPc : UInt256 := ⟨664⟩
abbrev endPotRoutinePc : UInt256 := ⟨3209⟩

set_option maxHeartbeats 1000000 in
theorem endPotArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endPotFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

theorem endReachPotBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endPotConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endPotEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x4ba2363a⟩ :=
    endSelWord_eq_of_beq I hsz 0x4b 0xa2 0x36 0x3a ⟨0x4ba2363a⟩
      (by decide +native) (by simpa [selIs, endPotConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endLow1JumpdestPc] using
      RD.selectorSplitTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; decide +native) (by jump_dest) (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by decide +native) (by simp)
  have h391 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow2JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [endLow1SplitPc, endLow2JumpdestPc] using
      RD.selectorSplitTakenAuto h272 endLow1SplitWellFormed
        (by rw [hword]; decide +native) (by jump_dest) (by simp)
  have h392 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
    simpa [endLow2SplitPc] using h391.jumpdest (by decide +native) (by simp)
  have h403 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endPotFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1 + 5)
        (C32 + 22 + 1 + 22 + 1 + 22) := by
    simpa [endLow2SplitPc, endPotFirstArmPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h392 endLow2SplitWellFormed
        (by rw [hword]; decide +native) (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endPotFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endPotFirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo endPotEntryPc 1 h403
    (fun j hj => endPotArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem endPotBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some potTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (potTransition.params.map Param.name)
        (transitionSignature potTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨664⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ potTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (potWord σ_solm I).toNat))])) := by
    simpa [potTransition, potWord, endAddressReturnWord, endSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := potRef) (er := ({ base := "pot", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [potRef])
        (by simp [evalStorageRef, evalStorageRefSteps, potRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨664⟩) (returnPc := ⟨572⟩)
    (routine := ⟨3209⟩) (slot := ⟨5⟩)
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
    (by rfl) (by simpa [potWord] using hbody)

theorem endPotBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf potTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endPotConcreteSelector := by
    simpa [endPotSelectorBytes, endPotConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endPotConcreteSelector (by rfl) hsel'
  exact endPotBodyCore hcode hwv (endDispatchPot hsel) (endDecode_pot hsz)
    (endReachPotBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')
    hAccounts

end Benchmarks.Dss.End
