import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `cat()` getter -/

def catWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcAddressSlotWord ⟨2⟩ σ I

theorem endDecode_cat {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (catTransition.params.map Param.name)
      (transitionSignature catTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endCatConcreteSelector : ByteArray := selectorBytes 0xe4 0x88 0x18 0x13
abbrev endCatFirstArmPc : UInt256 := ⟨65⟩
abbrev endCatEntryPc : UInt256 := ⟨1208⟩
abbrev endCatRoutinePc : UInt256 := ⟨9558⟩

set_option maxHeartbeats 1000000 in
theorem endCatArmsWellFormed :
    ∀ j, j ≤ 0 → armWellFormed endBytecode (nthArmPc endBytecode endCatFirstArmPc j) := by
  intro j hj
  interval_cases j
  dsimp [armWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endReachCatBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endCatConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState σ σ₀ g A I)
        endCatEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  have hword : endSelWord I = ⟨0xe4881813⟩ :=
    endSelWord_eq_of_beq I hsz 0xe4 0x88 0x18 0x13 ⟨0xe4881813⟩
      (by native_decide) (by simpa [selIs, endCatConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup65FirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endCatFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endCatFirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endCatEntryPc 0 hfirst
    (fun j hj => endCatArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endCatBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some catTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (catTransition.params.map Param.name)
        (transitionSignature catTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1208⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ catTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (catWord σ I).toNat))])) := by
    simpa [catTransition, catWord, solcAddressSlotWord, solcSlotWordAt, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      endAddressGetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := catRef) (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
        (slot := ⟨2⟩)
        (by simp only [initState]; exact hwv) (by simp [catRef])
        (by simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endAddressGetterBodyCore (entry := ⟨1208⟩) (returnPc := ⟨572⟩)
    (routine := ⟨9558⟩) (slot := ⟨2⟩)
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
    (by rfl) (by simpa [catWord] using hbody)

theorem endCatBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf catTransition)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsel' : selIs I endCatConcreteSelector := by
    simpa [endCatSelectorBytes, endCatConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endCatConcreteSelector (by rfl) hsel'
  exact endCatBodyCore hcode hwv (endDispatchCat hsel) (endDecode_cat hsz)
    (endReachCatBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')

end Benchmarks.Dss.End
