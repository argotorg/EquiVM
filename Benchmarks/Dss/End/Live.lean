import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `live()` getter -/

def liveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨8⟩ σ I

theorem endDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

abbrev endLiveConcreteSelector : ByteArray := selectorBytes 0x95 0x7a 0xa5 0x8c

abbrev endLiveFirstArmPc : UInt256 := ⟨223⟩
abbrev endLiveEntryPc : UInt256 := ⟨933⟩
abbrev endLiveRoutinePc : UInt256 := ⟨7494⟩

set_option maxHeartbeats 1000000 in
theorem endLiveArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed endBytecode (nthArmPc endBytecode endLiveFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem endReachLiveBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endLiveConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState σ σ₀ g A I)
        endLiveEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  have hword : endSelWord I = ⟨0x957aa58c⟩ :=
    endSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
      (by native_decide) (by simpa [selIs, endLiveConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup223FirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endLiveFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endLiveFirstArmPc 2))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endLiveEntryPc 2 hfirst
    (fun j hj => endLiveArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endLiveBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some liveTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
        (transitionSignature liveTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) endLiveEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (liveWord σ I).toNat))])) := by
    simpa [liveTransition, liveWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨8⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endUint256GetterBodyCore (entry := endLiveEntryPc)
    (returnPc := endWordReturnPc) (routine := endLiveRoutinePc) (slot := ⟨8⟩)
    hcode hdispatch hdecode hreach
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
    (by rfl) (by simpa [liveWord] using hbody)

theorem endLiveBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf liveTransition)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsel' : selIs I endLiveConcreteSelector := by
    simpa [endLiveSelectorBytes, endLiveConcreteSelector] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endLiveConcreteSelector (by rfl) hsel'
  exact endLiveBodyCore hcode hwv (endDispatchLive hsel) (endDecode_live hsz)
    (endReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')

end Benchmarks.Dss.End
