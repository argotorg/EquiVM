import Benchmarks.Dss.Spot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Spot

/-! ## `live()` getter -/

theorem spotDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem spotReachLiveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 6)) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨400⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : spotSelWord I = ⟨0x957aa58c⟩ :=
    spotSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc 1))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachHighBody 1 (by omega) ⟨400⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem spotLiveBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 6) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (spotLiveWord σ_solm I).toNat))])) := by
    simpa [liveTransition, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      spotUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact spotUint256GetterBodyCore (entry := ⟨400⟩) (returnPc := ⟨336⟩)
    (routine := ⟨1668⟩) (slot := ⟨4⟩)
    hcode (spotDispatchLive hsel) (spotDecode_live hsz)
    (spotReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
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
    (by rfl) (by simpa [spotLiveWord] using hbody)

end Benchmarks.Dss.Spot
