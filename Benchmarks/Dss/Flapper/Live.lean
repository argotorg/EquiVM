import Benchmarks.Dss.Flapper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flapper

/-! ## `live()` getter -/

def liveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperSlotWord ⟨7⟩ σ I

theorem flapperDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flapperReachLiveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 11)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨654⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0x957aa58c⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 0 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc 0))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨654⟩ 0 hfirst
    (fun j hj => flapperHighLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperLiveBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 11) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (liveWord σ_solm I).toNat))])) := by
    simpa [liveTransition, liveWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨7⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flapperUint256GetterBodyCore (entry := ⟨654⟩) (returnPc := ⟨313⟩)
    (routine := ⟨2981⟩) (slot := ⟨7⟩)
    hcode (flapperDispatchLive hsel) (flapperDecode_live hsz)
    (flapperReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts
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

end Benchmarks.Dss.Flapper
