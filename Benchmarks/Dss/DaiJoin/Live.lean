import Benchmarks.Dss.DaiJoin.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

/-! ## `live()` getter -/

def daiJoinLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  daiJoinSlotWord ⟨3⟩ σ I

theorem daiJoinDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem daiJoinReachLiveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiJoinSelBytes 5)) :
    ∃ k C, RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨280⟩ [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : daiJoinSelWord I = ⟨0x957aa58c⟩ :=
    daiJoinSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
      (by native_decide) (by simpa [daiJoinSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc 0))
        (daiJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact daiJoinReachHighBody 0 (by omega) ⟨280⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem daiJoinLiveBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiJoinSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiJoinSelBytes 5) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (daiJoinLiveWord σ_solm I).toNat))])) := by
    simpa [liveTransition, daiJoinLiveWord, daiJoinSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiJoinUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact daiJoinUint256GetterBodyCore (entry := ⟨280⟩) (returnPc := ⟨288⟩)
    (routine := ⟨1077⟩) (slot := ⟨3⟩)
    hcode (daiJoinDispatchLive hsel) (daiJoinDecode_live hsz)
    (daiJoinReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
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
    (by rfl) (by simpa [daiJoinLiveWord] using hbody)

end Benchmarks.Dss.DaiJoin
