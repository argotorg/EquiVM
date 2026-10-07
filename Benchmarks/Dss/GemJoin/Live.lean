import Benchmarks.Dss.GemJoin.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

/-! ## `live()` getter -/

def gemJoinLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨5⟩ σ I

theorem gemJoinDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem gemJoinReachLiveBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (gemJoinSelBytes 7)) :
    ∃ k C, RD gemJoinBytecode I g (initState σ σ₀ g A I)
        ⟨310⟩ [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : gemJoinSelWord I = ⟨0x957aa58c⟩ :=
    gemJoinSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
      (by native_decide) (by simpa [gemJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc 0))
        (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact gemJoinReachHighBody 0 (by omega) ⟨310⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem gemJoinLiveBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 7)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 7) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (gemJoinLiveWord σ I).toNat))])) := by
    simpa [liveTransition, gemJoinLiveWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      gemJoinUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact gemJoinUint256GetterBodyCore (entry := ⟨310⟩) (returnPc := ⟨318⟩)
    (routine := ⟨1347⟩) (slot := ⟨5⟩)
    hcode (gemJoinDispatchLive hsel) (gemJoinDecode_live hsz)
    (gemJoinReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
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
    (by rfl) (by simpa [gemJoinLiveWord] using hbody)

end Benchmarks.Dss.GemJoin
