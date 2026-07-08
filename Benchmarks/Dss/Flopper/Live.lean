import Benchmarks.Dss.Flopper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flopper

/-! ## `live()` getter -/

def liveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flopperSlotWord ⟨8⟩ σ I

theorem flopperDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flopperReachLiveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 10)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨670⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0x957aa58c⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 2 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc 2))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨670⟩ 2 hfirst
    (fun j hj => flopperHighLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperLiveBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some liveTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
        (transitionSignature liveTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨670⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (liveWord σ_solm I).toNat))])) := by
    simpa [liveTransition, liveWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨8⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flopperUint256GetterBodyCore (entry := ⟨670⟩) (returnPc := ⟨644⟩)
    (routine := ⟨3276⟩) (slot := ⟨8⟩)
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
    (by rfl) (by simpa [liveWord] using hbody)

theorem flopperLiveBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 10) rfl hsel
  exact flopperLiveBodyCore hcode hwv (flopperDispatchLive hsel) (flopperDecode_live hsz)
    (flopperReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Flopper
