import Benchmarks.Dss.DaiJoin.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

/-! ## `dai()` getter -/

def daiJoinDaiWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  daiJoinAddressReturnWord ⟨2⟩ σ I

theorem daiJoinDecode_dai {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (daiTransition.params.map Param.name)
      (transitionSignature daiTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem daiJoinReachDaiBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiJoinSelBytes 1)) :
    ∃ k C, RD daiJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨426⟩ [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : daiJoinSelWord I = ⟨0xf4b9fa75⟩ :=
    daiJoinSelWord_eq_of_beq I hsz 0xf4 0xb9 0xfa 0x75 ⟨0xf4b9fa75⟩
      (by native_decide) (by simpa [daiJoinSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat daiJoinBytecode (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc 4))
        (daiJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact daiJoinReachHighBody 4 (by omega) ⟨426⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem daiJoinDaiBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiJoinSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiJoinSelBytes 1) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ daiTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (daiJoinDaiWord σ_solm I).toNat))])) := by
    simpa [daiTransition, daiJoinDaiWord, daiJoinAddressReturnWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      daiJoinAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := daiRef) (er := ({ base := "dai", steps := [] } : EvaledStorageRef))
        (slot := ⟨2⟩)
        (by simp only [initState]; exact hwv) (by simp [daiRef])
        (by simp [evalStorageRef, evalStorageRefSteps, daiRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact daiJoinAddressGetterBodyCore (entry := ⟨426⟩) (returnPc := ⟨160⟩)
    (routine := ⟨1663⟩) (slot := ⟨2⟩)
    hcode (daiJoinDispatchDai hsel) (daiJoinDecode_dai hsz)
    (daiJoinReachDaiBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
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
    (by rfl) (by simpa [daiJoinDaiWord] using hbody)

end Benchmarks.Dss.DaiJoin
