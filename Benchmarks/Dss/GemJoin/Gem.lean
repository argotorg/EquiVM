import Benchmarks.Dss.GemJoin.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

/-! ## `gem()` getter -/

def gemJoinGemWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  gemJoinAddressReturnWord ⟨3⟩ σ I

theorem gemJoinDecode_gem {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (gemTransition.params.map Param.name)
      (transitionSignature gemTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem gemJoinReachGemBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (gemJoinSelBytes 4)) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨302⟩ [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : gemJoinSelWord I = ⟨0x7bd2bea7⟩ :=
    gemJoinSelWord_eq_of_beq I hsz 0x7b 0xd2 0xbe 0xa7 ⟨0x7bd2bea7⟩
      (by native_decide) (by simpa [gemJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc 4))
        (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact gemJoinReachLowBody 4 (by omega) ⟨302⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem gemJoinGemBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 4) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ gemTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (gemJoinGemWord σ_solm I).toNat))])) := by
    simpa [gemTransition, gemJoinGemWord, gemJoinAddressReturnWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      gemJoinAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := gemRef) (er := ({ base := "gem", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [gemRef])
        (by simp [evalStorageRef, evalStorageRefSteps, gemRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact gemJoinAddressGetterBodyCore (entry := ⟨302⟩) (returnPc := ⟨182⟩)
    (routine := ⟨1332⟩) (slot := ⟨3⟩)
    hcode (gemJoinDispatchGem hsel) (gemJoinDecode_gem hsz)
    (gemJoinReachGemBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
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
    (by rfl) (by simpa [gemJoinGemWord] using hbody)

end Benchmarks.Dss.GemJoin
