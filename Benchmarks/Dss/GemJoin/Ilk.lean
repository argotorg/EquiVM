import Benchmarks.Dss.GemJoin.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.GemJoin

/-! ## `ilk()` getter -/

def gemJoinIlkWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  gemJoinSlotWord ⟨2⟩ σ I

theorem gemJoinDecode_ilk {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ilkTransition.params.map Param.name)
      (transitionSignature ilkTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem gemJoinReachIlkBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (gemJoinSelBytes 5)) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨420⟩ [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : gemJoinSelWord I = ⟨0xc5ce281e⟩ :=
    gemJoinSelWord_eq_of_beq I hsz 0xc5 0xce 0x28 0x1e ⟨0xc5ce281e⟩
      (by native_decide) (by simpa [gemJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc 4))
        (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact gemJoinReachHighBody 4 (by omega) ⟨420⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem gemJoinIlkBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 5) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ ilkTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinIlkWord σ_solm I)))])) := by
    simpa [ilkTransition, gemJoinIlkWord, gemJoinSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      gemJoinBytes32GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := ilkRef) (er := ({ base := "ilk", steps := [] } : EvaledStorageRef))
        (slot := ⟨2⟩)
        (by simp only [initState]; exact hwv) (by simp [ilkRef])
        (by simp [evalStorageRef, evalStorageRefSteps, ilkRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact gemJoinBytes32GetterBodyCore (entry := ⟨420⟩) (returnPc := ⟨318⟩)
    (routine := ⟨1538⟩) (slot := ⟨2⟩)
    hcode (gemJoinDispatchIlk hsel) (gemJoinDecode_ilk hsz)
    (gemJoinReachIlkBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
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
    (by rfl) (by simpa [gemJoinIlkWord] using hbody)

end Benchmarks.Dss.GemJoin
