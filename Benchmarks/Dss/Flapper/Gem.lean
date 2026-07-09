import Benchmarks.Dss.Flapper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flapper

/-! ## `gem()` getter -/

def gemWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperAddressReturnWord ⟨3⟩ σ I

theorem flapperDecode_gem {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (gemTransition.params.map Param.name)
      (transitionSignature gemTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flapperReachGemBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 7)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨638⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0x7bd2bea7⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x7b 0xd2 0xbe 0xa7 ⟨0x7bd2bea7⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc 3))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨638⟩ 3 hfirst
    (fun j hj => flapperLowHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperGemBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 7) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ gemTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (gemWord σ_solm I).toNat))])) := by
    simpa [gemTransition, gemWord, flapperAddressReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := gemRef) (er := ({ base := "gem", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [gemRef])
        (by simp [evalStorageRef, evalStorageRefSteps, gemRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flapperAddressGetterBodyCore (entry := ⟨638⟩) (returnPc := ⟨405⟩)
    (routine := ⟨2960⟩) (slot := ⟨3⟩)
    hcode (flapperDispatchGem hsel) (flapperDecode_gem hsz)
    (flapperReachGemBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts
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
    (by rfl) (by simpa [gemWord] using hbody)

end Benchmarks.Dss.Flapper
