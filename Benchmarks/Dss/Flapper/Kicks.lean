import Benchmarks.Dss.Flapper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

/-! ## `kicks()` getter -/

def kicksWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperSlotWord ⟨6⟩ σ I

theorem flapperDecode_kicks {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (kicksTransition.params.map Param.name)
      (transitionSignature kicksTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flapperReachKicksBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 9)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨839⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0xcfdd3302⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xcf 0xdd 0x33 0x02 ⟨0xcfdd3302⟩
        (by decide +native) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 2 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc 2))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo ⟨839⟩ 2 hfirst
    (fun j hj => flapperHighHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem flapperKicksBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 9) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ kicksTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (kicksWord σ_solm I).toNat))])) := by
    simpa [kicksTransition, kicksWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := kicksRef) (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
        (slot := ⟨6⟩)
        (by simp only [initState]; exact hwv) (by simp [kicksRef])
        (by simp [evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flapperUint256GetterBodyCore (entry := ⟨839⟩) (returnPc := ⟨313⟩)
    (routine := ⟨4574⟩) (slot := ⟨6⟩)
    hcode (flapperDispatchKicks hsel) (flapperDecode_kicks hsz)
    (flapperReachKicksBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | decide +native)
    (by rfl) (by simpa [kicksWord] using hbody)

end Benchmarks.Dss.Flapper
