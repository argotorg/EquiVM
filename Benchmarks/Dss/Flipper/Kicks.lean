import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `kicks()` getter -/

def kicksWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord ⟨6⟩ σ I

theorem flipperDecode_kicks {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (kicksTransition.params.map Param.name)
      (transitionSignature kicksTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flipperReachKicksBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 10)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨878⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0xcfdd3302⟩ :=
    flipperSelWord_eq_of_beq I hsz 0xcf 0xdd 0x33 0x02 ⟨0xcfdd3302⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc 1))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachLowHighBody 1 (by omega) ⟨878⟩ hcode hwv hsz hsize hroot hlow
    heq0 htake (by jump_dest) (by native_decide)

theorem flipperKicksBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 10) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ kicksTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (kicksWord σ_solm I).toNat))])) := by
    simpa [kicksTransition, kicksWord, flipperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flipperUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := kicksRef) (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
        (slot := ⟨6⟩)
        (by simp only [initState]; exact hwv) (by simp [kicksRef])
        (by simp [evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flipperUint256GetterBodyCore (entry := ⟨878⟩) (returnPc := ⟨426⟩)
    (routine := ⟨5815⟩) (slot := ⟨6⟩)
    hcode (flipperDispatchKicks hsel) (flipperDecode_kicks hsz)
    (flipperReachKicksBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
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
    (by rfl) (by simpa [kicksWord] using hbody)

end Benchmarks.Dss.Flipper
