import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vat

/-! ## `vice()` getter -/

def viceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vatSlotWord ⟨8⟩ σ I

theorem vatDecode_vice {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (viceTransition.params.map Param.name)
      (transitionSignature viceTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vatReachViceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 26)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨674⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x2d61a355⟩ :=
    vatSelWord_eq_of_beq I hsz 0x2d 0x61 0xa3 0x55 ⟨0x2d61a355⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms370Body 2 (by omega) ⟨674⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by decide +native)

theorem vatViceBodyCore : VatBodyTheorem 26 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 26) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ viceTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (viceWord σ_solm I).toNat))])) := by
    simpa [viceTransition, viceWord, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vatUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := viceRef) (er := ({ base := "vice", steps := [] } : EvaledStorageRef))
        (slot := ⟨8⟩)
        (by simp only [initState]; exact hwv) (by simp [viceRef])
        (by simp [evalStorageRef, evalStorageRefSteps, viceRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vatUint256GetterBodyCore (entry := ⟨674⟩) (returnPc := ⟨465⟩)
    (routine := ⟨2225⟩) (slot := ⟨8⟩)
    hcode (vatDispatchVice hsel) (vatDecode_vice hsz)
    (vatReachViceBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
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
    (by rfl) (by simpa [viceWord] using hbody)

end Benchmarks.Dss.Vat
