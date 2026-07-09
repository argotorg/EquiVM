import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Vat

/-! ## `live()` getter -/

def liveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vatSlotWord ⟨10⟩ σ I

theorem vatDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vatReachLiveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 18)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1161⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x957aa58c⟩ :=
    vatSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms212Body 2 (by omega) ⟨1161⟩ hcode hwv hsz hsize
    hroot hhigh hhighlow heq0 htake (by jump_dest) (by native_decide)

theorem vatLiveBodyCore : VatBodyTheorem 18 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 18) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (liveWord σ_solm I).toNat))])) := by
    simpa [liveTransition, liveWord, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vatUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨10⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vatUint256GetterBodyCore (entry := ⟨1161⟩) (returnPc := ⟨465⟩)
    (routine := ⟨5356⟩) (slot := ⟨10⟩)
    hcode (vatDispatchLive hsel) (vatDecode_live hsz)
    (vatReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts
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

end Benchmarks.Dss.Vat
