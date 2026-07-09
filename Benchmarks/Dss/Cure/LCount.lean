import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Cure

/-! ## `lCount()` -/

def lCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨8⟩ σ I

theorem cureDispatchLCount {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 5)) :
    dispatchMsg contract I.calldata = some lCountTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some lCountTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes]
  native_decide

theorem cureDecode_lCount {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (lCountTransition.params.map Param.name)
      (transitionSignature lCountTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cureLCountBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 5) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ lCountTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (lCountWord σ_solm I).toNat))])) := by
    simpa [lCountTransition, lCountWord, cureSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      cureUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := lCountRef) (er := ({ base := "lCount", steps := [] } : EvaledStorageRef))
        (slot := ⟨8⟩)
        (by simp only [initState]; exact hwv) (by simp [lCountRef])
        (by simp [evalStorageRef, evalStorageRefSteps, lCountRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact cureUint256GetterBodyCore (entry := ⟨562⟩) (returnPc := ⟨343⟩)
    (routine := ⟨2226⟩) (slot := ⟨8⟩)
    hcode (cureDispatchLCount hsel) (cureDecode_lCount hsz)
    (cureReachLCountBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
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
    (by rfl) (by simpa [lCountWord] using hbody)

end Benchmarks.Dss.Cure
