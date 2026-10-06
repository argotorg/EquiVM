import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `when()` -/

def whenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨4⟩ σ I

theorem cureDispatchWhen {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 19)) :
    dispatchMsg contract I.calldata = some whenTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 19 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some whenTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes, curePosSelectorBytes,
    cureRelySelectorBytes, cureSaySelectorBytes, cureSrcsSelectorBytes,
    cureTCountSelectorBytes, cureTellSelectorBytes, cureWaitSelectorBytes,
    cureWardsSelectorBytes, cureWhenSelectorBytes]
  native_decide

theorem cureDecode_when {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (whenTransition.params.map Param.name)
      (transitionSignature whenTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cureWhenBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 19)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 19) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ whenTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (whenWord σ I).toNat))])) := by
    simpa [whenTransition, whenWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      cureUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := whenRef) (er := ({ base := "when", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [whenRef])
        (by simp [evalStorageRef, evalStorageRefSteps, whenRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact cureUint256GetterBodyCore (entry := ⟨808⟩) (returnPc := ⟨343⟩)
    (routine := ⟨3603⟩) (slot := ⟨4⟩)
    hcode (cureDispatchWhen hsel) (cureDecode_when hsz)
    (cureReachWhenBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
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
    (by rfl) (by simpa [whenWord] using hbody)

end Benchmarks.Dss.Cure
