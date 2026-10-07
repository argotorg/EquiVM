import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `say()` -/

def sayWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨9⟩ σ I

theorem cureDispatchSay {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 13)) :
    dispatchMsg contract I.calldata = some sayTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some sayTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes, curePosSelectorBytes,
    cureRelySelectorBytes, cureSaySelectorBytes]
  native_decide

theorem cureDecode_say {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (sayTransition.params.map Param.name)
      (transitionSignature sayTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cureSayBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 13)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 13) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ sayTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (sayWord σ I).toNat))])) := by
    simpa [sayTransition, sayWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      cureUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := sayRef) (er := ({ base := "say", steps := [] } : EvaledStorageRef))
        (slot := ⟨9⟩)
        (by simp only [initState]; exact hwv) (by simp [sayRef])
        (by simp [evalStorageRef, evalStorageRefSteps, sayRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact cureUint256GetterBodyCore (entry := ⟨716⟩) (returnPc := ⟨343⟩)
    (routine := ⟨3344⟩) (slot := ⟨9⟩)
    hcode (cureDispatchSay hsel) (cureDecode_say hsz)
    (cureReachSayBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
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
    (by rfl) (by simpa [sayWord] using hbody)

end Benchmarks.Dss.Cure
