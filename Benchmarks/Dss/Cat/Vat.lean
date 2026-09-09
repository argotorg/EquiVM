import Benchmarks.Dss.Cat.Common
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

theorem catDispatch_vat {I : ExecutionEnv} (hsel : selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x36, 0x56, 0x9e, 0x77]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition,
      ilksTransition, litterTransition, liveTransition, relyTransition])
    (post := [vowTransition, wardsTransition])
    (ti := vatTransition) (htr := by rfl)
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes, fileIlkFlipSelectorBytes,
        fileIlkUintSelectorBytes, fileUintSelectorBytes, ilksSelectorBytes, litterSelectorBytes,
        liveSelectorBytes, relySelectorBytes, hcd]
      decide +native
  · rw [selectorOf, vatSelectorBytes]; exact hsel

theorem catDecode_vat {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vatTransition.params.map Param.name)
      (transitionSignature vatTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem catReachVatBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨339⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : catSelWord I = ⟨911646327⟩ :=
    catSelWord_eq_of_beq I hsz 0x36 0x56 0x9e 0x77 ⟨911646327⟩ (by decide +native) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j <;> (rw [hword]; decide +native)
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc 2))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  exact catReachLowLowBody 2 (by omega) ⟨339⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by decide +native)

theorem catVatBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vatTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (catAddressReturnWord ⟨3⟩ σ_solm I).toNat))])) := by
    simpa [vatTransition, catAddressReturnWord, catSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, solcSlotWord] using
      catAddressGetterBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef)) (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [vatRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact catAddressGetterBodyCore (entry := ⟨339⟩) (routine := ⟨1148⟩) (slot := ⟨3⟩)
    hcode (catDispatch_vat hsel) (catDecode_vat hsz)
    (catReachVatBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | decide +native)
    (by unfold solcAddressSlotGetterWf; repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by rfl) (by simpa [catAddressReturnWord, catSlotWord] using hbody)

end Benchmarks.Dss.Cat
