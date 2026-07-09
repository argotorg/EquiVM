import Benchmarks.Dss.Cat.Common
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

theorem catDispatch_box {I : ExecutionEnv} (hsel : selIs I ⟨#[0x75, 0x42, 0x15, 0xa1]⟩) :
    dispatchMsg contract I.calldata = some boxTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x75, 0x42, 0x15, 0xa1]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition])
    (post := [cageTransition, clawTransition, denyTransition, fileAddressTransition,
      fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition, ilksTransition,
      litterTransition, liveTransition, relyTransition, vatTransition, vowTransition,
      wardsTransition])
    (ti := boxTransition) (htr := by rfl)
  · intro t ht
    simp at ht
    rcases ht with rfl
    simp only [selectorOf, biteSelectorBytes, hcd]
    native_decide
  · rw [selectorOf, boxSelectorBytes]; exact hsel

theorem catDecode_box {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (boxTransition.params.map Param.name)
      (transitionSignature boxTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem catReachBoxBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x75, 0x42, 0x15, 0xa1]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨491⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : catSelWord I = ⟨1967265185⟩ :=
    catSelWord_eq_of_beq I hsz 0x75 0x42 0x15 0xa1 ⟨1967265185⟩ (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j <;> (rw [hword]; native_decide)
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc 3))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  exact catReachLowHighBody 3 (by omega) ⟨491⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem catBoxBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x75, 0x42, 0x15, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x75, 0x42, 0x15, 0xa1]⟩ rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ boxTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (catSlotWord ⟨5⟩ σ_solm I).toNat))])) := by
    simpa [boxTransition, catSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
      solcSlotWord] using
      catUint256GetterBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := boxRef) (er := ({ base := "box", steps := [] } : EvaledStorageRef)) (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [boxRef])
        (by simp [evalStorageRef, evalStorageRefSteps, boxRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact catUint256GetterBodyCore (entry := ⟨491⟩) (routine := ⟨2929⟩) (slot := ⟨5⟩)
    hcode (catDispatch_box hsel) (catDecode_box hsz)
    (catReachBoxBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl) (by simpa [catSlotWord] using hbody)

end Benchmarks.Dss.Cat
