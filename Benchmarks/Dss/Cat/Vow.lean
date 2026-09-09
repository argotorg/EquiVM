import Benchmarks.Dss.Cat.Common
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

theorem catDispatch_vow {I : ExecutionEnv} (hsel : selIs I ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩) :
    dispatchMsg contract I.calldata = some vowTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition,
      ilksTransition, litterTransition, liveTransition, relyTransition, vatTransition])
    (post := [wardsTransition])
    (ti := vowTransition) (htr := by rfl)
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes, fileIlkFlipSelectorBytes,
        fileIlkUintSelectorBytes, fileUintSelectorBytes, ilksSelectorBytes, litterSelectorBytes,
        liveSelectorBytes, relySelectorBytes, vatSelectorBytes, hcd]
      decide +native
  · rw [selectorOf, vowSelectorBytes]; exact hsel

theorem catDecode_vow {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
      (transitionSignature vowTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem catReachVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨437⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : catSelWord I = ⟨1651291077⟩ :=
    catSelWord_eq_of_beq I hsz 0x62 0x6c 0xb3 0xc5 ⟨1651291077⟩ (by decide +native) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]; decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj; omega
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc 0))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  exact catReachLowHighBody 0 (by omega) ⟨437⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by decide +native)

theorem catVowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (catAddressReturnWord ⟨4⟩ σ_solm I).toNat))])) := by
    simpa [vowTransition, catAddressReturnWord, catSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, solcSlotWord] using
      catAddressGetterBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef)) (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [vowRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact catAddressGetterBodyCore (entry := ⟨437⟩) (routine := ⟨2700⟩) (slot := ⟨4⟩)
    hcode (catDispatch_vow hsel) (catDecode_vow hsz)
    (catReachVowBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | decide +native)
    (by unfold solcAddressSlotGetterWf; repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by rfl) (by simpa [catAddressReturnWord, catSlotWord] using hbody)

end Benchmarks.Dss.Cat
