import Benchmarks.Dss.Cat.Common
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-- `live()` reads storage slot 2. -/
def liveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := catSlotWord ⟨2⟩ σ I

theorem catDispatch_live {I : ExecutionEnv} (hsel : selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition,
      ilksTransition, litterTransition])
    (post := [relyTransition, vatTransition, vowTransition, wardsTransition])
    (ti := liveTransition) (htr := by rfl)
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes, fileIlkFlipSelectorBytes,
        fileIlkUintSelectorBytes, fileUintSelectorBytes, ilksSelectorBytes, litterSelectorBytes,
        hcd]
      native_decide
  · rw [selectorOf, liveSelectorBytes]; exact hsel

theorem catDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem catReachLiveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨499⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : catSelWord I = ⟨2507842956⟩ :=
    catSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨2507842956⟩ (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj; omega
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighLowFirstArmPc 0))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  exact catReachHighLowBody 0 (by omega) ⟨499⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

theorem catLiveBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (catSlotWord ⟨2⟩ σ_solm I).toNat))])) := by
    simpa [liveTransition, catSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
      solcSlotWord] using
      catUint256GetterBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef)) (slot := ⟨2⟩)
        (by simp only [initState]; exact hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact catUint256GetterBodyCore (entry := ⟨499⟩) (routine := ⟨2935⟩) (slot := ⟨2⟩)
    hcode (catDispatch_live hsel) (catDecode_live hsz)
    (catReachLiveBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl) (by simpa [catSlotWord] using hbody)

end Benchmarks.Dss.Cat
