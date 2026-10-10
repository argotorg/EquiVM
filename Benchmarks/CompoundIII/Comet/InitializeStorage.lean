import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.InitializeEvm
import Benchmarks.CompoundIII.Comet.InitializeSource

/-!
# CometWithExtendedAssetList `initializeStorage()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1330; reach lemma `cometWithExtendedAssetListReachInitializeStorageBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

/-- `initializeStorage()`: the theorem `Correct.lean` routes selector 6 to. -/
theorem cometWithExtendedAssetListInitializeStorageBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 6) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some initializeStorageTransition :=
    cometSelectorDispatch ⟨6, by decide⟩ hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (initializeStorageTransition.params.map Param.name)
      (transitionSignature initializeStorageTransition).paramTypes I.calldata =
      some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  have hX := initializeX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hvalid : lastAccrualWord (solcSlotWordAt ⟨1⟩ σ I) = ⟨0⟩ ∧
          (timestampWord I).toNat < 2^40
      · unfold InitializeResult at hX
        rw [if_pos ⟨hv, hhi, hvalid⟩] at hX
        have hz : lastAccrualWord (Solm.EVM.storageLoad
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨1⟩) = ⟨0⟩ := by
          simpa only [storageLoad_initState_solcSlotWord, solcSlotWordAt] using hvalid.1
        by_cases hp : I.perm = true
        · rw [if_pos hp] at hX
          exact selectorStateReturn_refines hcode hX hd hdec
            (initializeStorage_returns _ (immStore v) hv hhi hz hvalid.2)
            initializeSourceState_accountMap.symm voidReturnEquiv
        · rw [if_neg hp] at hX
          exact selectorStatic_refines hcode hX hd hdec
            (initializeStorage_static _ (immStore v) hv hhi hz hvalid.2
              (Bool.eq_false_iff.mpr hp))
      · simp only [InitializeResult, hvalid, and_false, if_false] at hX
        apply selectorRevert_refines hcode hX hd hdec
        apply initializeStorage_reverts _ (immStore v) hv hhi
        simpa only [storageLoad_initState_solcSlotWord, solcSlotWordAt] using hvalid
    · simp only [InitializeResult, hhi, false_and, and_false, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [initializeStorage_body]
      exact calldataPrologue_huge hv hhi
  · simp only [InitializeResult, hv, false_and, if_false] at hX
    apply selectorRevert_refines hcode hX hd hdec
    rw [initializeStorage_body]
    exact calldataPrologue_nonpayable hv

end Benchmarks.CompoundIII.Comet
