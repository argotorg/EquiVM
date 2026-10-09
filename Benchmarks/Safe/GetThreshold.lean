import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Storage
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeGetthresholdBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getthresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe7 0x52 0x35 0xb8 ⟨0xe75235b8⟩
    hdispatch getthresholdSelectorBytes (by decide)
  obtain ⟨k, C, h1501⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe75235b8⟩ 2 ⟨1501⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1512 := safeRuntime_block_1501_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1501
    obtain ⟨_, _, h974⟩ := safeRuntime_block_1512 (by simp) (by jump_dest) h1512
    have hret := safeReturnWord h974 (by simp)
    have hbody : ExecTransitionBody config contract
        (initState σ σ₀ (.ofUInt256 g) A I) ∅ getthresholdTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (.ofUInt256 g) A I)
          (some [.int (Int.ofNat (solcSlotWordAt ⟨4⟩ σ I).toNat)])) := by
      simpa only [getthresholdTransition, nonpayable, solcSlotWordAt, initState,
        Solm.EVM.storageLoad, State.lookupAccount] using
        uint256GetterBodyReturns (cfg := config) (c := contract)
          (initState σ σ₀ (.ofUInt256 g) A I) ∅
          (ref := thresholdRef) (er := { base := "threshold" }) (slot := ⟨4⟩)
          hvalue (by simp)
          (by simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, pure, bind])
          (by decide) rfl (by rfl)
    refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
    exact reEquivSelectorExecution hdispatch (decodeCalldata_empty_ok hlong) hbody
      (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt ⟨4⟩ σ I)))))
  · have h1509 := safeRuntime_block_1501_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1501
    have hrev := safeRuntime_block_1509 (by simp [safeRuntime_block_1501_fallthrough_stack])
      h1509
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getThreshold` (`getthresholdTransition`). -/
theorem safeGetthresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getthresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeGetthresholdBodyCore hcode hsize hdispatch

end Benchmarks.Safe
