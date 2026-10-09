import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Storage
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_009
import Benchmarks.Safe.Blocks.Runtime_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeNonceBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some nonceTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xaf 0xfe 0xd0 0xe0 ⟨0xaffed0e0⟩
    hdispatch nonceSelectorBytes (by decide)
  obtain ⟨k, C, h1187⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xaffed0e0⟩ 0 ⟨1187⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1198 := safeRuntime_block_1187_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1187
    obtain ⟨_, _, h974⟩ := safeRuntime_block_1198 (by simp) (by jump_dest) h1198
    have hret := safeReturnWord h974 (by simp)
    have hbody : ExecTransitionBody config contract
        (initState σ σ₀ (.ofUInt256 g) A I) ∅ nonceTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (.ofUInt256 g) A I)
          (some [.int (Int.ofNat (solcSlotWordAt ⟨5⟩ σ I).toNat)])) := by
      simpa only [nonceTransition, nonpayable, solcSlotWordAt, initState,
        Solm.EVM.storageLoad, State.lookupAccount] using
        uint256GetterBodyReturns (cfg := config) (c := contract)
          (initState σ σ₀ (.ofUInt256 g) A I) ∅
          (ref := nonceRef) (er := { base := "nonce" }) (slot := ⟨5⟩)
          hvalue (by simp)
          (by simp [evalStorageRef, evalStorageRefSteps, nonceRef, EvalResult.bind, pure, bind])
          (by decide) rfl (by rfl)
    refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
    exact reEquivSelectorExecution hdispatch (decodeCalldata_empty_ok hlong) hbody
      (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt ⟨5⟩ σ I)))))
  · have h1195 := safeRuntime_block_1187_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1187
    have hrev := safeRuntime_block_1195 (by simp [safeRuntime_block_1187_fallthrough_stack])
      h1195
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `nonce` (`nonceTransition`). -/
theorem safeNonceRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some nonceTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeNonceBodyCore hcode hsize hdispatch

end Benchmarks.Safe
