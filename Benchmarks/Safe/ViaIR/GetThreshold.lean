import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007
import Benchmarks.Safe.ViaIR.Blocks.Runtime_008

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeGetthresholdBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getthresholdTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe7 0x52 0x35 0xb8 ⟨0xe75235b8⟩
    hdispatch getthresholdSelectorBytes (by decide)
  obtain ⟨k, C, h1154⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe75235b8⟩ 25 ⟨1154⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1161 := safeRuntime_block_1154_fallthrough (by simp) hvalue h1154
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · have h1172 := safeRuntime_block_1161_fallthrough (by simp)
        (safeIRLengthCheckOk hlong hsmall hsize) h1161
      have hret := safeRuntime_block_1172 (by simp) h1172
      simp only [show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from
          solcFreePtrMem_mload64, show (⟨128⟩ : UInt256).toNat = 128 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl] at hret
      change RDret fork safeBytecode _ _ σ
        ((solcReturnMem (solcSlotWordAt ⟨4⟩ σ I)).readWithPadding 128 32) at hret
      rw [solcReturnMem_read128] at hret
      have hbody : ExecTransitionBody fork config contract
          (initState σ σ₀ (.ofUInt256 g) A I) ∅ getthresholdTransition.body
          (.returned { contract := contract, locals := ∅ }
            (initState σ σ₀ (.ofUInt256 g) A I)
            (some [.int (Int.ofNat (solcSlotWordAt ⟨4⟩ σ I).toNat)])) := by
        simpa only [getthresholdTransition, nonpayable, solcSlotWordAt, initState,
          Stele.EVM.storageLoad, State.lookupAccount] using
          uint256GetterBodyReturns (cfg := config) (c := contract)
            (initState σ σ₀ (.ofUInt256 g) A I) ∅
            (ref := thresholdRef) (er := { base := "threshold" }) (slot := ⟨4⟩)
            hvalue (by simp)
            (by simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, pure, bind])
            (by decide) rfl (by rfl)
      refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
      exact reEquivSelectorExecution hdispatch (safeDecodeCalldata_empty_ok hlong hsmall)
        hbody
        (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
          (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt ⟨4⟩ σ I)))))
    · have h589 := safeRuntime_block_1161_taken (by simp)
        (by
          change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨0⟩ ≠ ⟨0⟩
          rw [safeIRLengthCheckHuge (by omega) hsize]
          decide) (by jump_dest) h1161
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (safeDecodeCalldata_empty_huge (by omega)) (safeRuntime_block_589 (by simp) h589)
  · have h589 := safeRuntime_block_1154_taken (by simp) hvalue (by jump_dest) h1154
    have hrev := safeRuntime_block_589 (by simp [safeRuntime_block_1154_taken_stack]) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getThreshold` (`getthresholdTransition`). -/
theorem safeGetthresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getthresholdTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeGetthresholdBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
