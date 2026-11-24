import Benchmarks.Safe.V1_0227664.Dispatch
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_007
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_008
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_013
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_029
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_041

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def versionReturnData : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray ++ (⟨5⟩ : UInt256).toByteArray ++
    String.toByteArray "1.5.0" ++ ByteArray.zeroes 27

set_option maxRecDepth 100000 in
theorem safeVersionTrace {I g s0 σ k C} {R : List UInt256} {cv : UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1699⟩ (cv :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 18 ≤ 1024) :
    RDret fork safeBytecode g s0 σ versionReturnData := by
  have h918 := safeRuntime_block_1699 (by omega) (by jump_dest) h
  have h9876 := safeRuntime_block_918 (by simp; omega) (by jump_dest) h918
  have h9767 := safeRuntime_block_9489 (by simp; omega) (by jump_dest) h9876
  have h9735 := safeRuntime_block_9356 (by simp; omega) h9767
  have h9744 := safeRuntime_block_9364_fallthrough (by evm_ov)
    (by native_decide) h9735
  have h9735' := safeRuntime_block_9373 (by evm_ov) (by jump_dest) h9744
  have h9759 := safeRuntime_block_9364_taken (by evm_ov)
    (by native_decide) (by jump_dest) h9735'
  have h6891 := safeRuntime_block_9392 (by simp; omega) (by jump_dest) h9759
  have h771 := safeRuntime_block_6705 (by simp; omega) (by jump_dest) h6891
  have hret := safeRuntime_block_771 (by simp; omega) h771
  convert hret using 1 <;> native_decide

set_option maxRecDepth 100000 in
theorem safeVersionBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some versionTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xff 0xa1 0xad 0x74 ⟨0xffa1ad74⟩
    hdispatch versionSelectorBytes (by decide)
  obtain ⟨k, C, h1688⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xffa1ad74⟩ 3 ⟨1688⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1699 := safeRuntime_block_1688_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1688
    have hret := safeVersionTrace h1699 (by simp)
    have hbody := nonpayableBytesLiteralBodyReturns (fork := fork) (cfg := config) (contract := contract)
      (imms := ∅)
      (initState σ σ₀ (.ofUInt256 g) A I) ∅ (String.toByteArray "1.5.0") hvalue
    refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
    exact reEquivSelectorExecution hdispatch (decodeCalldata_empty_ok hlong) hbody
      (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode (by native_decide))))
  · have h1696 := safeRuntime_block_1688_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1688
    have hrev := safeRuntime_block_1696 (by simp [safeRuntime_block_1688_fallthrough_stack])
      h1696
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `VERSION` (`versionTransition`). -/
theorem safeVersionRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some versionTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeVersionBodyCore hcode hsize hdispatch

end Benchmarks.Safe.V1_0227664
