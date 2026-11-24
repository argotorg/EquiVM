import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034
import Benchmarks.Safe.ViaIR.Blocks.Runtime_035

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def versionReturnData : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray ++ (⟨5⟩ : UInt256).toByteArray ++
    String.toByteArray "1.5.0" ++ ByteArray.zeroes 27

set_option maxRecDepth 100000 in
theorem safeVersionTrace {I g s0 σ k C} {R : List UInt256} {cv : UInt256}
    (h : RD fork safeBytecode I g s0 ⟨530⟩ (cv :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 18 ≤ 1024) :
    RDret fork safeBytecode g s0 σ versionReturnData := by
  have h7128 := safeRuntime_block_530 (by omega) (by jump_dest) h
  have h7157 := safeRuntime_block_7128_fallthrough (by evm_ov) (by native_decide) h7128
  have h547 := safeRuntime_block_7157 (by evm_ov) (by jump_dest) h7157
  have h7374 := safeRuntime_block_547 (by evm_ov) (by jump_dest) h547
  have h7384 := safeRuntime_block_7374 (by evm_ov) h7374
  have h7416 := safeRuntime_block_7384_taken (by evm_ov) (by native_decide)
    (by jump_dest) h7384
  have h7384' := safeRuntime_block_7416 (by evm_ov) (by jump_dest) h7416
  have h7392 := safeRuntime_block_7384_fallthrough (by evm_ov) (by native_decide) h7384'
  have h585 := safeRuntime_block_7392 (by evm_ov) (by jump_dest) h7392
  have hret := safeRuntime_block_585 (by evm_ov) h585
  convert hret using 1 <;> native_decide

set_option maxRecDepth 100000 in
theorem safeVersionBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some versionTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xff 0xa1 0xad 0x74 ⟨0xffa1ad74⟩
    hdispatch versionSelectorBytes (by decide)
  change selWord I = ⟨0xffa1ad74⟩ at hword
  obtain ⟨k, C, h498⟩ := safeReachSelectorEnd (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hsize hlong (by rw [hword]; native_decide)
  have h513 := safeRuntime_block_498_taken (by simp) (by rw [hword]; decide)
    (by jump_dest) h498
  simp only [safeRuntime_block_498_taken_stack] at h513
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h519 := safeRuntime_block_513_fallthrough (by simp) hvalue h513
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · have h530 := safeRuntime_block_519_fallthrough (by simp)
        (safeIRLengthCheckOk hlong hsmall hsize) h519
      have hret := safeVersionTrace h530 (by simp)
      have hbody := nonpayableBytesLiteralBodyReturns (fork := fork) (cfg := config) (contract := contract)
        (imms := ∅)
        (initState σ σ₀ (.ofUInt256 g) A I) ∅ (String.toByteArray "1.5.0") hvalue
      refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
      exact reEquivSelectorExecution hdispatch (safeDecodeCalldata_empty_ok hlong hsmall) hbody
        (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode (by native_decide))))
    · have h589 := safeRuntime_block_519_taken (by simp)
        (by
          change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨0⟩ ≠ ⟨0⟩
          rw [safeIRLengthCheckHuge (by omega) hsize]
          decide) (by jump_dest) h519
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (safeDecodeCalldata_empty_huge (by omega)) (safeRuntime_block_589 (by simp) h589)
  · have h589 := safeRuntime_block_513_taken (by simp) hvalue (by jump_dest) h513
    exact reEquivSelectorRevert hcode hdispatch (safeRuntime_block_589 (by simp) h589)
      fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `VERSION` (`versionTransition`). -/
theorem safeVersionRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some versionTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeVersionBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
