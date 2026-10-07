import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Blocks.Runtime_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeReceiveArgs (evm : State) (frame : Frame) :
    evalExprs? config frame evm [sender, callvalue] =
      .ok [.address evm.executionEnv.source, .int evm.executionEnv.weiValue.toNat] := by
  simp only [evalExprs?, sender, callvalue, evalExpr?, envValue, bind, EvalResult.bind, pure]
  rfl

theorem safeReceiveSource (evm : State) :
    ExecTransitionBody config contract evm ∅ receiveTransition.body
      (.returned { contract := contract, locals := ∅ } evm none) := by
  exact .execBlockOK (.consNormal (.emit (safeReceiveArgs evm _)) .nil)

theorem safeReceiveSourceStatic (evm : State) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm ∅ receiveTransition.body .staticViolation := by
  exact .execBlockStatic (.consStatic (.emitStatic (safeReceiveArgs evm _) hperm))

theorem safeReceiveTraceStatic {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hperm : I.perm = false)
    (h : RD safeBytecode I g s0 ⟨481⟩ [] mem aw rdata σ k C) :
    RDstatic safeBytecode g s0 := by
  -- The provided summary of PC 481 includes LOG2 and requires write permission.
  -- Its static branch stops just before that instruction.
  have hstore := evm_run h with [push1 ⟨64⟩, genMload, callvalue, dup2, genMstore]
  have hcaller := evm_run hstore with [caller, swap1]
  have htopic := RD.pushConst (width := 32) (op := .PUSH32) hcaller
    ⟨27613899205238800472750487981127851187820584748339481801398827578897088740413⟩
    (by decide) (by native_decide) (by evm_ov)
  have hsize := evm_run htopic with [swap1, push1 ⟨32⟩, add]
  have hlog := evm_run hsize with [push1 ⟨64⟩, genMload, dup1, swap2, sub, swap1]
  exact RD.log2Static hlog hperm (by native_decide) (by decide)

theorem safeReceiveBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size = 0) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨k, C, h475⟩ := safeReachShort (g := Sat256.ofUInt256 g)
    (σ := σ) (σ₀ := σ₀) (A := A) hcode (by omega)
  have h481 := safeRuntime_block_475_fallthrough (by decide) (by rw [hsize]) h475
  have hreceive : receiveDispatchMsg contract I.calldata = some receiveTransition := by
    simp only [receiveDispatchMsg, hsize]
    rfl
  cases hperm : I.perm with
  | false =>
      exact RDstatic.reEquivReceiveStaticHalt hcode
        (safeReceiveTraceStatic hperm h481) hreceive rfl rfl
        (safeReceiveSourceStatic _ hperm)
  | true =>
      have hret := safeRuntime_block_481 (by decide) hperm h481
      exact RDret.reEquivElim hcode hret fun _ _ hsuccess ↦
        reEquiv_receiveExecution hreceive rfl rfl (safeReceiveSource _)
          (.success hsuccess rfl rfl (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))

/-- Empty calldata follows receive, including its LOG2 static-mode halt. -/
theorem safeReceiveRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size = 0) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeReceiveBodyCore hcode hsize

end Benchmarks.Safe
