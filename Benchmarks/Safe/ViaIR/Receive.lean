import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.Blocks.Runtime_001

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeReceiveArgs (evm : State) (frame : Frame) :
    evalExprs? config frame evm [sender, callvalue] =
      .ok [.address evm.executionEnv.source, .int evm.executionEnv.weiValue.toNat] := by
  simp only [evalExprs?, sender, callvalue, evalExpr?, envValue, bind, EvalResult.bind, pure]
  rfl

theorem safeReceiveSource (evm : State)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm ∅ receiveTransition.body
      (.returned { contract := contract, locals := ∅ } evm none) := by
  exact .execBlockOK (.consNormal (.emit (hperm := hperm) (safeReceiveArgs evm _)) .nil)

theorem safeReceiveSourceStatic (evm : State) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm ∅ receiveTransition.body .staticViolation := by
  exact .execBlockStatic (.consStatic (.emitStatic (safeReceiveArgs evm _) hperm))

theorem safeReceiveTraceStatic {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hperm : I.perm = false)
    (h : RD fork safeBytecode I g s0 ⟨115⟩ [] mem aw rdata σ k C) :
    RDstatic fork safeBytecode g s0 := by
  -- The provided summary of PC 115 includes LOG2 and requires write permission.
  -- Its static branch stops just before that instruction.
  have hstore := evm_run h with [jumpdest, push1 ⟨64⟩, genMload, callvalue, dup2, genMstore]
  have htopic := RD.pushConst (width := 32) (op := .PUSH32) hstore
    ⟨27613899205238800472750487981127851187820584748339481801398827578897088740413⟩
    (by decide) (by native_decide) (by evm_ov)
  have hlog := evm_run htopic with [push1 ⟨32⟩, caller, swap3]
  exact RD.log2Static hlog hperm (by native_decide) (by decide)

set_option maxRecDepth 100000 in
theorem safeReceiveBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size = 0) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨k, C, h14⟩ := safeReachShort (g := Sat256.ofUInt256 g)
    (σ := σ) (σ₀ := σ₀) (A := A) hcode (by omega)
  have h115 := safeRuntime_block_14_taken (by decide) (by rw [hsize]; decide)
    (by jump_dest) h14
  have hreceive : receiveDispatchMsg contract I.calldata = some receiveTransition := by
    simp only [receiveDispatchMsg, hsize]
    rfl
  cases hperm : I.perm with
  | false =>
      exact RDstatic.reEquivReceiveStaticHalt hcode
        (safeReceiveTraceStatic hperm h115) hreceive rfl rfl
        (safeReceiveSourceStatic _ hperm)
  | true =>
      have hret := safeRuntime_block_115 (by decide) hperm h115
      exact RDret.reEquivElim hcode hret fun _ _ hsuccess ↦
        reEquiv_receiveExecution hreceive rfl rfl (safeReceiveSource (fork := fork) (hperm := by assumption) _)
          (.success hsuccess rfl rfl (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))

/-- Empty calldata follows receive, including its LOG2 static-mode halt. -/
theorem safeReceiveRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size = 0) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeReceiveBodyCore hcode hsize

end Benchmarks.Safe.ViaIR
