import Benchmarks.UniswapV4PoolManager.CallComposition
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: continuation and complete traces for source functions returning no values.
def unitContinuationTrace (code : ByteArray) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (ret : UInt256) (R : List UInt256) : ExecResult → Prop
  | .returned _ evm none => ∃ mem aw out k C, RD code I g s0 ret R mem aw out evm.accountMap k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0
  | _ => False

def unitResultTrace (code : ByteArray) (g : Sat256) (s0 : State) : ExecResult → Prop
  | .returned _ evm none => RDret code g s0 evm.accountMap .empty
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0
  | _ => False

-- LIBRARY CANDIDATE: retain a memory invariant at a void function's continuation.
def unitContinuationTraceWithMemory (P : ByteArray → Prop) (code : ByteArray) (I : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret : UInt256) (R : List UInt256) : ExecResult → Prop
  | .returned _ evm none => ∃ mem aw out k C, P mem ∧ RD code I g s0 ret R mem aw out evm.accountMap k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0
  | _ => False

theorem unitContinuationTraceWithMemory_forget {P code I g s0 ret R result}
    (h : unitContinuationTraceWithMemory P code I g s0 ret R result) :
    unitContinuationTrace code I g s0 ret R result := by
  unfold unitContinuationTraceWithMemory at h
  split at h
  · obtain ⟨mem, aw, out, k, C, _, hr⟩ := h
    exact ⟨mem, aw, out, k, C, hr⟩
  · exact h
  · exact h
  · contradiction

theorem unitContinuationTrace_finish {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {result : ExecResult}
    (hfinish : ∀ {mem aw out σ k C}, RD code I g s0 ret R mem aw out σ k C → RDret code g s0 σ .empty)
    (h : unitContinuationTrace code I g s0 ret R result) : unitResultTrace code g s0 result := by
  unfold unitContinuationTrace at h
  split at h
  · obtain ⟨mem, aw, out, k, C, hr⟩ := h
    exact hfinish hr
  · exact h
  · exact h
  · contradiction

theorem unitResultTrace_finishCall {code : ByteArray} {g : Sat256} {s0 : State} {result : ExecResult}
    (caller : Frame) (retVar : Ident) (h : unitResultTrace code g s0 result) :
    unitResultTrace code g s0 (finishBlockResult (resumeCallResult caller retVar result)) := by
  unfold unitResultTrace at h
  split at h
  · exact h
  · exact h
  · exact h
  · contradiction

theorem unitResultTrace_refinement {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : UInt256} {code : ByteArray} {args imms : Store} {result : ExecResult}
    (hcode : I.code = code) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) args t.body result imms)
    (htrace : unitResultTrace code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) result)
    (htype : t.returnType = []) (hfallback : contract.fallback = none) (hreceive : contract.receive = none) :
    runtimeRefinementFor cfg contract σ σ₀ g A I imms := by
  unfold unitResultTrace at htrace
  split at htrace
  · exact htrace.reEquivExecutionGen hcode hd hdec hbody rfl
      (by rw [htype]; exact .fallthrough rfl rfl (by native_decide)) hfallback hreceive
  · exact htrace.reEquivExecutionRevert hcode hd hdec hbody hfallback hreceive
  · exact htrace.reEquivStaticHalt hcode hd hdec hbody hfallback hreceive
  · contradiction

end Benchmarks.UniswapV4PoolManager
