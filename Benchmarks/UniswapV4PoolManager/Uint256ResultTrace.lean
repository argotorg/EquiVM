import Benchmarks.UniswapV4PoolManager.ReturnCall
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a trace for a source computation returning one uint256.
def uint256ResultTrace (code : ByteArray) (g : Sat256) (s0 : State) : ExecResult → Prop
  | .returned _ evm (some [.int n]) =>
      ∃ word : UInt256, n = Int.ofNat word.toNat ∧ RDret code g s0 evm.accountMap word.toByteArray
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0
  | _ => False

theorem uint256ResultTrace_returnCall {code : ByteArray} {g : Sat256} {s0 : State} {result : ExecResult}
    (caller : Frame) (retVar : Ident) (h : uint256ResultTrace code g s0 result) :
    uint256ResultTrace code g s0 (returnCallResult caller retVar result) := by
  unfold uint256ResultTrace at h
  split at h
  · exact h
  · exact h
  · exact h
  · contradiction

theorem uint256ResultTrace_refinement {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : UInt256} {code : ByteArray} {args imms : Store} {result : ExecResult}
    (hcode : I.code = code) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) args t.body result imms)
    (htrace : uint256ResultTrace code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) result)
    (htype : t.returnType = [.elem (.int (.uint ⟨256, by decide⟩))])
    (hfallback : contract.fallback = none) (hreceive : contract.receive = none) :
    runtimeRefinementFor cfg contract σ σ₀ g A I imms := by
  unfold uint256ResultTrace at htrace
  split at htrace
  · obtain ⟨word, rfl, hr⟩ := htrace
    exact hr.reEquivExecutionGen hcode hd hdec hbody rfl
      (by rw [htype]; exact returnEquiv_of_encode (uint256ReturnEncoding word)) hfallback hreceive
  · exact htrace.reEquivExecutionRevert hcode hd hdec hbody hfallback hreceive
  · exact htrace.reEquivStaticHalt hcode hd hdec hbody hfallback hreceive
  · contradiction

end Benchmarks.UniswapV4PoolManager
