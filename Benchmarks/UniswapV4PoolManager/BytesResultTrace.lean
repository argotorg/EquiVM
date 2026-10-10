import Benchmarks.UniswapV4PoolManager.BytesABI
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: trace and refinement glue for a computation returning one bytes value.
def bytesResultTrace (code : ByteArray) (g : Sat256) (s0 : State) : ExecResult → Prop
  | .returned _ evm (some [.bytes data]) => RDret code g s0 evm.accountMap (bytesReturnEncoding data)
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0
  | _ => False

theorem bytesResultTrace_refinement {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : UInt256} {code : ByteArray} {args imms : Store} {result : ExecResult}
    (hcode : I.code = code) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) args t.body result imms)
    (htrace : bytesResultTrace code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) result)
    (htype : t.returnType = [.bytes])
    (hfallback : contract.fallback = none) (hreceive : contract.receive = none) :
    runtimeRefinementFor cfg contract σ σ₀ g A I imms := by
  unfold bytesResultTrace at htrace
  split at htrace
  · exact htrace.reEquivExecutionGen hcode hd hdec hbody rfl
      (by rw [htype]; exact returnEquiv_of_encode (encodeBytesReturn _)) hfallback hreceive
  · exact htrace.reEquivExecutionRevert hcode hd hdec hbody hfallback hreceive
  · exact htrace.reEquivStaticHalt hcode hd hdec hbody hfallback hreceive
  · contradiction

end Benchmarks.UniswapV4PoolManager
