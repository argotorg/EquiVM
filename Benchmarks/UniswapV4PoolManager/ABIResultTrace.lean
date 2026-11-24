import Benchmarks.UniswapV4PoolManager.FunctionResultTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: source function traces with an arbitrary ABI return signature.
def abiResultTrace (fork : Ethereum.Fork) (types : List ABIType) (code : ByteArray) (g : Sat256) (s0 : State) : ExecResult → Prop :=
  functionResultTrace fork code g s0 (fun post values =>
    ∃ out, RDret fork code g s0 post.accountMap out ∧ returnEquiv out values types)

theorem abiResultTrace_refinement {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : UInt256} {code : ByteArray} {args imms : Store} {result : ExecResult}
    (hcode : I.code = code) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody fork cfg contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) args t.body result imms)
    (htrace : abiResultTrace fork t.returnType code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) result)
    (hfallback : contract.fallback = none) (hreceive : contract.receive = none) :
    runtimeRefinementFor fork cfg contract σ σ₀ g A I imms := by
  cases result with
  | returned f post values =>
      obtain ⟨out, hr, he⟩ := htrace
      exact hr.reEquivExecutionGen hcode hd hdec hbody rfl he hfallback hreceive
  | reverted => exact htrace.reEquivExecutionRevert hcode hd hdec hbody hfallback hreceive
  | staticViolation => exact htrace.reEquivStaticHalt hcode hd hdec hbody hfallback hreceive
  | ok | «break» | «continue» | noMatch | decodingFailed => exact False.elim htrace

end Benchmarks.UniswapV4PoolManager
