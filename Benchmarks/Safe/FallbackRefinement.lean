import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES reEquiv_receiveExecution to fallback dispatch and its return convention.
theorem reEquivFallbackExecution {cfg : Config} {c : ContractDecl} {imms : Store}
    {σ σ₀ A I t args result convention} {g : UInt256}
    (hd : selectorDispatchMsg c I.calldata = none)
    (hr : receiveDispatchMsg c I.calldata = none) (hf : c.fallback = some t)
    (ha : fallbackCallargs I.calldata t.params = some args)
    (hc : fallbackReturnConvention t = some convention)
    (hbody : ExecTransitionBody cfg c (initState σ σ₀ (.ofUInt256 g) A I)
      args t.body result imms)
    (hequiv : execResultsEquiv (Ξ σ σ₀ g A I) result convention) :
    runtimeRefinementFor cfg c σ σ₀ g A I imms :=
  .execution rfl (.fallback hd hr hf ha hc rfl hbody) hequiv

end Benchmarks.Safe
