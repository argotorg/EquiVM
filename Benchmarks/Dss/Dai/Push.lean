import Benchmarks.Dss.Dai.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Dai

/-- `push(address,uint256)` body refines its Solm transition. -/
theorem daiPushBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (daiSelBytes 14))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

end Benchmarks.Dss.Dai
