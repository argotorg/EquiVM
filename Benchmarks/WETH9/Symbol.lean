import Benchmarks.WETH9.Routines

/-! # WETH9 `Symbol` refinement (scaffold — proof pending) -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9

theorem weth9SymbolBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

end Benchmarks.WETH9
