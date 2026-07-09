import Benchmarks.Dss.Clipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperFileAddressBody (v : ClipperImmutables) {code : ByteArray}
    (_hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = code) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (clipperSelBytes 10))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

end Benchmarks.Dss.Clipper
