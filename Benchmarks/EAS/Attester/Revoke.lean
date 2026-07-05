import Benchmarks.EAS.Attester.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-! ## `revoke(bytes32,bytes32)` -/

theorem attesterRevokeBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

end Benchmarks.EAS.Attester
