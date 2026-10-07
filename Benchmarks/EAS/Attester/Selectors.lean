import Benchmarks.EAS.Attester.Bytecode
import Reasoning.Dispatch

/-!
# EAS Attester selector proofs

The four theorems identify Attester's public ABI selectors.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

abbrev attesterMultiRevokeSelBytes : ByteArray := ⟨#[0x13, 0xfd, 0xe5, 0x50]⟩
abbrev attesterMultiAttestSelBytes : ByteArray := ⟨#[0x54, 0xe1, 0xdb, 0x35]⟩
abbrev attesterAttestSelBytes : ByteArray := ⟨#[0x72, 0xb9, 0x96, 0x6d]⟩
abbrev attesterRevokeSelBytes : ByteArray := ⟨#[0xc2, 0x66, 0x46, 0x10]⟩

/-- Selector fact: `keccak256("attest(bytes32,uint256)")[0:4]`. -/
theorem attestSelectorOf :
    selectorOf (attestTransition) = attesterAttestSelBytes := by
  native_decide

/-- Selector fact: `keccak256("revoke(bytes32,bytes32)")[0:4]`. -/
theorem revokeSelectorOf :
    selectorOf (revokeTransition) = attesterRevokeSelBytes := by
  native_decide

/-- Selector fact: `keccak256("multiAttest(bytes32[],uint256[][])")[0:4]`. -/
theorem multiAttestSelectorOf :
    selectorOf (multiAttestTransition) = attesterMultiAttestSelBytes := by
  native_decide

/-- Selector fact: `keccak256("multiRevoke(bytes32[],bytes32[][])")[0:4]`. -/
theorem multiRevokeSelectorOf :
    selectorOf (multiRevokeTransition) = attesterMultiRevokeSelBytes := by
  native_decide

end Benchmarks.EAS.Attester
