import Benchmarks.Scaffolds.EAS.Attester.Bytecode
import Reasoning.Dispatch

/-!
# EAS Attester trusted selector facts

The four declarations here are the local ABI selector facts for Attester's public entry points.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

abbrev attesterMultiRevokeSelBytes : ByteArray := ⟨#[0x13, 0xfd, 0xe5, 0x50]⟩
abbrev attesterMultiAttestSelBytes : ByteArray := ⟨#[0x54, 0xe1, 0xdb, 0x35]⟩
abbrev attesterAttestSelBytes : ByteArray := ⟨#[0x72, 0xb9, 0x96, 0x6d]⟩
abbrev attesterRevokeSelBytes : ByteArray := ⟨#[0xc2, 0x66, 0x46, 0x10]⟩

/-- Selector fact: `keccak256("attest(bytes32,uint256)")[0:4]`. -/
axiom attestSelectorOf (v : AttesterImmutables) :
    selectorOf (attestTransition v) = attesterAttestSelBytes

/-- Selector fact: `keccak256("revoke(bytes32,bytes32)")[0:4]`. -/
axiom revokeSelectorOf (v : AttesterImmutables) :
    selectorOf (revokeTransition v) = attesterRevokeSelBytes

/-- Selector fact: `keccak256("multiAttest(bytes32[],uint256[][])")[0:4]`. -/
axiom multiAttestSelectorOf (v : AttesterImmutables) :
    selectorOf (multiAttestTransition v) = attesterMultiAttestSelBytes

/-- Selector fact: `keccak256("multiRevoke(bytes32[],bytes32[][])")[0:4]`. -/
axiom multiRevokeSelectorOf (v : AttesterImmutables) :
    selectorOf (multiRevokeTransition v) = attesterMultiRevokeSelBytes

end Benchmarks.EAS.Attester
