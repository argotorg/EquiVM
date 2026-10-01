import Benchmarks.Scaffolds.EAS.Attester.Bytecode
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
theorem attestSelectorOf (v : AttesterImmutables) :
    selectorOf (attestTransition v) = attesterAttestSelBytes := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, attestTransition,
    bytes32, bytes32Width, uint256, uint256Int]
  decide +kernel

/-- Selector fact: `keccak256("revoke(bytes32,bytes32)")[0:4]`. -/
theorem revokeSelectorOf (v : AttesterImmutables) :
    selectorOf (revokeTransition v) = attesterRevokeSelBytes := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, revokeTransition, bytes32, bytes32Width]
  decide +kernel

/-- Selector fact: `keccak256("multiAttest(bytes32[],uint256[][])")[0:4]`. -/
theorem multiAttestSelectorOf (v : AttesterImmutables) :
    selectorOf (multiAttestTransition v) = attesterMultiAttestSelBytes := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, multiAttestTransition,
    bytes32, bytes32Width, bytes32Array, uint256, uint256Int, uint256Array, uint256NestedArray]
  decide +kernel

/-- Selector fact: `keccak256("multiRevoke(bytes32[],bytes32[][])")[0:4]`. -/
theorem multiRevokeSelectorOf (v : AttesterImmutables) :
    selectorOf (multiRevokeTransition v) = attesterMultiRevokeSelBytes := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, revokeTransition, multiRevokeTransition,
    bytes32, bytes32Width, bytes32Array, bytes32NestedArray]
  decide +kernel

end Benchmarks.EAS.Attester
