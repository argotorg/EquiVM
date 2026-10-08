import Benchmarks.EAS.Attester.Bytecode
import Reasoning.Dispatch

/-!
# EAS Attester selector proofs

The four theorems identify Attester's public ABI selectors.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

abbrev attesterMultiRevokeSelBytes : ByteArray := ⟨#[0x13, 0xfd, 0xe5, 0x50]⟩
abbrev attesterMultiAttestSelBytes : ByteArray := ⟨#[0x54, 0xe1, 0xdb, 0x35]⟩
abbrev attesterAttestSelBytes : ByteArray := ⟨#[0x72, 0xb9, 0x96, 0x6d]⟩
abbrev attesterRevokeSelBytes : ByteArray := ⟨#[0xc2, 0x66, 0x46, 0x10]⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Selector fact: `keccak256("attest(bytes32,uint256)")[0:4]`. -/
theorem attestSelectorOf :
    selectorOf (attestTransition) = attesterAttestSelBytes := by
  have hsig : transitionSigStr attestTransition = "attest(bytes32,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature,
      attestTransition, contract, Syntax.contractSyntax, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr,
      show Nat.repr 256 = "256" by decide +kernel,
      show Nat.repr 32 = "32" by decide +kernel]
    decide +kernel
  unfold selectorOf
  rw [hsig]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Selector fact: `keccak256("revoke(bytes32,bytes32)")[0:4]`. -/
theorem revokeSelectorOf :
    selectorOf (revokeTransition) = attesterRevokeSelBytes := by
  have hsig : transitionSigStr revokeTransition = "revoke(bytes32,bytes32)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature,
      revokeTransition, contract, Syntax.contractSyntax, ABI.abiToSigStr,
      ABI.elemToSigStr, show Nat.repr 32 = "32" by decide +kernel]
    decide +kernel
  unfold selectorOf
  rw [hsig]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Selector fact: `keccak256("multiAttest(bytes32[],uint256[][])")[0:4]`. -/
theorem multiAttestSelectorOf :
    selectorOf (multiAttestTransition) = attesterMultiAttestSelBytes := by
  have hsig : transitionSigStr multiAttestTransition = "multiAttest(bytes32[],uint256[][])" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature,
      multiAttestTransition, contract, Syntax.contractSyntax, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr,
      show Nat.repr 256 = "256" by decide +kernel,
      show Nat.repr 32 = "32" by decide +kernel]
    decide +kernel
  unfold selectorOf
  rw [hsig]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Selector fact: `keccak256("multiRevoke(bytes32[],bytes32[][])")[0:4]`. -/
theorem multiRevokeSelectorOf :
    selectorOf (multiRevokeTransition) = attesterMultiRevokeSelBytes := by
  have hsig : transitionSigStr multiRevokeTransition = "multiRevoke(bytes32[],bytes32[][])" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature,
      multiRevokeTransition, contract, Syntax.contractSyntax, ABI.abiToSigStr,
      ABI.elemToSigStr, show Nat.repr 32 = "32" by decide +kernel]
    decide +kernel
  unfold selectorOf
  rw [hsig]
  decide +kernel

end Benchmarks.EAS.Attester
