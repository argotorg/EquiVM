import Benchmarks.Xxx.Spec

/-!
# Xxx selectors (TEMPLATE)

This module owns the selector-byte table used by dispatch proofs and proves each entry from the
corresponding canonical ABI signature with the pure Keccak implementation. Keep signature
normalization private or local and expose one selector theorem per transition.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Xxx

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev xxxSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order (index comments per signature). -/
def xxxSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x55, 0x24, 0x10, 0x77]⟩  -- setValue(uint256)
  | _ => ⟨#[0x3f, 0xa4, 0xf2, 0x45]⟩  -- value()

private lemma natRepr256 : Nat.repr 256 = "256" := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- `keccak("setValue(uint256)")[0:4] = 0x55241077`. -/
theorem setValueSelectorBytes :
    (Ethereum.KEC (String.toByteArray (transitionSigStr setValueTransition))).extract 0 4 =
      xxxSelBytes 0 := by
  rw [show transitionSigStr setValueTransition = "setValue(uint256)" by
    simp [setValueTransition, contract, Syntax.contractSyntax, transitionSigStr, printSignature,
      transitionSignature, abiToSigStr, elemToSigStr, intTypeToSigStr, natRepr256]
    decide +kernel]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- `keccak("value()")[0:4] = 0x3fa4f245`. -/
theorem valueSelectorBytes :
    (Ethereum.KEC (String.toByteArray (transitionSigStr valueTransition))).extract 0 4 =
      xxxSelBytes 1 := by
  rw [show transitionSigStr valueTransition = "value()" by rfl]
  decide +kernel

end Benchmarks.Xxx
