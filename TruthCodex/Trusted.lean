import TruthCodex.Theory

/-!
# Trusted concrete hash facts

Temporary trusted key-value facts for opaque FFI computations.  Keep this file small:
each axiom should be a concrete input/output pair, not a semantic shortcut.
-/

/-- The Solidity ABI selector for `truth()`. -/
def trustedTruthSelector : ByteArray :=
  ByteArray.mk #[0x9e, 0x9f, 0x51, 0xd2]

/-- Trusted Keccak key-value pair:
`keccak256("truth()")[0:4] = 0x9e9f51d2`.
-/
axiom trustedKeccak_truth :
    (ffi.KEC (String.toByteArray "truth()")).extract 0 4 = trustedTruthSelector
