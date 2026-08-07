# Precompile-style bytecode proofs

This tree contains bytecode verification examples whose public specification is a pure Lean
function rather than a Sol⁻ contract.  The common interface lives in `Reasoning/Bytecode.lean`.
It states properties at the caller-visible bytecode boundary: successful valid inputs return a pure
output with exact bytecode gas, while invalid precompile-style inputs fail.

Contract-to-Solm equivalence layers, when present for the same implementation, live in sibling
example directories and are not part of these precompile-style specs.

## Current examples

- `Identity`: proves the seven-byte `evmification` replacement returns calldata unchanged with
  exact copy and memory-expansion gas.

- `Ripemd160`: proves the optimized Solidity implementation against the pure RIPEMD-160 model with
  exact gas for the complete successful trace.

- `Modexp`: proves selected paths against the EEST-tested `evm-semantics` model.  The complete
  single-word implementation and the arbitrary-width exponent-zero/base-zero/base-one paths have
  exact gas specifications.  The shared byte-array zero scans used by the general implementations
  are verified against the trusted padded parser with branch-sensitive exact gas.  The remaining
  Barrett and Montgomery arithmetic paths are still under development.

- `Blake2f`: complete.  The final theorem is:

  ```lean
  Blake2f.bytecodeSpec : bytecodeSpecTarget bytecodeGasCost
  ```

  This proves the deployed replacement bytecode against the trusted pure BLAKE2F model, with exact
  bytecode-specific gas.  The proof covers both zero-round and arbitrary positive-round valid
  inputs, and the invalid-input failure behavior for invalid length or final flag.  The local
  Solidity proof target was tightened to match EIP-152/native precompile behavior: final flag must
  be `0` or `1`, and explicit validation failures use `INVALID` rather than `REVERT` so that the
  caller-visible `Θ` observation matches the native precompile failure shape.
