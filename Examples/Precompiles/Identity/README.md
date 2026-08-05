# Identity bytecode proof

This example verifies the seven-byte Identity implementation documented in
`evmification/src/identity/Identity.sol` directly against the pure Identity model used by the
native precompile in `evm-semantics`.

`Identity.bytecodeSpec` states the final result through `Reasoning.Reach.BytecodeSpec`: accepted
calls return their calldata unchanged, consume exactly the bytecode-specific `Identity.gasCost`,
and have an exact out-of-gas threshold.
