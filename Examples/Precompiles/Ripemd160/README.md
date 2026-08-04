# RIPEMD-160 bytecode proof

This directory verifies the optimized RIPEMD-160 implementation as a precompile-style bytecode
program, directly against a pure Lean model. It is independent of the Solm refinement proof in
`Examples/Ripemd160`.

The public entry point is `Correct.lean`. Its main theorem is
`Ripemd160.ripemd160BytecodeSpec`, stated directly using `Reasoning.Reach.BytecodeSpec`. For
accepted execution environments, the bytecode returns `Ripemd160.Model.rawOutput` of the calldata
when enough gas is supplied, consumes exactly `Ripemd160.ripemd160GasCost`, and reports out-of-gas
exactly below that threshold. `Ripemd160.ripemd160BytecodeExactGas` is the stronger specialized
theorem used to establish this final interface result.

The implementation bytecode is pinned in `Bytecode.lean`. `HashModel.lean` contains the pure model;
the remaining files prove the parser, compression loops, memory representation, final output, and
exact gas trace. Compiler source and generated artifacts remain beside the separate contract/Solm
example in `Examples/Ripemd160`.
