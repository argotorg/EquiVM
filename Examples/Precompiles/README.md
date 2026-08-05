# Precompile-style bytecode proofs

This tree contains bytecode verification examples whose public specification is a pure Lean
function rather than a Sol⁻ contract. Each example may supply an acceptance predicate, output
function, and exact gas term through the generic interface in `Reasoning/Bytecode.lean`.

Current examples:

- `Identity`: the seven-byte `evmification` replacement, returning calldata unchanged with exact
  copy and memory-expansion gas.
- `Ripemd160`: the optimized Solidity implementation, proved against a pure RIPEMD-160 model with
  exact gas for its complete successful trace.
