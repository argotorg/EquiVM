# Precompile-style bytecode proofs

This tree contains bytecode verification examples whose public specification is a pure Lean
function rather than a Sol⁻ contract. Each example may supply an acceptance predicate, output
function, and exact gas term through the generic interface in `Reasoning/Bytecode.lean`.

Current examples:

- `Identity`: the seven-byte `evmification` replacement, returning calldata unchanged with exact
  copy and memory-expansion gas.
- `Ripemd160`: the optimized Solidity implementation, proved against a pure RIPEMD-160 model with
  exact gas for its complete successful trace.
- `Modexp`: a direct proof against the EEST-tested `evm-semantics` model. The complete single-word
  implementation and the arbitrary-width exponent-zero/base-zero/base-one paths have exact gas
  specifications. The shared memory byte-array zero scan used by both general implementations is
  zero and one byte-array scans used by both general implementations are also verified against the
  trusted padded parser with branch-sensitive exact gas; the remaining Barrett and Montgomery
  arithmetic paths are still being developed.
