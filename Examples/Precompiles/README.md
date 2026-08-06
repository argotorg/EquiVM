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
- `Blake2f`: an experiment setup for the `evmification` BLAKE2F replacement. The Solidity source is
  copied locally and tightened to reject invalid final-flag bytes. Explicit EIP-152 validation
  failures use `INVALID`, not `REVERT`, because the bytecode spec observes Θ and `REVERT` preserves
  leftover gas. The deployed fallback now checks calldata shape before allocating `msg.data`, so
  invalid length cannot route through allocator `REVERT`. The stable patched runtime bytecode is
  compiled with metadata hash disabled, transcribed, and equipped with a valid-jump certificate;
  the invalid-input side of the `PrecompileSpec` is closed, including the bridge from the
  bytecode-decoded final-flag word to the trusted model's `calldata[212]!`. The zero-round
  valid-input branch is also closed: for valid accepted inputs with `Model.rounds calldata = 0`,
  `Correct.ZeroRounds.Return.Final.zeroRoundValidTrace` proves that the bytecode returns
  `Model.output calldata` and consumes the exact branch-specific replacement-bytecode gas
  `zeroRoundGasCost` (`10647` for final flag `0`, `10674` for final flag `1`). The positive-round
  compression-loop valid branch is still being developed.

Contract-to-Solm equivalence layers, when they exist for the same implementation, remain in their
ordinary sibling example directories.
