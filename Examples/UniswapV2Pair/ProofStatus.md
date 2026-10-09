# Uniswap V2 Pair proof status

Constructor and runtime refinement are complete: `uniswapV2PairCorrect` (runtime) and
`uniswapV2PairContractCorrect` (creation and runtime) in `Correct.lean`, with no `sorry`.

`Bytecode.lean` proves the 27 selector values by reducing the pure Keccak function in the Lean
kernel. `ConstructorHashes.lean` proves the two compiler-precomputed constructor hashes,
`keccak256("Uniswap V2")` and `keccak256("1")`, the same way. The constructor proof uses these
identities to relate the source domain separator to the constants embedded in the creation
bytecode. Jump-destination tables are checked with `native_decide`.

The remaining trusted dependencies come from native evaluation and EVMLean's precompile model;
the selector and constructor hash identities add none.
