# Uniswap V2 Pair proof status

Constructor and runtime refinement are complete: `uniswapV2PairCorrect` (runtime) and
`uniswapV2PairContractCorrect` (creation and runtime) in `Correct.lean`, with no `sorry`.
Verified on 2026-09-07 with `lake build Examples.UniswapV2Pair.Correct` and a build of all
316 modules in this directory.

Trusted facts beyond the standard set: the 27 selector axioms in `Bytecode.lean` and the two
compiler-precomputed Keccak constants in `Trusted.lean`, `keccak256("Uniswap V2")` and
`keccak256("1")`. The constructor proof uses them to relate the source domain separator to
the constants embedded in the creation bytecode; the type-string hash and the final domain
hash are coupled symbolically through the Keccak semantics.

| Axiom category | `uniswapV2PairCorrect` | `uniswapV2PairContractCorrect` |
|---|---:|---:|
| Native evaluation facts (`native_decide`) | 11194 | 11382 |
| Standard logical axioms | 3 | 3 |
| Selector facts | 27 | 27 |
| Precompile output-size facts (EVMLean) | 7 | 7 |
| `keccak_size` | 1 | 1 |
| Constructor Keccak constants | 0 | 2 |
| Total | 11232 | 11422 |
