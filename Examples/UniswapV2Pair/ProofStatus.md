# Uniswap V2 Pair proof status

Constructor and runtime refinement are complete under `Misc/prompt.md`, with the two
additional fixed Keccak facts explicitly authorized by the user.

Verified on 2026-09-07:

- `lake build Examples.UniswapV2Pair.Correct` passed:
  `Build completed successfully (3768 jobs).`
- The build covering all 316 local Lean modules passed:
  `Build completed successfully (3784 jobs).`
- The proof-hole scan returned no matches (exit 1).
- Both top-level theorems have no `sorryAx` or unexpected axiom dependencies.
- Every local Lean file is at most 2000 lines; the largest is 1995 lines.
- The 965 declaration headers involved in the file split are preserved.
- The scratch file was removed.

The two new trusted statements in [Trusted.lean](Trusted.lean) are exactly the
compiler-precomputed evaluations of `keccak256("Uniswap V2")` and `keccak256("1")`.
The constructor proof uses them when relating the source domain separator to the
bytecode's embedded constants. Its type-string hash and final domain hash are coupled
symbolically through the existing Keccak semantics.

| Axiom category | Runtime theorem | Constructor/runtime theorem |
|---|---:|---:|
| Native evaluation facts | 11194 | 11382 |
| Standard logical axioms | 3 | 3 |
| Existing selector facts | 27 | 27 |
| Existing precompile output-size facts | 7 | 7 |
| Existing `keccak_size` | 1 | 1 |
| Authorized constructor hash facts | 0 | 2 |
| Total | 11232 | 11422 |

The constructor is factored into entry, memory, hash, source, storage, return, and
coupling modules. `PackedWordSource.lean` shares packed ABI helpers with Permit.
Oversized Common, Permit, Mint, Sync, and Skim files were split by concern while
preserving their public interfaces. Skim now uses one masked-address proof for both
canonical and noncanonical input words.

Verbatim validation commands and output: `/tmp/uniswap-final-validation.txt`.
Full axiom lists: `/tmp/uniswap-final-axioms.txt`.
Structured axiom summary: `/tmp/uniswap-final-axiom-summary.json`.
Build covering all local modules: `/tmp/uniswap-all-modules-build.log`.
