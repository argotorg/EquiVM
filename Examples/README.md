# Examples

Contracts used to develop and exercise the framework. Each directory holds one contract:
its Sol⁻ specification (`Spec.lean`, with Solidity-like surface syntax in `SpecSyntax.lean`),
the exact compiled bytecode as a Lean byte array (`Bytecode.lean`), and the refinement proof,
assembled in `Correct.lean`. The top-level theorem of each example is named in the table.

All proofs are complete except `UniswapV2Pair` (see status column).

| Example | Source | Compiler | Top-level theorem |
|---|---|---|---|
| `Truth` | Hand-written one-getter contract | solc, optimizer off, Shanghai | `truthCorrect` |
| `Pow` | Hand-written loop (exponentiation) | solc, optimizer off, Shanghai | `powCorrect` |
| `Caller` | Hand-written external-call contract | solc, optimizer off, Shanghai | `callerCorrect` |
| `CtorTruth` | `Truth` plus its real solc constructor | solc, `--no-cbor-metadata`, Shanghai | `ctorTruthRuntimeCorrect` |
| `CtorStore` | Hand-written minimal initcode storing one word | hand-written creation bytecode | `ctorStoreRuntimeCorrect` |
| `ERC20` | Minimal hand-written ERC20 | solc, optimizer off, Shanghai | `erc20Correct` |
| `VyperERC20` | ERC20 in Vyper | vyper 0.4.3 | `runtimeCorrect` |
| `StringStoreLite` | Hand-written string-storage contract | solc, optimizer off, Shanghai | `stringStoreLiteCorrect` |
| `TinyImmutable` | Hand-written immutables contract | solc 0.8.35, standard-json | `tinyImmutableCorrect` |
| `Reuse` | Two functions sharing a code block | solc 0.8.35, optimizer on, Shanghai | `cCorrect` |
| `Ballot` | Solidity documentation example | solc 0.8.35, optimizer on, Shanghai | `ballotCorrect` |
| `SimpleAuction` | Solidity documentation example | solc 0.8.35, optimizer on, Shanghai | `simpleAuctionCorrect` |
| `BlindAuction` | Solidity documentation example | solc 0.8.35, optimizer on, Shanghai | `blindAuctionCorrect` |
| `OpenZeppelinBench/Ownable2Step` | OpenZeppelin Contracts (master snapshot, 2026-06-23) | solc, optimizer on, Shanghai | `ownable2StepCorrect` |
| `OpenZeppelinBench/AccessControl` | OpenZeppelin Contracts (same snapshot) | solc, optimizer on, Shanghai | `accessControlCorrect` |
| `OpenZeppelinBench/Pausable` | OpenZeppelin Contracts (same snapshot) | solc, optimizer on, Shanghai | `pausableCorrect` |
| `OpenZeppelinBench/ERC6909` | OpenZeppelin Contracts (same snapshot) | solc, optimizer on, Shanghai | `erc6909Correct` |
| `UniswapV2Pair` | Unmodified `Uniswap/v2-core` tag `v1.0.1` | solc 0.5.16, optimizer on (200 runs) | `uniswapV2PairCorrect` — **in progress** |

## File conventions

- `Spec.lean` — the Sol⁻ contract: storage layout, transitions, external-call hooks.
- `SpecSyntax.lean` — the same spec in Solidity-like surface syntax, proved equal to `Spec.lean`.
- `Bytecode.lean` — the compiled bytecode as a byte array, with the compiler invocation recorded
  in the header, plus the verified jump-destination table.
- `Correct.lean` — the top-level theorem; per-function proofs live in sibling files.
- `.sol`/`.vy` sources are checked in next to the Lean files.

## Trusted base

Concrete keccak values cannot be computed inside Lean (`ffi.keccak256` is an opaque extern
function), so each contract's 4-byte function selectors are stated as per-contract axioms
(in `Bytecode.lean` or `Trusted.lean`). Jump-destination tables are verified with
`native_decide`, which trusts the Lean compiler.
