# Examples

Contracts used to develop and exercise the framework. Each directory holds one contract:
its Sol⁻ specification (`Spec.lean`, with Solidity-like surface syntax in `SpecSyntax.lean`),
the exact compiled bytecode as a Lean byte array (`Bytecode.lean`), and the refinement proof,
assembled in `Correct.lean`. The top-level theorem of each example is named in the table.

All proofs are complete except `UniswapV2Pair` (see status column).

| Example | Source | Compiler | Top-level theorem |
|---|---|---|---|
| `Truth` | Hand-written one-getter contract | solc 0.8.35, optimizer off, Shanghai | `truthCorrect` |
| `Pow` | Hand-written loop (exponentiation) | solc 0.8.35, optimizer off, Shanghai | `powCorrect` |
| `Caller` | Hand-written external-call contract | solc 0.8.35, optimizer off, Shanghai | `callerCorrect` |
| `CtorTruth` | `Truth` plus its real solc constructor | solc 0.8.35, `--no-cbor-metadata`, Shanghai | `ctorTruthRuntimeCorrect` |
| `CtorStore` | Hand-written minimal initcode storing one word | solc 0.8.35 runtime, hand-written creation bytecode | `ctorStoreRuntimeCorrect` |
| `ERC20` | Minimal hand-written ERC20 | solc 0.8.35, optimizer off, Shanghai | `erc20Correct` |
| `VyperERC20` | Hand-written Vyper version of the minimal ERC20 | vyper 0.4.3 | `runtimeCorrect` |
| `StringStoreLite` | Hand-written string-storage contract | solc 0.8.35, optimizer off, Shanghai | `stringStoreLiteCorrect` |
| `TinyImmutable` | Hand-written immutables contract | solc 0.8.35, standard-json | `tinyImmutableCorrect` |
| `Reuse` | Two functions sharing a code block | solc 0.8.35, optimizer on, Shanghai | `cCorrect` |
| `Ballot` | [Solidity docs: Voting](https://docs.soliditylang.org/en/latest/solidity-by-example.html#voting) | solc 0.8.35, optimizer on, Shanghai | `ballotCorrect` |
| `SimpleAuction` | [Solidity docs: Simple Open Auction](https://docs.soliditylang.org/en/latest/solidity-by-example.html#simple-open-auction) | solc 0.8.35, optimizer on, Shanghai | `simpleAuctionCorrect` |
| `BlindAuction` | [Solidity docs: Blind Auction](https://docs.soliditylang.org/en/latest/solidity-by-example.html#blind-auction) | solc 0.8.35, optimizer on, Shanghai | `blindAuctionCorrect` |
| `OpenZeppelinBench/Ownable2Step` | [OpenZeppelin `Ownable2Step.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/access/Ownable2Step.sol) (master snapshot, 2026-06-23) | solc 0.8.35, optimizer on, Shanghai | `ownable2StepCorrect` |
| `OpenZeppelinBench/AccessControl` | [OpenZeppelin `AccessControl.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/access/AccessControl.sol) (same snapshot) | solc 0.8.35, optimizer on, Shanghai | `accessControlCorrect` |
| `OpenZeppelinBench/Pausable` | [OpenZeppelin `Pausable.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/utils/Pausable.sol) (same snapshot) | solc 0.8.35, optimizer on, Shanghai | `pausableCorrect` |
| `OpenZeppelinBench/ERC6909` | [OpenZeppelin `ERC6909.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC6909/ERC6909.sol) (same snapshot) | solc 0.8.35, optimizer on, Shanghai | `erc6909Correct` |
| `UniswapV2Pair` | [`Uniswap/v2-core` `v1.0.1`](https://github.com/Uniswap/v2-core/blob/v1.0.1/contracts/UniswapV2Pair.sol) | solc 0.5.16, optimizer on (200 runs) | `uniswapV2PairCorrect` — **in progress** |
| `Ripemd160` | Pure Solidity RIPEMD-160 precompile replacement | solc 0.8.35, via IR, optimizer on (10,000 runs), Osaka | `ripemd160Correct` |
| `Ripemd160Old` | Original pure Solidity RIPEMD-160 precompile replacement | solc 0.8.35, via IR, optimizer off, Osaka | `ripemd160OldCorrect` |

Precompile-style bytecode proofs that do not refine a Sol⁻ contract live under `Precompiles/`.
`Precompiles/Ripemd160` proves `ripemd160BytecodeSpec`, relating the optimized runtime directly to
the pure Lean RIPEMD-160 function with an exact gas cost and OOG threshold through the generic
`BytecodeSpec` interface. The sibling
`Ripemd160` directory retains only its Solm specification and equivalence layer.

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
