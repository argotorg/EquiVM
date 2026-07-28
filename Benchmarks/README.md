# Benchmarks

Real-world contracts used to evaluate the framework at scale. The layout separates finished work
from prepared targets:

- **This directory** holds benchmarks whose refinement proof is complete (top-level
  `…ContractCorrect` theorem, no `sorry`), with one exception noted below.
- **`Scaffolds/`** holds benchmarks that are prepared for proving but not yet
  proved: the Sol⁻ specification, the exact compiled bytecode, the verified
  jump-destination table, and the top-level theorem statements (as `sorry`
  stubs) are checked in and compile (`lake build Benchmarks.Scaffolds`), so a
  proving agent can start immediately. NOte that the specification may need 
  further adjustments to match the bytecode exactly.

Sizes are bytes of checked-in `runtime.hex`.

## Completed

| Benchmark | Upstream source | solc | Runtime bytes | Top-level theorem |
|---|---|---|---|---|
| `WETH9` | Canonical mainnet WETH | 0.5.16 | 1763 | `weth9ContractCorrect` |
| `Dss/Dai` | MakerDAO `makerdao/dss` | 0.6.12 | 4011 | `daiContractCorrect` |
| `Dss/Vat` | MakerDAO `makerdao/dss` | 0.6.12 | 6965 | `vatContractCorrect` |
| `Dss/Vow` | MakerDAO `makerdao/dss` | 0.6.12 | 5150 | `vowContractCorrect` |
| `Dss/Pot` | MakerDAO `makerdao/dss` | 0.6.12 | 2595 | `potContractCorrect` |
| `Dss/Jug` | MakerDAO `makerdao/dss` | 0.6.12 | 2440 | `jugContractCorrect` |
| `Dss/Spot` | MakerDAO `makerdao/dss` | 0.6.12 | 2178 | `spotContractCorrect` |
| `Dss/Cat` | MakerDAO `makerdao/dss` | 0.6.12 | 3873 | `catContractCorrect` |
| `Dss/Dog` | MakerDAO `makerdao/dss` | 0.6.12 | 4745 | `dogContractCorrect` |
| `Dss/Cure` | MakerDAO `makerdao/dss` | 0.6.12 | 3875 | `cureContractCorrect` |
| `Dss/End` | MakerDAO `makerdao/dss` | 0.6.12 | 10265 | `endContractCorrect` |
| `Dss/Flapper` | MakerDAO `makerdao/dss` | 0.6.12 | 5008 | `flapperContractCorrect` |
| `Dss/Flipper` | MakerDAO `makerdao/dss` | 0.6.12 | 6386 | `flipperContractCorrect` |
| `Dss/Flopper` | MakerDAO `makerdao/dss` | 0.6.12 | 4780 | `flopperContractCorrect` |
| `Dss/GemJoin` | MakerDAO `makerdao/dss` (`join.sol`) | 0.6.12 | 2022 | `gemJoinContractCorrect` |
| `Dss/DaiJoin` | MakerDAO `makerdao/dss` (`join.sol`) | 0.6.12 | 1733 | `daiJoinContractCorrect` |
| `Dss/LinearDecrease` | MakerDAO `makerdao/dss` (`abaci.sol`) | 0.6.12 | 1128 | `linearDecreaseContractCorrect` |
| `Dss/StairstepExponentialDecrease` | MakerDAO `makerdao/dss` (`abaci.sol`) | 0.6.12 | 1433 | `stairstepExponentialDecreaseContractCorrect` |
| `Dss/ExponentialDecrease` | MakerDAO `makerdao/dss` (`abaci.sol`) | 0.6.12 | 1321 | `exponentialDecreaseContractCorrect` |
| `Dss/Clipper` | MakerDAO `makerdao/dss` | 0.6.12 | 9360 | `clipperContractCorrect` — **in progress**|

`Dss/Clipper` stays here rather than in `Scaffolds/` because it completes the Dss suite and its
proof is substantially under way.

## Scaffolds

| Benchmark | Upstream source | solc | Runtime bytes |
|---|---|---|---|
| `Scaffolds/Safe` | Safe (Gnosis Safe) | 0.8.35 | 11874 |
| `Scaffolds/Klima` | KlimaDAO `KlimaToken` | 0.7.5 | 6975 |
| `Scaffolds/Auction` | Nouns auction house | 0.8.23 | 6150 |
| `Scaffolds/ERC721` | Compact ERC721 core | 0.8.35 | 1482 |
| `Scaffolds/EAS/Attester` | Ethereum Attestation Service | 0.8.26 | 3186 |
| `Scaffolds/CometRewards` | Compound III | 0.8.15 via-IR | 4063 |
| `Scaffolds/Comet` | Compound III | 0.8.15 via-IR | 18655 |
| `Scaffolds/VestingWallet` | OpenZeppelin Contracts | 0.8.35 | 2277 |
| `Scaffolds/TimelockController` | OpenZeppelin Contracts | 0.8.35 | 6509 |
| `Scaffolds/UniswapV3Pool` | `Uniswap/v3-core` | 0.7.6 | 22142 |
| `Scaffolds/UniswapV2Router02` | `Uniswap/v2-periphery` | 0.6.6 | 21955 |

`Scaffolds/CompoundIII/` and `Scaffolds/OpenZeppelinBench/` hold source closures shared by the
respective scaffolds.

## File conventions

Each benchmark directory contains:

- `Spec.lean` — the Sol⁻ contract: storage layout, transitions, typed external-call hooks.
- `SpecSyntax.lean` — the same spec in Solidity-like surface syntax, proved equal to `Spec.lean`.
- `Bytecode.lean` — the compiled creation/runtime bytecode as Lean byte arrays with the verified
  jump-destination table.
- `Trusted.lean` — the per-contract trusted base: the contract's 4-byte function selectors as
  axioms (concrete keccak values cannot be computed inside Lean; `ffi.keccak256` is an opaque
  extern function), plus occasional data-slot constants of the same kind.
- `Constructor.lean` / `Correct.lean` — constructor and runtime equivalence; `…ContractCorrect`
  bundles both. In `Scaffolds/` these are `sorry` stubs.
- Artifacts: `runtime.hex`, `creation.hex`, `*.abi.json`, `*.storage.json`, `sources.sha256`
  (pins the upstream sources), and `contracts/` (the exact source closure used to reproduce the
  bytecode). Compiler version and flags are recorded per benchmark in its own `README.md` where
  present.
