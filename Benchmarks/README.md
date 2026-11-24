# Benchmarks

Real-world contracts used to evaluate the framework at scale. The layout tracks completed proofs,
active proof targets, and prepared scaffolds:

- **This directory** holds completed proofs (top-level `…ContractCorrect` theorem, no `sorry`)
  and targets promoted for active proof work. Their status is listed separately below.
- **`Scaffolds/`** holds benchmarks that are prepared for proving but not yet
  proved: the Stele specification, the exact compiled bytecode, the verified
  jump-destination table, and the top-level theorem statements (as `sorry`
  stubs) are checked in and compile (`lake build Benchmarks.Scaffolds`), so a
  proving agent can start immediately. NOte that the specification may need 
  further adjustments to match the bytecode exactly.

Sizes are bytes of checked-in `runtime.hex`.

## Completed

`import Benchmarks` exposes all 35 completed benchmark correctness modules. The tables below
list their whole-contract certificates; the unfinished scaffolds remain separate.

| Benchmark | Upstream source | solc | Runtime bytes | Top-level theorem |
|---|---|---|---|---|
| `Auction` | [Nouns auction house, `nounsDAO/nouns-monorepo`](https://github.com/nounsDAO/nouns-monorepo) | 0.8.23 | 6150 | `auctionContractCorrect` |
| `WETH9` | [`gnosis/canonical-weth`](https://github.com/gnosis/canonical-weth/blob/master/contracts/WETH9.sol) (canonical mainnet WETH) | 0.5.16 | 1763 | `weth9ContractCorrect` |
| `Dss/Dai` | [`makerdao/dss` `dai.sol`](https://github.com/makerdao/dss/blob/master/src/dai.sol) | 0.6.12 | 4011 | `daiContractCorrect` |
| `Dss/Vat` | [`makerdao/dss` `vat.sol`](https://github.com/makerdao/dss/blob/master/src/vat.sol) | 0.6.12 | 6965 | `vatContractCorrect` |
| `Dss/Vow` | [`makerdao/dss` `vow.sol`](https://github.com/makerdao/dss/blob/master/src/vow.sol) | 0.6.12 | 5150 | `vowContractCorrect` |
| `Dss/Pot` | [`makerdao/dss` `pot.sol`](https://github.com/makerdao/dss/blob/master/src/pot.sol) | 0.6.12 | 2595 | `potContractCorrect` |
| `Dss/Jug` | [`makerdao/dss` `jug.sol`](https://github.com/makerdao/dss/blob/master/src/jug.sol) | 0.6.12 | 2440 | `jugContractCorrect` |
| `Dss/Spot` | [`makerdao/dss` `spot.sol`](https://github.com/makerdao/dss/blob/master/src/spot.sol) | 0.6.12 | 2178 | `spotContractCorrect` |
| `Dss/Cat` | [`makerdao/dss` `cat.sol`](https://github.com/makerdao/dss/blob/master/src/cat.sol) | 0.6.12 | 3873 | `catContractCorrect` |
| `Dss/Dog` | [`makerdao/dss` `dog.sol`](https://github.com/makerdao/dss/blob/master/src/dog.sol) | 0.6.12 | 4745 | `dogContractCorrect` |
| `Dss/Cure` | [`makerdao/dss` `cure.sol`](https://github.com/makerdao/dss/blob/master/src/cure.sol) | 0.6.12 | 3875 | `cureContractCorrect` |
| `Dss/End` | [`makerdao/dss` `end.sol`](https://github.com/makerdao/dss/blob/master/src/end.sol) | 0.6.12 | 10265 | `endContractCorrect` |
| `Dss/Flapper` | [`makerdao/dss` `flap.sol`](https://github.com/makerdao/dss/blob/master/src/flap.sol) | 0.6.12 | 5008 | `flapperContractCorrect` |
| `Dss/Flipper` | [`makerdao/dss` `flip.sol`](https://github.com/makerdao/dss/blob/master/src/flip.sol) | 0.6.12 | 6386 | `flipperContractCorrect` |
| `Dss/Flopper` | [`makerdao/dss` `flop.sol`](https://github.com/makerdao/dss/blob/master/src/flop.sol) | 0.6.12 | 4780 | `flopperContractCorrect` |
| `Dss/GemJoin` | [`makerdao/dss` `join.sol`](https://github.com/makerdao/dss/blob/master/src/join.sol) | 0.6.12 | 2022 | `gemJoinContractCorrect` |
| `Dss/DaiJoin` | [`makerdao/dss` `join.sol`](https://github.com/makerdao/dss/blob/master/src/join.sol) | 0.6.12 | 1733 | `daiJoinContractCorrect` |
| `Dss/LinearDecrease` | [`makerdao/dss` `abaci.sol`](https://github.com/makerdao/dss/blob/master/src/abaci.sol) | 0.6.12 | 1128 | `linearDecreaseContractCorrect` |
| `Dss/StairstepExponentialDecrease` | [`makerdao/dss` `abaci.sol`](https://github.com/makerdao/dss/blob/master/src/abaci.sol) | 0.6.12 | 1433 | `stairstepExponentialDecreaseContractCorrect` |
| `Dss/ExponentialDecrease` | [`makerdao/dss` `abaci.sol`](https://github.com/makerdao/dss/blob/master/src/abaci.sol) | 0.6.12 | 1321 | `exponentialDecreaseContractCorrect` |

Additional completed proofs:

| Benchmark | Top-level theorem |
|---|---|
| `Dss/Clipper` | `clipperContractCorrect` |
| `EAS/Attester` | `attesterContractCorrect` |
| `EAS/EAS` | `easContractCorrect` |
| `CompoundIII/Comet` | `cometWithExtendedAssetListContractCorrect` |
| `CurveVault` | `vaultContractCorrect` |
| `Morpho/MorphoBlue` | `morphoContractCorrect` |
| `UniswapV3/Pool` | `uniswapV3PoolContractCorrect` |
| `UniswapV4PoolManager` | `poolManagerContractCorrect` |
| `Safe/Main` | `safeContractCorrect` |
| `Safe/Runs1e6` | `safeContractCorrect` |
| `Safe/V0_cdb2eb5` | `safeContractCorrect` |
| `Safe/V1_0227664` | `safeContractCorrect` |
| `Safe/V2_0e91d99` | `safeContractCorrect` |
| `Safe/V3_77901a5` | `safeContractCorrect` |
| `Safe/ViaIR` | `safeContractCorrect` |

## Scaffolds

| Benchmark | Upstream source | solc | Runtime bytes |
|---|---|---|---|
| `Scaffolds/Klima` | [`KlimaDAO/klimadao-solidity`](https://github.com/KlimaDAO/klimadao-solidity/blob/0eb4770c1e9cbead8dd23ef0c23a9a27d761d029/src/protocol/tokens/regular/KlimaToken.sol) | 0.7.5 | 6975 |
| `Scaffolds/ERC721` | Benchmark-local compact ERC721 core ([`ERC721.sol`](Scaffolds/ERC721/ERC721.sol)) | 0.8.35 | 1482 |
| `Scaffolds/CometRewards` | [`compound-finance/comet`](https://github.com/compound-finance/comet/blob/f766f51583c23acc33b2a7824654ef2029a96804/contracts/CometRewards.sol) | 0.8.15 via-IR | 4063 |
| `Scaffolds/Comet` | [`compound-finance/comet`](https://github.com/compound-finance/comet/blob/f766f51583c23acc33b2a7824654ef2029a96804/contracts/Comet.sol) | 0.8.15 via-IR | 18655 |
| `Scaffolds/VestingWallet` | [OpenZeppelin `VestingWallet.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/finance/VestingWallet.sol) | 0.8.35 | 2277 |
| `Scaffolds/TimelockController` | [OpenZeppelin `TimelockController.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/governance/TimelockController.sol) | 0.8.35 | 6509 |
| `Scaffolds/UniswapV3Pool` | [`Uniswap/v3-core`](https://github.com/Uniswap/v3-core/blob/d0831dc6b8a318df3872b6d68f6de135c9f3ec29/contracts/UniswapV3Pool.sol) | 0.7.6 | 22142 |
| `Scaffolds/UniswapV2Router02` | [`Uniswap/v2-periphery`](https://github.com/Uniswap/v2-periphery/blob/ed24991304291297c3b4a52818d02f46a17aa9a2/contracts/UniswapV2Router02.sol) | 0.6.6 | 21955 |

`Scaffolds/CompoundIII/` and `Scaffolds/OpenZeppelinBench/` hold source closures shared by the
respective scaffolds.

## File conventions

Each benchmark directory contains:

- `Spec.lean` — the Stele contract: storage layout, transitions, typed external-call hooks.
- `SpecSyntax.lean` — the same spec in Solidity-like surface syntax, proved equal to `Spec.lean`.
- `Bytecode.lean` — the compiled bytecode: a kernel-checked listing of the runtime (with
  `CreationBytecode.lean` for the creation code), as `scripts/scaffold.py lean` writes it: a
  `listing_from_hex` command that decodes `runtime.hex` (pinned by its SHA-256) when the file is
  built; `#print_listing <Module>.Listing.table` shows the instructions.
- `Selectors.lean` — proofs of concrete 4-byte function selectors.
- `Constructor.lean` / `Correct.lean` — constructor and runtime equivalence; `…ContractCorrect`
  bundles both. Scaffolds and active proof targets retain `sorry` for unfinished obligations.
- Artifacts: `runtime.hex`, `creation.hex`, `*.abi.json`, `*.storage.json`, `sources.sha256`
  (pins the upstream sources), and `contracts/` (the exact source closure used to reproduce the
  bytecode). Compiler version and flags are recorded per benchmark in its own `README.md` where
  present.
