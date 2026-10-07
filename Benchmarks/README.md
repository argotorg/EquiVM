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
| `Dss/Clipper` | [`makerdao/dss` `clip.sol`](https://github.com/makerdao/dss/blob/master/src/clip.sol) | 0.6.12 | 9360 | `clipperContractCorrect` — **in progress**|

`Dss/Clipper` stays here rather than in `Scaffolds/` because it completes the Dss suite and its
proof is substantially under way.

## Scaffolds

| Benchmark | Upstream source | solc | Runtime bytes |
|---|---|---|---|
| `Scaffolds/Safe` | [`safe-global/safe-smart-account`](https://github.com/safe-global/safe-smart-account/blob/77901a5a1ad835b74ad3b72f73a8412cfe491c57/contracts/Safe.sol) | 0.7.6 | 20869 |
| `Scaffolds/Klima` | [`KlimaDAO/klimadao-solidity`](https://github.com/KlimaDAO/klimadao-solidity/blob/0eb4770c1e9cbead8dd23ef0c23a9a27d761d029/src/protocol/tokens/regular/KlimaToken.sol) | 0.7.5 | 7110 |
| `Scaffolds/ERC721` | Benchmark-local compact ERC721 core ([`ERC721.sol`](Scaffolds/ERC721/ERC721.sol)) | 0.8.35 | 1482 |
| `Scaffolds/EAS/Attester` | [`ethereum-attestation-service/eas-contracts-example`](https://github.com/ethereum-attestation-service/eas-contracts-example/blob/d2864b166a08f9b3f9314f8b302316d67f227462/contracts/Attester.sol) | 0.8.26 | 3865 |
| `Scaffolds/CometRewards` | [`compound-finance/comet`](https://github.com/compound-finance/comet/blob/f766f51583c23acc33b2a7824654ef2029a96804/contracts/CometRewards.sol) | 0.8.15 via-IR | 3473 |
| `Scaffolds/Comet` | [`compound-finance/comet`](https://github.com/compound-finance/comet/blob/f766f51583c23acc33b2a7824654ef2029a96804/contracts/CometWithExtendedAssetList.sol) | 0.8.15 via-IR | 18599 |
| `Scaffolds/VestingWallet` | [OpenZeppelin `VestingWallet.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/finance/VestingWallet.sol) | 0.8.35 | 2277 |
| `Scaffolds/TimelockController` | [OpenZeppelin `TimelockController.sol`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/governance/TimelockController.sol) | 0.8.35 | 6509 |
| `Scaffolds/UniswapV3Pool` | [`Uniswap/v3-core`](https://github.com/Uniswap/v3-core/blob/d0831dc6b8a318df3872b6d68f6de135c9f3ec29/contracts/UniswapV3Pool.sol) | 0.7.6 | 22142 |
| `Scaffolds/UniswapV2Router02` | [`Uniswap/v2-periphery`](https://github.com/Uniswap/v2-periphery/blob/ed24991304291297c3b4a52818d02f46a17aa9a2/contracts/UniswapV2Router02.sol) | 0.6.6 | 21996 |

`Scaffolds/CompoundIII/` and `Scaffolds/OpenZeppelinBench/` hold source closures shared by the
respective scaffolds.

## File conventions

Each benchmark directory contains:

- `Spec.lean` — the Sol⁻ contract: storage layout, transitions, typed external-call hooks.
- `SpecSyntax.lean` — the same spec in Solidity-like surface syntax, proved equal to `Spec.lean`.
- `Bytecode.lean` — the compiled creation/runtime bytecode as Lean byte arrays with the verified
  jump-destination table.
- `Selectors.lean` — proofs of concrete 4-byte function selectors.
- `Constructor.lean` / `Correct.lean` — constructor and runtime equivalence; `…ContractCorrect`
  bundles both. In `Scaffolds/` these are `sorry` stubs.
- Artifacts: `runtime.hex`, `creation.hex`, `*.abi.json`, `*.storage.json`, `sources.sha256`
  (pins the upstream sources), and `contracts/` (the exact source closure used to reproduce the
  bytecode). Compiler version and flags are recorded per benchmark in its own `README.md` where
  present.

## Reproducing upstream scaffold builds

Comet, CometRewards, Safe, EAS Attester, Klima, and UniswapV2Router02 have pinned `build.json`
manifests. Their creation/runtime bytecode was compared byte-for-byte with the actual builds at
the recorded upstream commits. The manifests preserve source names, metadata settings, optimizer
details, dependency source checksums, and build tool versions. No on-chain bytecode match is implied.

| Scaffold | Upstream build | Optimizer runs | EVM | Metadata |
|---|---|---|---|---|
| Comet / CometRewards | `yarn build` | 1, via-IR, custom Yul sequence | London | IPFS |
| Safe | `npm run build` | Disabled | Istanbul | IPFS, literal source content |
| EAS Attester | `pnpm compile` | 1,000,000 | Paris (Hardhat default) | No hash |
| Klima | Foundry `forge build` | 800 | Istanbul | IPFS, upstream remappings |
| UniswapV2Router02 | `yarn compile` | 999,999 | Istanbul | IPFS |

Replay any manifest with the matching compiler; use `--check` to verify without changing files:

```bash
python3 scripts/regenerate_scaffold_artifacts.py \
  Benchmarks/Scaffolds/Safe/build.json --solc /path/to/solc-0.7.6 --check
```

The script verifies source hashes and both upstream bytecode hashes before regenerating hex, ABI,
storage/metadata/AST artifacts, Lean byte arrays, jump tables, and immutable offsets. The source
closure replay was separately checked against the upstream build, including its metadata.

Generate and type-check fresh runtime block summaries with:

```bash
python3 scripts/check_all_benchmark_blocks.py \
  --output-dir /tmp/equivm-upstream-builds/blocks --jobs 4 \
  --contract Scaffolds/Comet --contract Scaffolds/CometRewards \
  --contract Scaffolds/Safe --contract Scaffolds/EAS/Attester \
  --contract Scaffolds/Klima --contract Scaffolds/UniswapV2Router02
```

Use a fresh output directory after changing bytecode or imported Lean definitions: the existing
checker caches successful shards by generated source hash. The generator uses each contract's
updated immutable layout and emits explicit boundaries for unsupported instructions; the summaries
cover supported segments and do not complete the scaffold's whole-contract equivalence proof.
