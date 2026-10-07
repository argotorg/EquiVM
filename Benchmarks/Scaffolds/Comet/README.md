# Compound III Comet Benchmark

Source: [`contracts/CometWithExtendedAssetList.sol`](../CompoundIII/contracts/CometWithExtendedAssetList.sol) from
[`compound-finance/comet`](https://github.com/compound-finance/comet/tree/f766f51583c23acc33b2a7824654ef2029a96804)
commit `f766f51583c23acc33b2a7824654ef2029a96804`.

Artifacts reproduce the pinned upstream `yarn build` build, including metadata.
The [`hardhat.config.ts`](https://github.com/compound-finance/comet/blob/f766f51583c23acc33b2a7824654ef2029a96804/hardhat.config.ts) build uses
Solidity 0.8.15, optimizer enabled with 1 run, via-IR, the upstream custom Yul optimizer
sequence, London EVM, and default IPFS metadata.

Both creation and runtime bytecode were compared byte-for-byte with the actual upstream build.
The vendored Solidity source contents are unchanged.

Compiler: `0.8.15+commit.e14f2714.Linux.g++`. Build tool versions, configuration/lockfile hashes,
canonical source paths, complete compiler settings, and expected bytecode hashes are in
[`build.json`](build.json). The compiler inputs retain upstream source names even where the
vendored directory layout differs.

Reproduce from the repository root with the matching solc binary:

```bash
python3 scripts/regenerate_scaffold_artifacts.py \
  Benchmarks/Scaffolds/Comet/build.json --solc /path/to/solc-0.8.15
```

Add `--check` to verify without writing. This replays the target's source closure through solc
standard JSON; its creation/runtime output is required to match the recorded upstream build.
Additional AST/storage output selection does not change the bytecode.

Artifacts:

- `creation.hex`: 21425 bytes, without constructor arguments.
- `runtime.hex`: 18599 bytes.
- `CometWithExtendedAssetList.abi.json`, `CometWithExtendedAssetList.storage.json`, and `CometWithExtendedAssetList.metadata.json`: compiler outputs.
- `CometWithExtendedAssetList.sol.ast.json`: Solidity compact AST JSON.
- `Bytecode.lean`: matching creation/runtime arrays and verified jump-destination tables.
- `Immutables.lean`: immutable offsets regenerated from compiler references and matched by AST name.
- `artifacts.sha256`: hashes of the generated files, checked from this directory with
  `sha256sum -c artifacts.sha256`. `build.json` separately records hashes of raw bytecode bytes.

The shared source closure and source checksum manifest are in
[`../CompoundIII/`](../CompoundIII/README.md).

Block summaries are generated and type-checked with
[`check_all_benchmark_blocks.py`](../../../scripts/check_all_benchmark_blocks.py).
See the [benchmark build instructions](../../README.md#reproducing-upstream-scaffold-builds)
for the complete command. Generated summaries live outside the source tree.

The runtime is an unpatched compiler template: constructor-set immutables are still zero.
Matching the upstream build does not identify a particular on-chain deployment.

Status:

- The stored `runtime.hex`/`cometBytecode` is solc's unpatched deployed-bytecode template. Its
  immutable references are represented explicitly in `Immutables.lean` as zero-valued template
  slots.
- The payable fallback path is represented by a raw-bytes Solm fallback that delegates to
  `extensionDelegate`.
- The theorem now uses an immutable-aware `constructorEquivalenceWith` wrapper, but the constructor
  spec is still not faithful enough for handoff: `numAssets`, asset-list creation, constructor
  validation, and constructor external-call wiring remain placeholders.
- Several protocol bodies are still source-level scaffolds, not final proof-ready specs. In
  particular, the lending, transfer, liquidation, oracle, collateral, and asset-list paths still
  need full Solm bodies before this benchmark is ready for an agent to prove end-to-end.
