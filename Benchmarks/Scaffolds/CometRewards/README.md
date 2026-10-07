# Compound III CometRewards Benchmark

Source: [`contracts/CometRewards.sol`](../CompoundIII/contracts/CometRewards.sol) from
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
  Benchmarks/Scaffolds/CometRewards/build.json --solc /path/to/solc-0.8.15
```

Add `--check` to verify without writing. This replays the target's source closure through solc
standard JSON; its creation/runtime output is required to match the recorded upstream build.
Additional AST/storage output selection does not change the bytecode.

Artifacts:

- `creation.hex`: 3621 bytes, without constructor arguments.
- `runtime.hex`: 3473 bytes.
- `CometRewards.abi.json`, `CometRewards.storage.json`, and `CometRewards.metadata.json`: compiler outputs.
- `CometRewards.sol.ast.json`: Solidity compact AST JSON.
- `Bytecode.lean`: matching creation/runtime arrays and verified jump-destination tables.
- `artifacts.sha256`: hashes of the generated files, checked from this directory with
  `sha256sum -c artifacts.sha256`. `build.json` separately records hashes of raw bytecode bytes.

The shared source closure and source checksum manifest are in
[`../CompoundIII/`](../CompoundIII/README.md).

Block summaries are generated and type-checked with
[`check_all_benchmark_blocks.py`](../../../scripts/check_all_benchmark_blocks.py).
See the [benchmark build instructions](../../README.md#reproducing-upstream-scaffold-builds)
for the complete command. Generated summaries live outside the source tree.

Status:

- Target theorem:
  `Benchmarks.CompoundIII.CometRewards.cometRewardsContractCorrect`.
- Fresh solc `0.8.15` via-IR output matches the checked-in Lean creation/runtime byte arrays and
  ABI exactly. The storage slot/type layout is unchanged; source paths and AST identifiers are regenerated.
- The runtime has four `STATICCALL` sites, three `CALL` sites, and two `EXTCODESIZE` guards. The
  spec models the view calls with `perm := false`; the two no-return `accrueAccount` calls are
  guarded with explicit `EXTCODESIZE > 0` checks.
- The three source events and custom-error revert payloads are intentionally not represented under
  the current equivalence relation, which ignores substate/logs and revert data.
