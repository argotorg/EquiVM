# Uniswap V2 Router02 Benchmark

Source: [`contracts/UniswapV2Router02.sol`](contracts/UniswapV2Router02.sol) from
[`Uniswap/v2-periphery`](https://github.com/Uniswap/v2-periphery/tree/ed24991304291297c3b4a52818d02f46a17aa9a2)
commit `ed24991304291297c3b4a52818d02f46a17aa9a2`.

Artifacts reproduce the pinned upstream `yarn compile` build, including metadata.
The [`.waffle.json`](https://github.com/Uniswap/v2-periphery/blob/ed24991304291297c3b4a52818d02f46a17aa9a2/.waffle.json) build uses
Solidity 0.6.6, optimizer enabled with 999,999 runs, Istanbul EVM, and default IPFS metadata.

Both creation and runtime bytecode were compared byte-for-byte with the actual upstream build.
The vendored Solidity source contents are unchanged.

Dependencies are the upstream lockfile packages `@uniswap/v2-core@1.0.0` and
`@uniswap/lib@4.0.1-alpha`; the imported files match the vendored copies exactly.

Compiler: `0.6.6+commit.6c089d02.Linux.g++`. Build tool versions, configuration/lockfile hashes,
canonical source paths, complete compiler settings, and expected bytecode hashes are in
[`build.json`](build.json). The compiler inputs retain upstream source names even where the
vendored directory layout differs.

Reproduce from the repository root with the matching solc binary:

```bash
python3 scripts/regenerate_scaffold_artifacts.py \
  Benchmarks/Scaffolds/UniswapV2Router02/build.json --solc /path/to/solc-0.6.6
```

Add `--check` to verify without writing. This replays the target's source closure through solc
standard JSON; its creation/runtime output is required to match the recorded upstream build.
Additional AST/storage output selection does not change the bytecode.

Artifacts:

- `creation.hex`: 22387 bytes, without constructor arguments.
- `runtime.hex`: 21996 bytes.
- `UniswapV2Router02.abi.json`, `UniswapV2Router02.storage.json`, and `UniswapV2Router02.metadata.json`: compiler outputs.
- `UniswapV2Router02.sol.ast.json`: Solidity compact AST JSON.
- `Bytecode.lean`: matching creation/runtime arrays and verified jump-destination tables.
- `Immutables.lean`: immutable offsets regenerated from compiler references and matched by AST name.
- `artifacts.sha256`: hashes of the generated files, checked from this directory with
  `sha256sum -c artifacts.sha256`. `build.json` separately records hashes of raw bytecode bytes.

`sources.sha256` records vendored Solidity checksums relative to this directory.

Block summaries are generated and type-checked with
[`check_all_benchmark_blocks.py`](../../../scripts/check_all_benchmark_blocks.py).
See the [benchmark build instructions](../../README.md#reproducing-upstream-scaffold-builds)
for the complete command. Generated summaries live outside the source tree.

The runtime is an unpatched compiler template: constructor-set immutables are still zero.
Matching the upstream build does not identify a particular on-chain deployment.

Scaffold notes:

- The contract has no storage. Its only persistent constructor data are the immutable `factory` and
  `WETH` addresses.
- `runtime.hex` is solc's deployed runtime template with zeroed immutable references. Concrete
  runtime correctness is stated for `patchRuntime uniswapV2Router02Bytecode (patches v)`.
- The source uses dynamic calldata/memory arrays, `for` loops, `abi.encodePacked`, `keccak256`,
  raw TransferHelper calls, typed pair/factory/WETH/ERC20 calls, payable ETH paths, and a payable
  `receive` restricted to WETH.
- No change to `Reasoning/` or `Solm/` was needed for this scaffold to build. The likely proof
  hotspots are CREATE2 `pairFor`, the chained `getAmountsIn`/`getAmountsOut` loops, TransferHelper
  raw-call return decoding, and the optimized router dispatcher.
