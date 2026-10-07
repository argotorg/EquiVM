# Safe Benchmark

Source: [`contracts/Safe.sol`](contracts/Safe.sol) from
[`safe-global/safe-smart-account`](https://github.com/safe-global/safe-smart-account/tree/77901a5a1ad835b74ad3b72f73a8412cfe491c57)
commit `77901a5a1ad835b74ad3b72f73a8412cfe491c57`.

Artifacts reproduce the pinned upstream `npm run build` build, including metadata.
The [`hardhat.config.ts`](https://github.com/safe-global/safe-smart-account/blob/77901a5a1ad835b74ad3b72f73a8412cfe491c57/hardhat.config.ts) build uses
Solidity 0.7.6, optimizer disabled, Istanbul EVM, and IPFS metadata with
`useLiteralContent: true` (set by the upstream Hardhat build).

Both creation and runtime bytecode were compared byte-for-byte with the actual upstream build.
The vendored Solidity source contents are unchanged.

Compiler: `0.7.6+commit.7338295f.Linux.g++`. Build tool versions, configuration/lockfile hashes,
canonical source paths, complete compiler settings, and expected bytecode hashes are in
[`build.json`](build.json). The compiler inputs retain upstream source names even where the
vendored directory layout differs.

Reproduce from the repository root with the matching solc binary:

```bash
python3 scripts/regenerate_scaffold_artifacts.py \
  Benchmarks/Scaffolds/Safe/build.json --solc /path/to/solc-0.7.6
```

Add `--check` to verify without writing. This replays the target's source closure through solc
standard JSON; its creation/runtime output is required to match the recorded upstream build.
Additional AST/storage output selection does not change the bytecode.

Artifacts:

- `creation.hex`: 20909 bytes, without constructor arguments.
- `runtime.hex`: 20869 bytes.
- `Safe.abi.json`, `Safe.storage.json`, and `Safe.metadata.json`: compiler outputs.
- `Bytecode.lean`: matching creation/runtime arrays and verified jump-destination tables.
- `artifacts.sha256`: hashes of the generated files, checked from this directory with
  `sha256sum -c artifacts.sha256`. `build.json` separately records hashes of raw bytecode bytes.

`sources.sha256` records vendored Solidity checksums relative to this directory.

Block summaries are generated and type-checked with
[`check_all_benchmark_blocks.py`](../../../scripts/check_all_benchmark_blocks.py).
See the [benchmark build instructions](../../README.md#reproducing-upstream-scaffold-builds)
for the complete command. Generated summaries live outside the source tree.

Scaffold notes:

- The spec uses `DecodeMode.legacySolc05` for the upstream compiler's default ABI coder v1.
- Raw increments, decrements, and gas arithmetic wrap at 256 bits, as in Solidity 0.7.6;
  explicit `SafeMath` operations keep their range checks. Overflow/underflow examples in
  `Spec.lean` check this distinction.
- The receive/fallback path is present in the runtime and modeled in `Spec.lean`.
- Constructor, runtime, and whole-contract correctness proofs remain scaffold `sorry` targets.
- Events and revert payloads are omitted under the framework's equivalence relation.
