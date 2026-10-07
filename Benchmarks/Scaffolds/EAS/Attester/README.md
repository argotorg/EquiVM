# EAS Attester Benchmark

Source: [`contracts/Attester.sol`](contracts/Attester.sol) from
[`ethereum-attestation-service/eas-contracts-example`](https://github.com/ethereum-attestation-service/eas-contracts-example/tree/d2864b166a08f9b3f9314f8b302316d67f227462)
commit `d2864b166a08f9b3f9314f8b302316d67f227462`.

Artifacts reproduce the pinned upstream `pnpm compile` build, including metadata.
The [`hardhat.config.ts`](https://github.com/ethereum-attestation-service/eas-contracts-example/blob/d2864b166a08f9b3f9314f8b302316d67f227462/hardhat.config.ts) build uses
Solidity 0.8.26, optimizer enabled with 1,000,000 runs, Paris EVM, and
`metadata.bytecodeHash: "none"`. The pinned Hardhat 2.22.13 chooses Paris when the
project does not specify an EVM version; using solc's Cancun default does not reproduce this build.

Both creation and runtime bytecode were compared byte-for-byte with the actual upstream build.
The vendored Solidity source contents are unchanged.

The imported EAS interfaces are from the locked npm package
`@ethereum-attestation-service/eas-contracts@1.7.1`.

Compiler: `0.8.26+commit.8a97fa7a.Linux.g++`. Build tool versions, configuration/lockfile hashes,
canonical source paths, complete compiler settings, and expected bytecode hashes are in
[`build.json`](build.json). The compiler inputs retain upstream source names even where the
vendored directory layout differs.

Reproduce from the repository root with the matching solc binary:

```bash
python3 scripts/regenerate_scaffold_artifacts.py \
  Benchmarks/Scaffolds/EAS/Attester/build.json --solc /path/to/solc-0.8.26
```

Add `--check` to verify without writing. This replays the target's source closure through solc
standard JSON; its creation/runtime output is required to match the recorded upstream build.
Additional AST/storage output selection does not change the bytecode.

Artifacts:

- `creation.hex`: 4057 bytes, without constructor arguments.
- `runtime.hex`: 3865 bytes.
- `Attester.abi.json`, `Attester.storage.json`, and `Attester.metadata.json`: compiler outputs.
- `Attester.sol.ast.json`: Solidity compact AST JSON.
- `Bytecode.lean`: matching creation/runtime arrays and verified jump-destination tables.
- `Immutables.lean`: immutable offsets regenerated from compiler references and matched by AST name.
- `artifacts.sha256`: hashes of the generated files, checked from this directory with
  `sha256sum -c artifacts.sha256`. `build.json` separately records hashes of raw bytecode bytes.

`sources.sha256` records vendored Solidity checksums relative to this directory.

Block summaries are generated and type-checked with
[`check_all_benchmark_blocks.py`](../../../../scripts/check_all_benchmark_blocks.py).
See the [benchmark build instructions](../../../README.md#reproducing-upstream-scaffold-builds)
for the complete command. Generated summaries live outside the source tree.

The runtime is an unpatched compiler template: constructor-set immutables are still zero.
Matching the upstream build does not identify a particular on-chain deployment.

Scaffold notes:

- The runtime has no storage slots. The constructor-set `_eas` immutable is patched into the
  runtime template at byte offsets `824, 1719, 1888, 2289`.
- Public ABI surface: `attest`, `revoke`, `multiAttest`, and `multiRevoke`.
- The spec models EAS request structs as ABI tuples in field order, matching Solidity calldata.
- `abi.encode(input)` is modeled as one-word ABI encoding by reusing Solm's configured ABI encoder
  and dropping a dummy selector.
- Solc emits explicit `EXTCODESIZE` guards for the no-return typed calls `revoke` and
  `multiRevoke`; these guards are present in the spec. The return-valued calls `attest` and
  `multiAttest` rely on return decoding instead and have no explicit code-size guard in the
  optimized runtime.
- Custom-error payloads and events are omitted consistently with the framework's revert-data and
  substate abstraction.
