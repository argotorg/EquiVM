# Safe Benchmark

Source: [`Benchmarks/Safe/contracts/Safe.sol`](contracts/Safe.sol) from `safe-global/safe-smart-account` commit `77901a5a1ad835b74ad3b72f73a8412cfe491c57` (2026-06-05, `Do Not Propagate Reverts on Signatures (#1115)`).

Compiled with the current local Solidity compiler and optimizer enabled:

```bash
solc --optimize --optimize-runs 200 --evm-version shanghai --metadata-hash none --bin --bin-runtime --abi --storage-layout \
  --base-path . --overwrite -o /private/tmp/safe-build-current Benchmarks/Safe/contracts/Safe.sol
```

Compiler: `0.8.35+commit.47b9dedd.Darwin.appleclang`.

The EVM target is pinned to Shanghai because solc 0.8.35 defaults to Osaka, whose optimized
output may use `MCOPY`; this benchmark repository's EVM semantics currently model Shanghai-era
opcodes such as `PUSH0`, but not Osaka's `MCOPY`.

Some vendored upstream Solidity comments still mention the historical 0.7.6 compiler or link to
0.7.6 documentation; those comments are not the benchmark compiler pin.  The command above is the
artifact provenance for this benchmark.

Artifacts:

- `creation.hex`: optimized creation bytecode, 11907 bytes, sha256 `0d94b8c31e4fb2d01d7653b1c53013fba78f5d053014edd9e17c89888d7c7281`
- `runtime.hex`: optimized deployed runtime bytecode, 11874 bytes, sha256 `99919d79befacfb9210453d4ba1d3193e3b334a5dc6206596b4f48bb55136006`
- `Safe.abi.json`: ABI emitted by solc, sha256 `c2d916b516f1cf00691d5fe99f62e8bba92e0675e8c25b5e5800d6e53b08053a`
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree
- `Spec.lean`: Solm AST scaffold with ABI surface, solc 0.8.35 ABI coder mode, and solc storage layout
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold
- `Bytecode.lean`: optimized bytecode embedded as `ByteArray`, with `valid_jumps` facts
- `Constructor.lean`: constructor equivalence proof for the storage-initializing initcode
- `Correct.lean`: runtime dispatch routing and top-level contract equivalence target

Main source sha256: `9f91d9250e18bb0710b7b1f10dcbe2417e9ef8d22eeee98dba2ef48661a060fa`.

Note: The receive/fallback path is present in the Solidity runtime and modeled explicitly in
`Spec.lean`. Events and revert payloads are omitted, as in the other benchmarks.
