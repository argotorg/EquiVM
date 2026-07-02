# Safe Benchmark

Source: [`Benchmarks/Safe/contracts/Safe.sol`](contracts/Safe.sol) from `safe-global/safe-smart-account` commit `77901a5a1ad835b74ad3b72f73a8412cfe491c57` (2026-06-05, `Do Not Propagate Reverts on Signatures (#1115)`).

Compiled with optimizer enabled:

```bash
/tmp/solc-0.7.6 --optimize --optimize-runs 200 --metadata-hash none --bin --bin-runtime --abi \
  --base-path . --overwrite -o /tmp/safe-build Benchmarks/Safe/contracts/Safe.sol
```

Compiler: `0.7.6+commit.7338295f.Darwin.appleclang`.

Artifacts:

- `creation.hex`: optimized creation bytecode, 12584 bytes, sha256 `9be87a0042e500eb766f4155012cf206062dda9dec402522f1701cae84725e6d`
- `runtime.hex`: optimized deployed runtime bytecode, 12547 bytes, sha256 `f9461fcb6142665544c5b5492b4cc8a2ea155f65ca00075debcf9b6cb71a3117`
- `Safe.abi.json`: ABI emitted by solc, sha256 `c2d916b516f1cf00691d5fe99f62e8bba92e0675e8c25b5e5800d6e53b08053a`
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree
- `Spec.lean`: Solm AST scaffold with ABI surface and solc storage layout
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold
- `Bytecode.lean`: optimized bytecode embedded as `ByteArray`, with `valid_jumps` facts
- `Constructor.lean`: constructor equivalence target, currently `sorry`
- `Correct.lean`: runtime and top-level contract equivalence targets, currently `sorry`

Main source sha256: `9f91d9250e18bb0710b7b1f10dcbe2417e9ef8d22eeee98dba2ef48661a060fa`.

Note: The receive/fallback path is present in the Solidity runtime but not represented by `ContractDecl` fallback dispatch yet. Events are omitted, as in the other benchmarks.
