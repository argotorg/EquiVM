# MakerDAO/Sky DSS Stairstep Exponential Decrease Benchmark

This benchmark uses the unmodified upstream DSS `StairstepExponentialDecrease` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/abaci.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/abaci.sol`
- Solidity pragma: see `contracts/abaci.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-stairstepexponentialdecrease-build --overwrite \
  Benchmarks/Dss/StairstepExponentialDecrease/contracts/abaci.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/abaci.sol`: exact fetched upstream Solidity source.
- `abaci.sol.ast.json`: Solidity AST JSON emitted by solc.
- `StairstepExponentialDecrease.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `StairstepExponentialDecrease.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/abaci.sol      sha256 a4c3dc0368d66a5bf84e586f0cf76e2e80fb8b336c00348a97cc0d4ddcb016ca
abaci.sol.ast.json       sha256 b784526c2474f9ba6ed70d3e38549cf83de2c07bbda2518a858c3b1e8feeb86c
StairstepExponentialDecrease.abi.json sha256 f951e28b2e61d421e391818c302aa251e2ac74ab06129e4aca7383dda63a5d1d
StairstepExponentialDecrease.storage.json sha256 ff358b4e80dd29f2c0e6cca97fd315903a24d56fb6cd772546c8fa8e9d080546
creation.hex             sha256 246ed73d3882f6fc7e6a728df22c0f5e42ca9df8a7680c8dc82bc01cac27aac9
runtime.hex              sha256 23cbd1978b917fc121afa3380a3557fa47f0387e0dbf1bac6ed2f17de43458a1
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `stairstepExponentialDecreaseContractCorrect` in `Correct.lean`.
