# MakerDAO/Sky DSS Exponential Decrease Benchmark

This benchmark uses the unmodified upstream DSS `ExponentialDecrease` source from MakerDAO/Sky:

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
  -o /tmp/equivm-dss-exponentialdecrease-build --overwrite \
  Benchmarks/Dss/ExponentialDecrease/contracts/abaci.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/abaci.sol`: exact fetched upstream Solidity source.
- `abaci.sol.ast.json`: Solidity AST JSON emitted by solc.
- `ExponentialDecrease.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `ExponentialDecrease.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/abaci.sol      sha256 a4c3dc0368d66a5bf84e586f0cf76e2e80fb8b336c00348a97cc0d4ddcb016ca
abaci.sol.ast.json       sha256 37272c262c3c67d70fcd11d8ea512a4f678a0a1d2aeb300613392b040e03168b
ExponentialDecrease.abi.json sha256 7f1b16624ec29b7f0adbd50f0a97be1c6b315d70e43c5c714b9776fb4f7432be
ExponentialDecrease.storage.json sha256 6412932c94f6540e642138d9df1118f08df3a787b8db37d24bf8b056afefe82e
creation.hex             sha256 9bee8fc71e0c78bd881fab2b17a790befee837bc94c5c8ef4440446afdd51759
runtime.hex              sha256 abb7584c00bee9ff49f6a9d2e8d548efa0ae5aeee340a2b9e9c41fe01a41f92a
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `exponentialDecreaseContractCorrect` in `Correct.lean`.
