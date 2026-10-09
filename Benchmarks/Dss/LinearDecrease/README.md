# MakerDAO/Sky DSS Linear Decrease Benchmark

This benchmark uses the unmodified upstream DSS `LinearDecrease` source from MakerDAO/Sky:

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
  -o /tmp/equivm-dss-lineardecrease-build --overwrite \
  Benchmarks/Dss/LinearDecrease/contracts/abaci.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/abaci.sol`: exact fetched upstream Solidity source.
- `abaci.sol.ast.json`: Solidity AST JSON emitted by solc.
- `LinearDecrease.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `LinearDecrease.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/abaci.sol      sha256 a4c3dc0368d66a5bf84e586f0cf76e2e80fb8b336c00348a97cc0d4ddcb016ca
abaci.sol.ast.json       sha256 91966cd8a437d9be0ec24d1a85861ebbd8d8e2dc2382b9cac88c3341e837ee42
LinearDecrease.abi.json  sha256 ede5548d03d74fe9c03f44a7cad9e85f63dd7e073257d423230a7df70ca5d8a2
LinearDecrease.storage.json sha256 e927ce81404a8c9c512f740dd1ab31eb339e8f79e8cf670973b7ea4d02ed00f4
creation.hex             sha256 223b89d79919951aa9d1528b39bd9f62930cfce6c5557b8528a3415378952df4
runtime.hex              sha256 9b76fdfca3abc40ffd3a5bd186451dcffa3d526fac99b384cbceaa5e45478f7c
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `linearDecreaseContractCorrect` in `Correct.lean`.
