# MakerDAO/Sky DSS Flipper Benchmark

This benchmark uses the unmodified upstream DSS `Flipper` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/flip.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/flip.sol`
- Solidity pragma: see `contracts/flip.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-flipper-build --overwrite \
  Benchmarks/Dss/Flipper/contracts/flip.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/flip.sol`: exact fetched upstream Solidity source.
- `flip.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Flipper.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `Flipper.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/flip.sol       sha256 6bb5e688aae203d418aed4ef01f2e6619ca9e9075a7848cc307123271e0c7979
flip.sol.ast.json        sha256 2cd59950e2228f4138f8db041894b6e982f7d933d72ad1f70def5974b88a33e0
Flipper.abi.json         sha256 32563b2b6955cebb027c32c4f2f1769d41d5fbe2a21dd5d3b36e4089d6ccb3cc
Flipper.storage.json     sha256 9ee3ad9ef208d26209e7f650487b9a8e6d839549e27dbd14bafa1aba5bbc9197
creation.hex             sha256 e4b2b8cbcfe874c5c2192aa65649a650250fd04978aa06a96c2bd1003c16ba39
runtime.hex              sha256 2752db55eb3bfce2e1e04d4ef59213ccabd8251bdc9bd05d1ee53d3538e1557c
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `flipperContractCorrect` in `Correct.lean`.
