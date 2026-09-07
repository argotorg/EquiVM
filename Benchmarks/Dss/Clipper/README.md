# MakerDAO/Sky DSS Clipper Benchmark

This benchmark uses the unmodified upstream DSS `Clipper` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/clip.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/clip.sol`
- Solidity pragma: see `contracts/clip.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-clipper-build --overwrite \
  Benchmarks/Dss/Clipper/contracts/clip.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/clip.sol`: exact fetched upstream Solidity source.
- `clip.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Clipper.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `Clipper.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/clip.sol       sha256 1ea897fc0e8e0964a2e5098716d86fdcd93d11e0b2e4f65998eb1b7650d167de
clip.sol.ast.json        sha256 a7738910f5c1609263b38c41c8a8eb9fba925628991208ee415ef50fe9631441
Clipper.abi.json         sha256 5b50c95b143cc17fd1e2f426ca4800cc4acbf7b08fdc023c90da5db4caf28be1
Clipper.storage.json     sha256 3111f14b0d7dc69853a77a923a4d708a3aeb090b8f0b9e03383c84c0a165fd12
creation.hex             sha256 60a21b7d664b3064aec07d16d7193d8faf028c0a54beed570bf7fd5e70a22f64
runtime.hex              sha256 138ad9c2511ecb8ef1a13a93740e688e3df7d8ce156e40c514f657605af14ec5
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `clipperContractCorrect` in `Correct.lean`.
- The spec uses `DecodeMode.legacySolc05` for coder-v1 calldata and return decoding. The runtime
  theorem's existing `clipperStorageWF` precondition includes `I.calldata.size < 2^255`, excluding
  the inputs on which Clipper's signed dynamic-size guard differs from the legacy decoder.
