# MakerDAO/Sky DSS Flopper Benchmark

This benchmark uses the unmodified upstream DSS `Flopper` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/flop.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/flop.sol`
- Solidity pragma: see `contracts/flop.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-flopper-build --overwrite \
  Benchmarks/Dss/Flopper/contracts/flop.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/flop.sol`: exact fetched upstream Solidity source.
- `flop.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Flopper.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `Flopper.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/flop.sol       sha256 0e02d2169c0872486b202ff74456e77704034586928cf1def3ae54f670140f8e
flop.sol.ast.json        sha256 8494b08966b81d484c01952df2bd0503a25a64a8064eaaf057db48e1f62b5a49
Flopper.abi.json         sha256 e42ffaa276c7550e3fb9e03a21e76f7365d5051a7dcaddaec05fb46db82f9518
Flopper.storage.json     sha256 851c2c806de80df8e4dc10c4455743ec92070373f259ec768ee9c4b55b24e620
creation.hex             sha256 5312a7abac73fbb0b087bda85722bb09356b29db7e20967f3c03b0bdc9b45dd3
runtime.hex              sha256 b826f8f36efff3f22cf07f6a6bf42401a706e7ccd019472b27327c66cc5e3a34
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `flopperContractCorrect` in `Correct.lean`.
