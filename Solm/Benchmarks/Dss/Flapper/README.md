# MakerDAO/Sky DSS Flapper Benchmark

This benchmark uses the unmodified upstream DSS `Flapper` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/flap.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/flap.sol`
- Solidity pragma: see `contracts/flap.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-flapper-build --overwrite \
  Benchmarks/Dss/Flapper/contracts/flap.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/flap.sol`: exact fetched upstream Solidity source.
- `flap.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Flapper.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `Flapper.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/flap.sol       sha256 81b1e49097fbb6eba3c58ac7146bcaaa6f6156428d51455880e60b95ae9a3077
flap.sol.ast.json        sha256 7d69ccfec4ea3be2cdc1399a2578bd6c8150d881db6653926e9df3f8a1add999
Flapper.abi.json         sha256 08ab1af40da39bb0f320fc5beff5eb7a94b389c36888d414cbc9381a671bc3a2
Flapper.storage.json     sha256 7bbada4fc7265c65bcb418747b40346f3859bd260a9954c5cfc8e4279a1fa386
creation.hex             sha256 9d1b5ceede2d7cfeaf3642a7fb2fe8f4127b2018f71ac427432fc20ef62f4c1b
runtime.hex              sha256 83aae9032144e1f054502270d98b40fa4f148052913c402c9bd02cf682ddd6f5
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `flapperContractCorrect` in `Correct.lean`.
