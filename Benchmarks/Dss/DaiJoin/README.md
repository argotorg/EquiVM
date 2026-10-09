# MakerDAO/Sky DSS Dai Join Benchmark

This benchmark uses the unmodified upstream DSS `DaiJoin` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/join.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/join.sol`
- Solidity pragma: see `contracts/join.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-daijoin-build --overwrite \
  Benchmarks/Dss/DaiJoin/contracts/join.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/join.sol`: exact fetched upstream Solidity source.
- `join.sol.ast.json`: Solidity AST JSON emitted by solc.
- `DaiJoin.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `DaiJoin.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/join.sol       sha256 96fceff4511aa976db5c6b144d83f4dd1bde832dd2f49fd6e54e69343b9583f9
join.sol.ast.json        sha256 5591beb3d003a65489169d4f92c6a70f90621aa280c76fe6e77a7a4f2b22cf23
DaiJoin.abi.json         sha256 a703aa58960ab57bfa8c80a36581172294cd868d5e0663a4f6360e560b601838
DaiJoin.storage.json     sha256 a62f9b3385ae947c81663df62061ae2b77d1577791bb701d03fd788856ad838e
creation.hex             sha256 b44a311e5ce707b64484e06771af967a181edac1803710139228962c143aed16
runtime.hex              sha256 c409e297dbb83b98448ed84315989f174c7656e2affae4c1aca6dbc64973ddb6
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `daiJoinContractCorrect` in `Correct.lean`.
