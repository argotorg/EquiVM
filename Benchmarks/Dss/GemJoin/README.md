# MakerDAO/Sky DSS Gem Join Benchmark

This benchmark uses the unmodified upstream DSS `GemJoin` source from MakerDAO/Sky:

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
  -o /tmp/equivm-dss-gemjoin-build --overwrite \
  Benchmarks/Dss/GemJoin/contracts/join.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/join.sol`: exact fetched upstream Solidity source.
- `join.sol.ast.json`: Solidity AST JSON emitted by solc.
- `GemJoin.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `GemJoin.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/join.sol       sha256 96fceff4511aa976db5c6b144d83f4dd1bde832dd2f49fd6e54e69343b9583f9
join.sol.ast.json        sha256 a9bc4a1582515bcadec1e85f82b49570d11f62689480cf0ea1a434ba4b736088
GemJoin.abi.json         sha256 64e88e4c0589ad97aea39f930bde70e36709d8096be1895a7b62cc56ce2e884f
GemJoin.storage.json     sha256 8a445d8f5c856b92d2fa8115bbbfb077d8fd77406cdd08cdfda213403e59e09d
creation.hex             sha256 d1c0f4ecb2ec3c3a1ac0b2b4afe8993e83b3bdf659e5c76605badec25d9f1167
runtime.hex              sha256 2cb61a36f057b3f0fe0ac9842dd21d7aa77aa1c48df362177a884606a2338ed5
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `gemJoinContractCorrect` in `Correct.lean`.
