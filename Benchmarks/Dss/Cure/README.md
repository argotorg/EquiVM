# MakerDAO/Sky DSS Cure Benchmark

This benchmark uses the unmodified upstream DSS `Cure` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/cure.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/cure.sol`
- Solidity pragma: see `contracts/cure.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-cure-build --overwrite \
  Benchmarks/Dss/Cure/contracts/cure.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/cure.sol`: exact fetched upstream Solidity source.
- `cure.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Cure.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `Cure.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/cure.sol       sha256 ebc21dbf0cc4693cefad6b209c624513b885c2505a34bbcc8362a9f7c68ac25c
cure.sol.ast.json        sha256 98919b31d3e61e3dde1bbb30b9ff221cbc62d6df9857d91f15c4e9deb02b19a6
Cure.abi.json            sha256 d867c7bb8227f2f0b0a27e99254f666751d4df72653b94b92ce60a7fcb965fb8
Cure.storage.json        sha256 f35aa59a25561c541bb1b0af6a044e869566c822bb75d6501e42031f16fabf25
creation.hex             sha256 2431093c08bb0cb5764d60634a33988d2ddb3ffb24caeb30135bbf9f6af17ba6
runtime.hex              sha256 199a0aa60cdd9abd96fdc3b3ee9f83136a7340521f7c46775567486dc77c7cbb
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `cureContractCorrect` in `Correct.lean`.
