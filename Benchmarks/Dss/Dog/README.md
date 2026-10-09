# MakerDAO/Sky DSS Dog Benchmark

This benchmark uses the unmodified upstream DSS `Dog` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/dog.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/dog.sol`
- Solidity pragma: see `contracts/dog.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-dog-build --overwrite \
  Benchmarks/Dss/Dog/contracts/dog.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/dog.sol`: exact fetched upstream Solidity source.
- `dog.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Dog.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `Dog.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/dog.sol        sha256 274f7c5df8a13e535b496236436ebf726228fbe9285d94c542e2c9d2a78671de
dog.sol.ast.json         sha256 b2c706b442f3330b3bfe74881fa2f855d681bf1184f1526cde3ec722333705a9
Dog.abi.json             sha256 5d2b2a541441b6fb3eb35fa5832dc3506cafd8f72e1a14dae3edd4b64b22ae18
Dog.storage.json         sha256 3a7a6289736ec45c8ac993935b4d9b4d94c4f0d6c096bbf8790e822b6264cc51
creation.hex             sha256 55d20b9999033d2665bd64fe3d6fa340d5b19a57708a1f585878dc92cc0de216
runtime.hex              sha256 76a2038588f1cffc3954e4d702144a75a7e9f589ba9acb4b79b387be3bae9bdd
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `dogContractCorrect` in `Correct.lean`.
