# EAS Attester Benchmark

This benchmark uses the upstream Ethereum Attestation Service example `Attester` source:

- Repository: `ethereum-attestation-service/eas-contracts-example`
- Commit: `d2864b166a08f9b3f9314f8b302316d67f227462`
- Commit date: `2024-10-12T17:55:58Z`
- Path: `contracts/Attester.sol`
- Source URL:
  `https://github.com/ethereum-attestation-service/eas-contracts-example/blob/d2864b166a08f9b3f9314f8b302316d67f227462/contracts/Attester.sol`
- Solidity pragma: `0.8.26`

The imported EAS interface sources are vendored from npm package
`@ethereum-attestation-service/eas-contracts@1.7.1`, matching the example repository lockfile.

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.8.26 --optimize --optimize-runs 200 --metadata-hash none \
  --base-path Benchmarks/EAS/Attester/contracts \
  --bin --bin-runtime --abi --ast-compact-json --storage-layout \
  -o /tmp/equivm-eas-attester-build --overwrite \
  Benchmarks/EAS/Attester/contracts/Attester.sol
```

Compiler:

```text
0.8.26+commit.8a97fa7a.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/Attester.sol`: exact fetched upstream Solidity source.
- `contracts/@ethereum-attestation-service/eas-contracts/contracts/*`: minimal imported EAS
  interface sources from package version `1.7.1`.
- `Attester.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Attester.storage.json`: solc storage layout; empty because `_eas` is immutable.
- `creation.hex`: optimized creation bytecode, 3371 bytes.
- `runtime.hex`: optimized deployed runtime template, 3186 bytes.
- `Attester.abi.json`: ABI emitted by solc.
- `Immutables.lean`: `_eas` immutable value, runtime patch offsets, and `runtimeCodeOf`.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: compact Solm AST spec with the full public ABI surface.
- `Constructor.lean`: constructor-equivalence theorem stub.
- `Correct.lean`: runtime-equivalence theorem stub plus whole-contract wrapper.

Source and artifact hashes are recorded in `sources.sha256`.

Scaffold notes:

- The runtime has no storage slots. The constructor-set `_eas` immutable is patched into the
  runtime template at byte offsets `722`, `1465`, `1598`, and `1939`.
- Public ABI surface: `attest`, `revoke`, `multiAttest`, and `multiRevoke`.
- The spec models EAS request structs as ABI tuples in field order, matching Solidity calldata.
- `abi.encode(input)` is modeled as one-word ABI encoding by reusing Solm's configured ABI encoder
  and dropping a dummy selector.
- Solc emits explicit `EXTCODESIZE` guards for the no-return typed calls `revoke` and
  `multiRevoke`; these guards are present in the spec. The return-valued calls `attest` and
  `multiAttest` rely on return decoding instead and have no explicit code-size guard in the
  optimized runtime.
- Custom-error payloads and events are omitted consistently with the framework's revert-data and
  substate abstraction.
