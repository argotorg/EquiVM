# MakerDAO/Sky DSS Spotter Benchmark

This benchmark uses the unmodified upstream DSS Spotter source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/spot.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/spot.sol`
- Solidity pragma: `^0.6.12`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json -o /tmp/equivm-dss-spot-build --overwrite \
  Benchmarks/Dss/Spot/contracts/spot.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/spot.sol`: exact fetched upstream Solidity source.
- `spot.sol.ast.json`: Solidity AST JSON emitted by solc.
- `creation.hex`: optimized creation bytecode, 2320 bytes.
- `runtime.hex`: optimized deployed runtime bytecode, 2178 bytes.
- `Spotter.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold with storage layout and full public ABI surface.
- `SpecSyntax.lean`: Solm notation presentation for representative fragments, checked by `rfl`.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper,
  intentionally `sorry` at the runtime target.

Source and artifact hashes:

```text
contracts/spot.sol sha256 f772861927801ca1e32ba818ffc55df6ceffcc530ac3d8b6b223e7411bed118f
creation.hex       sha256 37f6b1f77414cf962b738035e9a1b4687b48625539850545f56fe3dbb274207a
runtime.hex        sha256 6ec8e84641273e3d41440ebf39fa502ebd768fd77e0187881c36afbceba8d4cc
Spotter.abi.json   sha256 f34e920a26434f13280517184b7074656f23cef6cf3f6d602f652d1febcf27b1
spot.sol.ast.json  sha256 3b8eadb6c97c88fe178542d7301709856fab894843f2ef9d184e0471bc69b0bd
```

Scaffold notes:

- Readiness: ready for proof as of 2026-07-03. Fresh solc output exactly matches the checked-in
  Lean creation/runtime byte arrays, and the solc storage layout matches `Spec.lean`.
- The named ABI surface includes public storage getters, auth, three overloaded `file` functions,
  `poke`, and `cage`.
- Storage layout is transcribed from solc's `--storage-layout`: `wards` slot 0, `ilks` slot 1,
  `vat` slot 2, `par` slot 3, and `live` slot 4.
- `PipLike.peek()` and `VatLike.file(bytes32,bytes32,uint256)` are represented with a custom
  external ABI. `peek` is modeled as a normal external call because the upstream interface is not
  declared `view`.
- The runtime has two `CALL` sites and two matching `EXTCODESIZE` guards. The spec models solc's
  guard on both `poke` calls: `PipLike.peek()` and `VatLike.file(bytes32,bytes32,uint256)`.
- The `Poke` event is intentionally omitted; the current equivalence relation ignores substate/logs,
  matching the policy used by the other event-bearing benchmarks.
- The conditional arithmetic in `poke` is short-circuited: if `has` is false, the nested
  `mul/rdiv/rdiv` path is not evaluated.
- No known Solm syntax or semantics change is required to start proving this benchmark. The likely
  proof hotspots are oracle return decoding, conditional arithmetic, and packed bytes32-to-uint casts.
