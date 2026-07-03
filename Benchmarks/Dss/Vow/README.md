# MakerDAO/Sky DSS Vow Benchmark

This benchmark uses the unmodified upstream DSS Vow source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/vow.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/vow.sol`
- Solidity pragma: `^0.6.12`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json -o /tmp/equivm-dss-vow-build --overwrite \
  Benchmarks/Dss/Vow/contracts/vow.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/vow.sol`: exact fetched upstream Solidity source.
- `vow.sol.ast.json`: Solidity AST JSON emitted by solc.
- `creation.hex`: optimized creation bytecode, 5410 bytes.
- `runtime.hex`: optimized deployed runtime bytecode, 5150 bytes.
- `Vow.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold with storage layout and full public ABI surface.
- `SpecSyntax.lean`: Solm notation presentation for representative fragments, checked by `rfl`.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper,
  intentionally `sorry` at the runtime target.

Source and artifact hashes:

```text
contracts/vow.sol sha256 609e5da454c0e68ce1c4dc7eb702a015139cd31305727604b777e13ea7bae302
creation.hex      sha256 ab631b0f6a35fce8509057bf8bafe8c03a9a0940f36b90bd8ad83f99a3f90115
runtime.hex       sha256 854a789dad9bea5ec0ac4149d3c535a91912658469e3b4266cf498950f7bf7a7
Vow.abi.json      sha256 bd97f42aa28fc8f5acfeda39b2ee2528063c9fe1fa69d4ba3301f10121d3751c
vow.sol.ast.json  sha256 00b4a222bebf2be75dd8f37fb83b303a9262b0e58114abefa83d266450a1db69
```

Scaffold notes:

- The named ABI surface includes public storage getters, auth, overloaded `file`, debt-queue,
  settlement, auction, and shutdown flows.
- Storage layout is transcribed from solc's `--storage-layout`: `wards` slot 0, `vat` slot 1,
  `flapper` slot 2, `flopper` slot 3, `sin` slot 4, `Sin` slot 5, `Ash` slot 6, `wait` slot 7,
  `dump` slot 8, `sump` slot 9, `bump` slot 10, `hump` slot 11, and `live` slot 12.
- `VatLike`, `FlapLike`, and `FlopLike` are represented with a custom external ABI. The overloaded
  `kick` and `cage` calls are dispatched by argument shape.
- The constructor includes the source-level `vat.hope(flapper_)` external call. `dai` and `sin` are
  modeled as static external calls; other interface calls are modeled as normal external calls.
- Repeated `vat.dai` and `vat.sin` reads are intentionally repeated in the spec, matching the source
  behavior under changing external state.
- No known Solm syntax or semantics change is required to start proving this benchmark. The likely
  proof hotspots are overloaded external ABI dispatch, repeated static calls, and sequential storage
  updates around `file("flapper", ...)`, `fess`, and `cage`.
