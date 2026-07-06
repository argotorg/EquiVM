# MakerDAO/Sky DSS Pot Benchmark

This benchmark uses the unmodified upstream DSS Pot source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/pot.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/pot.sol`
- Solidity pragma: `^0.6.12`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json -o /tmp/equivm-dss-pot-build --overwrite \
  Benchmarks/Dss/Pot/contracts/pot.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/pot.sol`: exact fetched upstream Solidity source.
- `pot.sol.ast.json`: Solidity AST JSON emitted by solc.
- `creation.hex`: optimized creation bytecode, 2746 bytes.
- `runtime.hex`: optimized deployed runtime bytecode, 2595 bytes.
- `Pot.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold with storage layout and full public ABI surface.
- `SpecSyntax.lean`: Solm notation presentation for representative fragments, checked by `rfl`.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper,
  intentionally `sorry` at the runtime target.

Source and artifact hashes:

```text
contracts/pot.sol sha256 8b22fb58d37e5eba6c5d1f42c8651a2c5077d39a93edd13082029bc3bfb3edc6
creation.hex      sha256 5f9545127ff0838c3d8441c46b431df1d700162f92932723c04bc3924258662e
runtime.hex       sha256 586a7d2ca61ba9569b7e714b10b78a0434da8dd1b8186348fb04f39fa6390a99
Pot.abi.json      sha256 bbf338478109d65779c31584b02a1d84f9f49793e1401d4559e2e23a4a051ba4
pot.sol.ast.json  sha256 f207fff82a6a016fa3d2b1b1be527bc076c85e98f6cff5a0a08ac3364d7c7006
```

Scaffold notes:

- Readiness: ready for proof as of 2026-07-03. Fresh solc output exactly matches the checked-in
  Lean creation/runtime byte arrays, and the solc storage layout matches `Spec.lean`.
- The named ABI surface includes public storage getters, auth, overloaded `file`, `drip`, `join`,
  `exit`, and `cage`.
- Storage layout is transcribed from solc's `--storage-layout`: `wards` slot 0, `pie` slot 1,
  `Pie` slot 2, `dsr` slot 3, `chi` slot 4, `vat` slot 5, `vow` slot 6, `rho` slot 7, and
  `live` slot 8.
- `VatLike.move(address,address,uint256)` and `VatLike.suck(address,address,uint256)` are
  represented with a custom external ABI.
- The runtime has two optimized `CALL` sites and two matching `EXTCODESIZE` guards. The source has
  three high-level `VatLike` calls because `join` and `exit` share one optimized bytecode call path;
  the spec models solc's guard on all three source-level calls.
- The assembly `_rpow` helper is modeled structurally as a Solm loop with the same checked multiply,
  rounding-add, division, and odd-exponent update shape. Reusable proof work should isolate `_rpow`,
  `_rmul`, and typed external-call lemmas.
- No known Solm syntax or semantics change is required to start proving this benchmark. The likely
  proof hotspot is the optimized assembly `_rpow` loop.
