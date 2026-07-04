# MakerDAO/Sky DSS Jug Benchmark

This benchmark uses the unmodified upstream DSS Jug source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/jug.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/jug.sol`
- Solidity pragma: `^0.6.12`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json -o /tmp/equivm-dss-jug-build --overwrite \
  Benchmarks/Dss/Jug/contracts/jug.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/jug.sol`: exact fetched upstream Solidity source.
- `jug.sol.ast.json`: Solidity AST JSON emitted by solc.
- `creation.hex`: optimized creation bytecode, 2560 bytes.
- `runtime.hex`: optimized deployed runtime bytecode, 2440 bytes.
- `Jug.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold with storage layout and full public ABI surface.
- `SpecSyntax.lean`: Solm notation presentation for representative fragments, checked by `rfl`.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper,
  intentionally `sorry` at the runtime target.

Source and artifact hashes:

```text
contracts/jug.sol sha256 cefc440545885a916920ce2dc251916f2fc218701ba32413d3ce4884fba07927
creation.hex      sha256 a48b536159ace9be419072a7ffeb640a3bf9b7f4086f965a269b9a8aa90040d8
runtime.hex       sha256 f70e2265698a98c6cafafd0505e5ccd87c79d2765fe026af89021d9a0aafb4d1
Jug.abi.json      sha256 077cd611060e5231763d70f59b44de8384390a54398fa9e59b0e1fc61f167d4f
jug.sol.ast.json  sha256 9ef821916e6994153589a0de782fb1f00dc43e518d1f1bd4691ea353ef3b0ce2
```

Scaffold notes:

- Readiness: ready for proof as of 2026-07-03. Fresh solc output exactly matches the checked-in
  Lean creation/runtime byte arrays, and the solc storage layout matches `Spec.lean`.
- The named ABI surface includes public storage getters, auth, three overloaded `file` functions,
  `init`, and `drip`.
- Storage layout is transcribed from solc's `--storage-layout`: `wards` slot 0, `ilks` slot 1,
  `vat` slot 2, `vow` slot 3, and `base` slot 4.
- `VatLike.ilks(bytes32)` and `VatLike.fold(bytes32,address,int256)` are represented with a custom
  external ABI, including a two-word decode for `ilks`.
- The runtime has two `CALL` sites and two matching `EXTCODESIZE` guards. The spec models solc's
  guard on both high-level `VatLike` calls in `drip`.
- The assembly `_rpow` helper is modeled structurally as a Solm loop with the same checked multiply,
  rounding-add, division, and odd-exponent update shape. Reusable proof work should isolate `_rpow`,
  `_rmul`, `_diff`, and typed external-call return decoding lemmas.
- No known Solm syntax or semantics change is required to start proving this benchmark. The likely
  proof hotspot is the optimized assembly `_rpow` loop.
