# MakerDAO/Sky DSS Vat Benchmark

This benchmark uses the unmodified upstream DSS Vat source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/vat.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/vat.sol`
- Solidity pragma: `^0.6.12`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json -o /tmp/equivm-dss-vat-build --overwrite \
  Benchmarks/Dss/Vat/contracts/vat.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/vat.sol`: exact fetched upstream Solidity source.
- `vat.sol.ast.json`: Solidity AST JSON emitted by solc.
- `creation.hex`: optimized creation bytecode, 7021 bytes.
- `runtime.hex`: optimized deployed runtime bytecode, 6965 bytes.
- `Vat.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold with storage layout and full public ABI surface.
- `SpecSyntax.lean`: Solm notation presentation for representative fragments, checked by `rfl`.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper,
  intentionally `sorry` at the runtime target.

Source and artifact hashes:

```text
contracts/vat.sol sha256 9016fd94f0f1b014abf184edab86a3f5843042b17e3734407e0f0fabb920f49f
creation.hex      sha256 4723d252278404d2b86d3bce523410b82f1a1c4b04c0b985935c697beff0f3ae
runtime.hex       sha256 2dfffcc5166ff4ac0505970ba311900e051cbfa1745bfc4df187b71a68915a66
Vat.abi.json      sha256 fa7dd1bbd56879f9aaba0efa979db6cd27d588ff0e54d43be58a0c8510e2379e
vat.sol.ast.json  sha256 403328c674c3b6f3365d616e039a4ff048a546a7b273412d0440461169fe804e
```

Scaffold notes:

- Readiness: ready for proof as of 2026-07-03. Fresh solc output exactly matches the checked-in
  Lean creation/runtime byte arrays, and the solc storage layout matches `Spec.lean`.
- The named ABI surface includes public storage getters, auth, permission, administration,
  fungibility, CDP manipulation, confiscation, settlement, and rate updates.
- Storage layout is transcribed from solc's `--storage-layout`: `wards` slot 0, `can` slot 1,
  `ilks` slot 2, `urns` slot 3, `gem` slot 4, `dai` slot 5, `sin` slot 6, `debt` slot 7,
  `vice` slot 8, `Line` slot 9, and `live` slot 10.
- Runtime opcode audit: no `CALL`, `STATICCALL`, `DELEGATECALL`, `CALLCODE`, `CREATE`, `CREATE2`,
  `SELFDESTRUCT`, or `EXTCODESIZE` sites are present in the deployed runtime.
- Maker's checked `_add`, `_sub`, and `_mul` helpers are modeled explicitly for both unsigned and
  signed arguments. Reusable proof work should isolate these helper lemmas.
- The `either` and `both` helpers are ordinary internal Solidity functions, so arithmetic-heavy
  arguments are evaluated eagerly in the source. The scaffold binds those intermediate products
  before the relevant `require`s to avoid accidental short-circuiting.
- No known Solm syntax or semantics change is required to start proving this benchmark. The likely
  proof hotspot is showing that the source-level checked signed/unsigned helper model matches the
  optimized Solidity 0.6.12 bytecode paths.
