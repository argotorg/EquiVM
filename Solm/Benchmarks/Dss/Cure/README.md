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
- `creation.hex`: optimized creation bytecode, 3971 bytes.
- `runtime.hex`: optimized deployed runtime bytecode, 3875 bytes.
- `Cure.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Trusted.lean`: selector Keccak facts plus proof-local names for the verified `JUMPDEST` sets.
- `Spec.lean`: Solm AST benchmark scaffold with storage layout and full public ABI surface.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec, checked by `rfl`.
- `Constructor.lean`: top-level constructor-equivalence theorem, intentionally `sorry`.
- `Correct.lean`: top-level runtime-equivalence theorem plus whole-contract wrapper,
  intentionally `sorry` at the runtime target.

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

- Readiness: ready for proof as of 2026-07-06. Fresh solc output is checked in, and the solc
  storage layout matches `Spec.lean`.
- The named ABI surface includes public storage getters, `tCount`, `list`, `tell`,
  auth-gated `rely`/`deny`, `file(bytes32,uint256)`, source-list management, `cage`, and `load`.
- Storage layout is transcribed from solc's `--storage-layout`: `wards` slot 0, `live` slot 1,
  dynamic `srcs` slot 2, `wait` slot 3, `when` slot 4, `pos` slot 5, `amt` slot 6, `loaded` slot 7,
  `lCount` slot 8, and `say` slot 9.
- The runtime has one `STATICCALL` site and one matching `EXTCODESIZE` guard for
  `SourceLike.cure()`. It has no `CALL`, `DELEGATECALL`, contract creation, or selfdestruct.
- `SourceLike.cure()` is represented with a custom external ABI and modeled as `perm := false`,
  matching the upstream `view` interface and runtime `STATICCALL`.
- `Trusted.lean` records the 20 opaque Keccak selector facts needed to connect Solm dispatch to the
  runtime dispatcher constants; the values match the selectors embedded in `runtime.hex`.
- Checked `_add`/`_sub` use the same revert conditions as Solidity 0.6 wrapped arithmetic plus the
  source `require`s. The `lCount++` in `load` is modeled as unchecked modulo-2^256 wrapping.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- No known Solm syntax or semantics change is required to start proving this benchmark. The likely
  proof hotspots are dispatcher routing, dynamic-array and mapping storage lemmas, checked
  arithmetic, and static-call return decoding.
