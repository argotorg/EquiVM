# MakerDAO/Sky DSS Cat Benchmark

This benchmark uses the unmodified upstream DSS `Cat` source from MakerDAO/Sky:

- Repository requested: `makerdao/dss`
- Canonical GitHub redirect: `sky-ecosystem/dss`
- Commit: `fa4f6630afb0624d04a003e920b0d71a00331d98`
- Commit date: `2022-05-18T14:07:24Z`
- Path: `src/cat.sol`
- Source URL:
  `https://raw.githubusercontent.com/sky-ecosystem/dss/fa4f6630afb0624d04a003e920b0d71a00331d98/src/cat.sol`
- Solidity pragma: see `contracts/cat.sol`

Artifacts were generated locally with optimizer enabled and metadata hash disabled:

```bash
/tmp/solc-0.6.12 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --ast-json --storage-layout \
  -o /tmp/equivm-dss-cat-build --overwrite \
  Benchmarks/Dss/Cat/contracts/cat.sol
```

Compiler:

```text
0.6.12+commit.27d51765.Darwin.appleclang
```

Generated artifacts and scaffold files:

- `contracts/cat.sol`: exact fetched upstream Solidity source.
- `cat.sol.ast.json`: Solidity AST JSON emitted by solc.
- `Cat.storage.json`: solc storage layout for this contract.
- `creation.hex`: optimized creation bytecode.
- `runtime.hex`: optimized deployed runtime bytecode/template.
- `Cat.abi.json`: ABI emitted by solc.
- `Bytecode.lean`: creation/runtime bytecode as Lean `ByteArray`s plus verified `JUMPDEST` sets.
- `Spec.lean`: Solm benchmark spec entrypoint.
- `SpecSyntax.lean`: Solm notation companion wired to the AST spec.
- `Constructor.lean`: top-level constructor-equivalence theorem target.
- `Correct.lean`: top-level runtime-equivalence theorem target plus whole-contract wrapper.

Source and artifact hashes:

```text
contracts/cat.sol        sha256 341b2a7414a81f1baf2a070a5201be30fd232bada290ad75b8b8c6cbf034898e
cat.sol.ast.json         sha256 a2a3d885badaa136ad060abd3538bfd469781b29083d1890111f740997d6cdf8
Cat.abi.json             sha256 2d291345728a3c38a434e2e28c2d31663f3d7d15ecf276ba62367af24d8cd18d
Cat.storage.json         sha256 9cde18f8a2f5a99224435199c5d78ba59acb1bb610e5bbacb91a89287ecad831
creation.hex             sha256 a496cf84be96e216342201aad12c9d290c4cc7a365f46319c1c68d8e620c94c8
runtime.hex              sha256 8702bb359876e13ae7d71e8c7a0b53633280aebc56c780d01476e776a4959865
```

Scaffold notes:

- This file was generated as part of the DSS coverage expansion pass on 2026-07-06.
- Events are intentionally omitted from the Solm specs, matching the existing event-bearing DSS
  benchmarks whose equivalence relation ignores logs/substate.
- Proof status is tracked by `catContractCorrect` in `Correct.lean`.
